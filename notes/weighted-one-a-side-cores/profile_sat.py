"""Independent SAT check of the two three-by-three omission profiles."""
from itertools import combinations_with_replacement, product
from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Solver

from core_profile import profile


def realizable(target, defaults, signed, budget):
    types = [(shore,i) for shore, hidden in enumerate(defaults) for i in range(3) if i != hidden]
    pool = IDPool()
    with Solver(name='cadical195') as sat:
        def one_of(vs):
            sat.append_formula(CardEnc.equals(vs, bound=1, vpool=pool, encoding=1).clauses)

        options=[]
        for g in range(budget):
            reads = range(len(types)+g)
            gates = [(op,a,b) for a,b in combinations_with_replacement(reads,2)
                     for op in ('and','or')]
            if signed:
                gates.extend(('not',a,a) for a in reads)
            choices=[(gate, pool.id(('choice',g,gate))) for gate in gates]
            one_of([s for _,s in choices]); options.append(choices)
        for n,(i,j) in enumerate(product(range(3),repeat=2)):
            wires=[pool.id(('input',n,k)) for k in range(len(types))]
            for k,(shore,index) in enumerate(types):
                sat.add_clause([wires[k] if (i,j)[shore]==index else -wires[k]])
            for g,choices in enumerate(options):
                z=pool.id(('wire',n,g))
                for (op,a,b),s in choices:
                    x,y=wires[a],wires[b]
                    clauses=([[-x,-y,z],[x,-z],[y,-z]] if op=='and' else
                             [[x,y,-z],[-x,z],[-y,z]] if op=='or' else
                             [[x,z],[-x,-z]])
                    sat.append_formula([[-s,*clause] for clause in clauses])
                wires.append(z)
            sat.add_clause([wires[-1] if target>>n&1 else -wires[-1]])
        return sat.solve()


if __name__ == '__main__':
    for name, rows in [('overlapping',(0,3,5)), ('disjoint',(1,2,5))]:
        target=sum(mask<<(3*r) for r,mask in enumerate(rows))
        for signed in (False,True):
            for defaults,bound in profile(target,signed).items():
                assert realizable(target,defaults,signed,bound), (name,signed,defaults,bound)
                assert not realizable(target,defaults,signed,bound-1), (name,signed,defaults,bound)
                print(name,signed,*defaults,bound,flush=True)
