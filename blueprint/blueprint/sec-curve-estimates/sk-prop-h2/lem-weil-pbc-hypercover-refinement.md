+++
id = "lem-weil-pbc-hypercover-refinement"
kind = "lemma"
title = "Finite refinements and local lifting"
order = 947
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-finite-split-hypercover"]
+++
For a quasi-compact quasi-separated $X$, split etale hypercovers finite in
each degree [def-weil-pbc-finite-split-hypercover] exist. Their homotopy
category is cofiltered. A finite collection of local lifting requirements on
their terms in finitely many degrees can be satisfied after refinement,
provided each requirement is locally solvable for the etale topology.
Consequently an arbitrary etale hypercover can, through any specified finite
degree, be refined by one finite in each degree.

## Proof

Use the quasi-compact etale objects of the site in
[def-weil-pbc-etale-site]. Their fibre products and the finite limits
defining matching schemes are quasi-compact and quasi-separated. Any etale
covering of such an object admits a finite refinement by affine opens of its
members: etale maps have open images, and finitely many of those images cover
the target. Each selected affine is of finite presentation over the target.

Construct a split hypercover successively. In degree $n$, retain the finitely
many degeneracy summands already prescribed, choose a finite cover of
$M_n(U)$ as the new summand $N_n$, and use its projections for the face maps.
The matching equations give the simplicial identities. This is precisely the
split construction in [def-weil-pbc-finite-split-hypercover]. For a
refinement $V\to U$, the corresponding target for the new nondegenerate
summand is

$$
 M_n(V)\times_{M_n(U)} U_n.
$$

Its map to $M_n(V)$ is a cover, so the same construction works. If local
lifts have also been prescribed, intersect this cover with the finitely many
covering families on which the lifts exist. Before constructing degree $n$,
impose also the pullbacks of the requirements in higher specified degrees
along every degeneracy from degree $n$. There are only finitely many such
degeneracies up to the specified degree. Thus the already prescribed
degenerate summands have the required lifts as well. Epimorphisms of the
sheaves in [def-weil-pbc-etale-sheaves] are locally surjective, so lifting
finitely many sections through epimorphisms is one such requirement.
Continuing above the specified degree needs no new requirements. This also
constructs a refinement of an arbitrary hypercover: only finitely many affine
pieces of the covering of each matching scheme are selected at each step.

For two hypercovers, perform this construction with the product of their
matching covers; the result maps to both. For parallel maps $f,g:V\to U$,
construct a homotopy after refining $V$. In degree zero choose, locally, a
$1$-simplex of $U$ with endpoints $f(v),g(v)$. In subsequent degrees
triangulate $\Delta^n\times\Delta^1$ into its $n+1$ standard simplices.
Previously chosen faces prescribe compatible boundaries; the matching covers
of $U$ lift those boundaries after finite refinement. Induction supplies a
simplicial homotopy in every degree. On cochains the alternating sum of these
prism maps is a chain homotopy: internal faces cancel in pairs, leaving
$g^*-f^*$. This proves cofilteredness after identifying homotopic maps.
