## Worker report

The module `lean/Sheaf/CategoryTheory/ExactCoupleMorphism.lean` states
`CategoryTheory.BigradedExactCouple.coupleMorphism`. Its only proof is `sorry`.
No definitions are introduced, no existing declaration is replaced, and the node
copy changes only `lean`.

Source checked: the complete blueprint file named in the node's source was read
on the server with a read-only SSH `cat` (the literature files are absent from
this machine's clone). The blueprint's proof explicitly restricts the initial
E map to limiting cycles and passes to the boundary quotient; its abutment map
is the component of the original D map. The node already corrects the blueprint's
phrase “induces t_E” to the induced map on E-infinity. No further statement
correction is needed.

Hypotheses and clauses, individually matched:

- The same abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`;
  `X Y : BigradedExactCouple C 0` are the two initial exact couples. Universes
  `u v` and all variables are explicitly declared.
- Bidegree preservation is the type of `tD` and `tE`: their components have
  source and target at the same arbitrary integer pair `(p,q)`.
- Commutation with alpha is `hα`, with target bidegree `(p-1,q+1)`.
  Lean's `≫` reads left to right, so this is precisely t_D alpha = alpha' t_D.
- Commutation with f is `hf`, with target bidegree `(p+2,q-1)`.
- Commutation with g is `hg`. `initialG` is the recorded dependency's g map
  transported from `(p+0,q-0)` to `(p,q)`; no structure map is replaced.
- A map on every page is the existential family `t r p q`. The natural index
  `r` means actual page `r+2`, matching `pageCouple`; `t 0 p q = tE p q`
  identifies the initial map.
- Compatibility with differentials is the displayed equation using
  `(X.pageCouple r).d` and `(Y.pageCouple r).d`; the target indices are
  `(p+2+r,q-1-r)`, exactly the actual page-r+2 differential bidegree.
- These are morphisms of spectral sequences, not an unrelated collection of
  chain maps: the next conjunct gives a kernel map `k` commuting with the
  kernel inclusions and the equation
  `derivedEProjection ≫ t (r+1) = k ≫ derivedEProjection`.
  Thus the successor map is the map induced on page cohomology. This unfolds
  the morphism compatibility on the existing exact-couple page representation,
  without defining another spectral sequence or morphism notion.
- The conditional half-plane clause is under `∀ a b : ℤ` and four implications:
  D vanishes below a, E vanishes for p<0 or q<a, and the identical two
  hypotheses for Y with bound b. Separate bounds allow every pair of couples
  satisfying the convergence theorem, even when their lower bounds differ.
  No convergence premise is substituted for these hypotheses.
- `L M : LimitSubobjects` and `A B : ∀ n, AlphaColimit ... n` are the existing
  canonical limiting cycles/boundaries and diagonal colimits. `hA hB` identify
  each colimit object with `D 0 n`. The two zero-index cocone equations make
  these identifications canonical, exactly as in `halfPlaneConvergence`.
  These are existential outputs, not additional assumptions.
- Filtration preservation is `f n : FilteredObject.Hom` on the two existing
  `imageFiltration`s. Its `preserves` field means that the original map
  restricted to each filtration step factors through the target step.
- `(f n).hom = eqToHom (hA n) ≫ tD 0 n ≫ eqToHom (hB n).symm`
  says the underlying abutment map is precisely t_D^{0,n}. The following
  cocone equation states the same induced map on every diagonal component.
- The infinite-page map induced by t_E is `tInf`. The map `z` restricts t_E
  to the limiting cycle subobjects (the first square), and the next square
  says `tInf` is induced on their existing cokernels modulo limiting boundaries.
  Hence its specification also forces boundaries to be killed after passage
  to the target quotient.
- `gr p q` has the existing graded pieces as its source and target. The
  equation `toGradedPiece ≫ gr = tD ≫ toGradedPiece` characterizes the
  associated-graded map induced by the abutment map. The diagonal cocone maps
  factor through the filtration-step images; the image-factorization maps and
  quotient projections are epimorphic, so this equation uniquely specifies
  the restriction-and-quotient map, rather than an arbitrary graded map.
- `e e'` are the comparison isomorphisms. Each commutes with `toPageInfinity`
  and `toGradedPiece`, exactly the canonical identifications in the recorded
  half-plane convergence theorem. These too are existential outputs.
- `(e p q).hom ≫ gr p q = tInf p q ≫ (e' p q).hom` is the final asserted
  identification of the graded map with the induced infinite-page map.
  Integer pairs `(p,q)` cover every total degree n and filtration index p
  by q=n-p; no sign or degree restriction is imposed.

Dependency declarations read and used (including their full docstrings/signatures):

- `Sheaf.CategoryTheory.ExactCouple`: `CategoryTheory.BigradedExactCouple`,
  `BigradedExactCouple.pageCouple`, `.d`, and `.derivedEProjection`.
- `Sheaf.CategoryTheory.Filtration`: `CategoryTheory.DecreasingFiltration`,
  `.gradedPiece`, `CategoryTheory.FilteredObject`, and `FilteredObject.Hom`.
- `Sheaf.CategoryTheory.ExactCoupleConvergence`: `.LimitSubobjects`,
  `.limitBoundary_le_cycle`, `.pageInfinity`, `.initialG`, `.AlphaColimit`,
  `.imageFiltration`, `.toPageInfinity`, and `.toGradedPiece`, all in
  `CategoryTheory.BigradedExactCouple`.
- `Sheaf.CategoryTheory.HalfPlaneConvergence`: `.halfPlaneConvergence` was
  read to match the four vanishing hypotheses, the canonical D^{0,n}
  identifications, and the canonical comparison squares. This is the single
  umbrella import and supplies all the preceding definitions.
- Mathlib kernel, cokernel, subobject inclusions, isomorphisms and `eqToHom`
  are used directly. Mathlib's `SpectralSequence.Hom` signature and docstring
  were checked: it takes bundled homological-complex pages, whereas the
  recorded exact couple supplies kernel/cokernel pages. Its two conditions
  are rendered explicitly on those pages; no duplicate structure is defined.

Edge cases checked: initial actual page 2; every later page; zero morphisms;
zero couples; all negative integer indices; n=0; n below the lower support
bound (zero abutment); p<=0 (whole filtration step) and indices above the
support bound (zero step); distinct lower bounds for the couples. None is
excluded. No infinite limits, complete subobject lattice, elements of category
objects, or extra finiteness assumptions are required. Index universes do not
restrict the abelian category or its Hom universe.

Searches performed before writing (real queries logged in `searches.jsonl`):

- LeanFinder via msearch.py: “morphisms of exact couples induce morphisms of
  spectral sequences”: eight homology-sequence and snake-lemma hits, no
  exact-couple or abutment functoriality result.
- Loogle via msearch.py: `SpectralSequence.Hom`: no hits, unknown identifier
  at the service. The declaration was nevertheless read from local Mathlib.
- Mathlib grep via msearch.py: `ExactCouple|SpectralSequence`, restricted to
  Algebra/Homology: hits for spectral sequence/object definitions and their
  maps; no exact-couple declaration or theorem matching this node.
- LeanSearch via msearch.py: “morphism of exact couples induces morphism of
  spectral sequences”: service unavailable (Internal Server Error), recorded
  as unavailable, with no claimed search verdict.
- Local rg on WeilConjectures and lean/Sheaf for exact-couple morphisms and
  `pageInfinity`: only existing spectral-sequence/infinity definitions and
  page-induction material; none states this lemma. Node-id search in
  WeilConjectures has no hit. Exact name searches for `coupleMorphism` and
  `ExactCoupleMorphism` in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json had no hits before writing.

The natural-language proof in the theorem docstring records all three DAG
proof steps and names their supporting nodes. No node fault or
STATEMENT-DISPUTED claim remains. The server single-file compile succeeded
with no errors or warnings. The delivery dry run is the final verification;
independent second reading and delivery are reserved for the next worker.

## Second reading by C1

I independently reread the node statement, its source blueprint place (lemma order 513),
and the Lean declaration `CategoryTheory.BigradedExactCouple.coupleMorphism`.
The objects and hypotheses match item by item: `X,Y : BigradedExactCouple C 0`; component
maps `tD,tE`; the three commutative squares `hα`, `hf`, and `hg` with the exact bidegrees;
and the half-plane hypotheses for X and Y with independent bounds `a,b`. No extra category,
Noetherian, finiteness, or universe assumptions occur.

The conclusion is rendered by one existential family `t` of maps between
`(pageCouple r).E` objects. Its first conjunct identifies page zero with `tE`; its second
has the differential target `(p+2+r,q-1-r)`, since `pageCouple r` has type parameter `r`;
its third gives the kernel lift and derived-E projection square, expressing the induced
successor page map. Under the four vanishing hypotheses, the Lean existential witnesses
`L,M,A,B,hA,hB,f,z,tInf,gr,e,e'` correspond respectively to limiting cycles/boundaries,
diagonal colimits and their canonical identifications, filtration map, limiting-cycle map,
infinite-page map, graded map, and comparison isomorphisms. The displayed equations are,
clause by clause, the cocone, filtration-preservation, quotient, page-infinity, graded,
and final comparison assertions of the node.

Edge cases checked: zero maps and zero couples; empty/vanishing pages and filtration steps;
negative integer indices; `n=0`; indices below either lower support bound; and arbitrary
integer bidegrees. The explicit `C : Type u`, `Category.{v}`, and shared `Abelian` instance
cover the stated universes without restrictions.

Searches were rechecked with `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` for
`coupleMorphism` and `ExactCoupleMorphism`; no duplicate declaration exists. The local
Mathlib spectral-sequence hom declarations concern bundled homological-complex pages and
do not state this exact-couple result. No mismatch was found, so no Lean or node statement
was changed. The module compiles cleanly with `scompile.py`; its only proof remains the
named theorem's permitted `sorry`.
