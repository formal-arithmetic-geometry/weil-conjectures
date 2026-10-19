## Worker report

The module `Sheaf.CategoryTheory.CocartesianFullRestriction` states the target
`SSet.Enhanced.cocartesian_full_restriction` with proof `sorry`.  It defines the
strict relative diagram fiber `relativeFunctorFiber`, the canonical inclusion
`relativeFunctorInclusion` (with its commuting-square helper
`relativeFunctorInclusion_squares`), and the predicate `relativeDiagramInFull` used
by the theorem's relative-functor conclusion.  The module docstring and every
public declaration identify the relevant source calculation; the main docstrings cite
HTT Propositions 2.4.1.7 and 3.1.2.1 and the blueprint node `lem-coef-cocartesian-full-restriction`.

The theorem renders the node statement as follows.  `E` and `B` are simplicial
sets in universe `u`, with explicit `Quasicategory E` and `Quasicategory B`
instances; `p : E ⟶ B` and `hp : cocartesianFibrationOver p` are the stated
cocartesian fibration data.  `R : E.Subcomplex` is full through
`hfull : R = fullSubcomplex E (fun x ↦ x ∈ R.obj (op ⦋0⦌))`.  The repleteness
hypothesis is `hreplete`, which closes the vertex predicate under equivalence edges from a source in
`R` to their target (`δ 1` is source and `δ 0` is target).  The transport hypothesis is
`htransport`: for every source vertex `x`, target base vertex `b`, and base edge
`α`, with the two endpoint equalities and `x` in `R`, it supplies an edge `e` with
source `x`, target in `R`, image exactly `α`, and
`IsCocartesianEdge p (SSet.yonedaEquiv.symm e)`.

The first conclusion is `Quasicategory (R : SSet)`; the second is the restricted
cocartesian-fibration predicate `cocartesianFibrationOver (R.ι ≫ p)`.  The third
says, for every edge of `R`, that restricted cocartesianness is equivalent to
ambient cocartesianness after composing with `R.ι`, so preservation and reflection
are both present.  For every small `K : SSet.{u}` and `a : K ⟶ B`, the remaining
conjunction gives quasicategory instances for both strict fibers
`relativeFunctorFiber (R.ι ≫ p) a` and `relativeFunctorFiber p a`; the degreewise
image characterization is the displayed existential involving
`relativeFunctorInclusion` and `relativeDiagramInFull`; and the right-pinched
mapping-space map is degreewise bijective for every pair of retained objects `b,c`
and every simplex degree `n`.  The final clause quantifies over every
`L : SSet.{u}`, precomposition map `t : L ⟶ K`, simplex degree `n`, and unrestricted
`R`-diagram simplex `r`, and supplies the corresponding `r'` over `L` with the
specified equality.  Thus it includes naturality under precomposition and also
allows the empty indexing simplicial set.

Dependency declarations used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex`,
  `SSet.Enhanced.mappingSpaceMap`, and the simplicial-set, functor, and mapping
  conventions from `SSet.Enhanced.mappingSpace`.
* `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`:
  `SSet.Enhanced.cocartesianFibrationOver`.
* `Sheaf.CategoryTheory.InfinityCocartesianCompositionInitiality`:
  `SSet.Enhanced.cocartesian_composition_initiality` (including its stated
  cocartesian composition, degenerate-edge, and lift-initiality clauses).
* `Sheaf.CategoryTheory.InnerFibrationEquivalenceOuterHornLift`:
  `SSet.Enhanced.inner_fibration_equivalence_outer_horn_lift`.
* Mathlib leaf
  `SSet.innerAnodyneExtensions_pushoutObjObjι'` from
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`
  (the node records this exact match); no local declaration is duplicated for it.

Edge cases checked against the statement and definitions were: `K = ∅` (both
strict fibers and the relative comparison reduce to the one-point simplicial
set, and precomposition remains defined), degenerate base edges, identity
transport edges, an empty/full subcomplex, and the smallest horn dimensions
(`n = 2`, where every horn contains all vertices).  The full-subcomplex
characterization was checked degreewise: factoring a simplex through `R` is
exactly the condition that all its object vertices lie in `R`; this also checks
that right-pinched mapping simplices with fixed endpoints remain in `R`.

Searches made:

* `msearch.py NV lem-coef-cocartesian-full-restriction leansearch
  "cocartesian fibration restricted to a replete full subcategory closed under
  cocartesian transport, and relative functor fibers"`: 8 Mathlib hits, all
  ordinary-category fibered-category declarations; no matching simplicial
  cocartesian-restriction theorem.
* `msearch.py ... loogle
  "SSet.Enhanced.cocartesianFibrationOver, SSet.Enhanced.IsCocartesianEdge"`:
  0 hits (`unknown identifier` for the project declaration in the Mathlib-only
  search), so Mathlib supplies no existing declaration.
* `msearch.py ... grep "cocartesian|quasicategor" AlgebraicTopology`: 25 hits,
  all generic quasicategory/cocartesian background files; none states this
  restriction theorem.
* `grep -rl "lem-coef-cocartesian-full-restriction" dag/nodes` found only the
  target and its citing proof nodes, with no second node for this notion.
  `tools/blueprint_refs.py search lem-coef-cocartesian-full-restriction` found
  no blueprint node.  `rg` over the source repository found no upstream
  declaration; `rg` over `lean/Sheaf` found only this module.

No statement correction, dependency repair, new node, or
`STATEMENT-DISPUTED` issue is needed.

## Second reading by NV

Independent maintainer reading of the immutable delivery
`fc1a4b847e421d8bd630b8c55a39f2fde27ea186`, performed on 2026-10-17.
This section is the maintainer's reading, not a claim that another NV worker
reviewed the delivery. The former placeholder has been replaced.

I read the item node, its six proof steps, both statement-dependency nodes,
the delivered module and all five declarations, and the exact imported
interfaces. Sources opened were Lurie's Higher Topos Theory (online IAS PDF),
Definitions 2.0.0.3 and 2.4.2.1, Remark 2.4.1.4, Propositions 2.4.1.5,
2.4.1.7, 2.4.4.3 and 3.1.2.1, Remark 2.4.1.9, and Corollaries 2.3.2.4--5;
Kerodon 01KX and 01H0 were also opened. The full restriction and strict-fiber
calculation is agent-formulated, as the node says, rather than a verbatim
HTT proposition. WANTED: an archived copy of HTT in literature/.

Objects and hypotheses agree with the node. `E`, `B`, and all indexing
simplicial sets are in the fixed universe `u`. The two quasicategory
instances are explicit. `cocartesianFibrationOver` has the same inner-fibration
and specified-source lift conditions as the older quasicategory predicate,
without its instance parameters; no extra assumption is introduced.
`R : E.Subcomplex` is a genuine simplicial subset, and `hfull` identifies
it with the dependency's full subcomplex on exactly its retained vertices.
`hreplete` closes that set under equivalence edges from source to target;
inverse equivalences make this the symmetric repleteness condition.
`htransport` quantifies over every retained source and every base edge with
that exact source image, and supplies an ambient cocartesian lift with target
in `R` and image exactly the prescribed base edge. Its extra quantified `b`
is merely the named target of the edge, not a restriction.

The conclusion supplies the quasicategory structure of `R`, the restricted
cocartesian fibration, and both directions of the cocartesian-edge equivalence.
For every `K` and `a`, both relative fibers are quasicategories. The definition
of `relativeFunctorFiber` is the actual pullback of internal-hom postcomposition
against the constant point `diagramVertex a`, so it is the required strict
fiber, not a homotopy-fiber substitute. `relativeFunctorInclusion` is the
canonical pullback map; its only postponed inputs are the two uniquely typed
commuting-square equalities in the named helper theorem.

The fullness clause is encoded using factorization, rather than a second
vertex predicate: `relativeDiagramInFull` says the underlying diagram simplex
factors through `R`. Under `hfull`, this is exactly the condition that all
vertices of `K × Δ[n]`, hence every object value of every diagram vertex,
belong to `R`. Subcomplex inclusion is degreewise injective, as is its
internal-hom map; in the pullback the other coordinate is in `Δ[0]` and is
unique. Consequently the canonical relative inclusion is degreewise injective
and its stated image characterization describes the full subcategory.
This uses the actual dependency definition of `fullSubcomplex`, not an
unconstrained predicate or a hollow construction.

The mapping-space clause is a bijection on each degree of the canonical
`mappingSpaceMap` between retained endpoints. That dependency is the
right-pinched construction with the whole initial face constant and the last
vertex fixed; its simplicial operators append the last vertex. Thus the
bijections respect those operators and express the claimed identical mapping
simplices after the canonical inclusion, rather than merely a weak equivalence.

The final clause is expressed as a factorization of precomposition on the
underlying internal-hom simplices. Although its witness `r'` is existential,
it is unique: postcomposition with the subcomplex inclusion is injective.
Canonical precomposition of `r` is such a witness by internal-hom naturality,
so the clause identifies precisely canonical restriction, not an arbitrary
choice. If `r` lies over `a`, composing its equation with `p` shows that its
restriction lies over `t ≫ a`. The point coordinate in the strict fiber is
unique. These restrictions are simplicial, and restricting the initial face
and last vertex gives the same commutation on the stated pinched mapping
simplices. Thus no relative-fiber or mapping-space naturality case is lost.

The six proof steps match the dependencies: fullness retains inner-horn
fillers; it also retains initial outer-horn fillers and the supplied lifts;
initiality compares two lifts and the relative equivalence outer-horn theorem
makes the comparison ambient cocartesian; cocartesian composition then gives
reflection. The Mathlib pushout-product declaration makes postcomposition
an inner fibration for arbitrary `K`, and strict point pullback gives the
quasicategory fibers. The final two steps are the degreewise full-subcomplex
and pinched-simplex calculations. The imported composition/initiality and
relative outer-horn theorems have the needed quasicategory and inner-fibration
parameters. `proof_deps` equals the union of the proof-step `uses`.

No nonemptiness is assumed. Empty `K` gives point fibers, including when
`R` is empty. If `R` is empty and `K` has a vertex, its relative fiber is
empty, which remains a quasicategory. `R = E`, empty total/base simplicial
sets, point bases, degenerate base edges, degree zero, and the first horn
dimension two are covered. The common universe is the fixed simplicial-set
universe of the dependencies; there is no extra site-universe equality or
restricted test universe. No ring, scheme, characteristic, or pro-etale
assumption occurs in this item.

I independently searched Mathlib's algebraic-topology material, upstream
WeilConjectures, and the group clone's Sheaf modules for relative-fiber names,
full restriction, and cocartesian/full combinations. Ordinary-category
`Functor.IsCocartesian` uses Hom-set uniqueness and is not this statement;
base restriction and monoidal full-subcategory specializations are different
statements. The current clone has a later augmentation of this same owning
module; it was context only and was not substituted for the immutable file.
The delivered helpers reuse `fiber`, internal hom, and `pullback.map`, rather
than duplicating their notions. The worker's three search kinds are recorded
above. No new independent definition or missing DAG prerequisite is required.
No statement correction or citer audit is needed.

All five delivered declarations are listed in `lean.declarations`. The
`lean.statement` equals the theorem signature after joining source whitespace.
Every variable is bound with `autoImplicit false`, the largest line is 96
characters, source/blueprint docstrings are present, and the main docstring
follows all six proof steps. Both theorem bodies are whole `by sorry`;
there is no local proof beyond `sorry`, data-valued sorry, or arbitrary-map
construction. The imports match the statement and proof dependencies.

Independent compiler reproduction used the immutable file:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py NV lem-coef-cocartesian-full-restriction snapshot/lean/Sheaf/CategoryTheory/CocartesianFullRestriction.lean
```

Exit status 0, no diagnostics. The wrapper reported sandbox compilation in
6.0 s and library compilation in 2.2 s, using a private overlay at
`/dev/shm/nt-tmp/nt-local-compile-p2hr4omm/.lbuild`. This installed version of
`scompile.py` sends its overlay transaction to the server; its output reports
the sandbox and library checks. No direct ssh, lake build, global build, live
Lean write, clone edit, Git mutation, merge, claim, or delivery was performed.
The immutable worker report contained no actual compile log, so the concrete
successful reproduction is recorded here instead of attributing a compile
record to the worker.

Findings repaired in this complete replacement report: H11, the second-reading
placeholder; the corrupted HTT citation; the reversed prose explanation of
`hreplete`; the description of mapping endpoints as ambient rather than
retained; and the description of the final quantified simplex as relative
rather than unrestricted. Compiler evidence and the missing archival-source
notice have been supplied. No Lean or node correction is required.
