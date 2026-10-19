## Worker report

The module `Sheaf.Algebra.Homology.PseudoCoherentTensorClosure` states the two
clauses of Stacks Tag 0DJE (more-algebra.tex, lemma-tensor-pseudo-coherent).
Its declarations are `DerivedCategory.isMPseudoCoherent_tensor` and
`DerivedCategory.isPseudoCoherent_tensor`. Both proofs are `sorry`. The original
node is unchanged except for its `lean` record. No definition or helper is added.

Clause-by-clause comparison:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A commutative ring R | `(R : Type u) [CommRing R]` |
| K,L in D(R) | `(K L : DerivedCategory (ModuleCat.{u} R))` with the explicit chosen-localization binder `[HasDerivedCategory.{w} (ModuleCat.{u} R)]` |
| Integers n,m and upper cohomology bounds a,b | `(n m a b : ℤ)` |
| K is n-pseudo-coherent | `hK : IsMPseudoCoherent n K` |
| H^i(K)=0 for i>a | `hKa : ∀ i : ℤ, a < i → IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj K)` |
| L is m-pseudo-coherent | `hL : IsMPseudoCoherent m L` |
| H^j(L)=0 for j>b | `hLb : ∀ j : ℤ, b < j → IsZero ((homologyFunctor (ModuleCat.{u} R) j).obj L)` |
| Derived tensor | `K ⊗ L`, with the upstream K-flat derived monoidal instance, not an arbitrary monoidal structure binder |
| t=max(m+a,n+b), tensor is t-pseudo-coherent | `IsMPseudoCoherent (max (m + a) (n + b)) (K ⊗ L)` |
| Two pseudo-coherent objects | In the second theorem, `hK : IsPseudoCoherent K` and `hL : IsPseudoCoherent L` |
| Their derived tensor is pseudo-coherent | `IsPseudoCoherent (K ⊗ L)` without the first theorem's finite-stage hypotheses |

The phrase describing the K-flat total-complex model specifies the meaning of
the derived tensor, rather than an extra conclusion about a chosen resolution.
The existing upstream tensor has exactly that meaning: the monoidal structure
in `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal` is the
left-derived tensor bifunctor on the homotopy localization. Its K-flat comparison
is supplied by `CategoryTheory.DerivedMonoidal.isIso_counit_app_app_of_kFlat_left`
in `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`. On complexes the
tensor is the signed direct-sum total of `CochainComplex.mapBifunctor`.
Thus no representative, map, or noncanonical tensor is assumed in the statements.
The later source inspection found this direct canonical interface, so the final
draft does not need explicit representative binders.

Statement dependencies read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q` from `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  cohomology is `DerivedCategory.homologyFunctor` from its `HomologySequence` module.
- `def-pc-ring-pseudo-coherent-complex`: `DerivedCategory.IsPseudoCoherent` from
  `Sheaf.RingTheory.RingPseudoCoherent`. Its definition uses a bounded-above
  finite-free complex and an isomorphism after Q, not a bounded or perfect model.
- `def-pc-ring-m-pseudo-coherent`: `DerivedCategory.IsMPseudoCoherent` from
  `Sheaf.RingTheory.MPseudoCoherent`. Its definition requires a bounded
  finite-free approximation, isomorphisms strictly above m, and an epimorphism at m.
- `def-pc-tensor-complex-sheaves`: `CochainComplex.mapBifunctor` from
  `Mathlib.Algebra.Homology.BifunctorShift`, with `MonoidalCategory.curriedTensor`,
  specialized to ordinary modules. This is the total tensor used by the upstream
  derived monoidal structure, with the Koszul sign on the second differential.
- `def-pc-module-kflat-complex`: `CategoryTheory.MorphismProperty.kFlat` from
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`, specialized to
  `HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)`. Its two preservation
  properties supply the K-flat derived construction used by the tensor notation.

The existing canonical structure is provided by
`ModuleCat.hasFunctorialFlatResolution` in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
and `DerivedCategory.hasDerivedMonoidalCategory` in
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.
Both modules are public imports. There is no extra flat-resolution assumption.

Proof dependency imports, retained as the stage-3 plan: `def-kun-truncations`
(`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`);
`lem-pc-kflat-bounded-flat-replacement`
(`CochainComplex.exists_functorial_boundedAbove_flat_replacement` in
`Sheaf.Algebra.Homology.BoundedFlatReplacement`);
`lem-pc-module-bounded-flat-kflat`
(`CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat` in
`Sheaf.Algebra.Homology.BoundedFlatKFlat`);
`lem-pc-derived-tensor-second-factor-functor`
(`DerivedCategory.exists_derivedTensor_second_factor_functor` in
`Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`);
`lem-sf-derived-homology-long-exact` (`DerivedCategory.HomologySequence.exact₁`,
`exact₂`, `exact₃` in `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`).
The other proof dependencies are also statement dependencies and are public imports.
The first theorem's docstring carries steps 1–6 of the node; the second carries step 7.

Edge cases checked before drafting: the zero ring is permitted by `[CommRing R]`;
zero factors give zero tensor and satisfy every relevant pseudo-coherence stage;
the cases n>a or m>b use the zero approximation as described in the node's proof;
equalities n=a and m=b retain the strict cohomology inequalities and the boundary
surjection. Integers may be negative. Complexes may be unbounded below and have
infinite Tor-dimension: for example Z/2 over Z/4 remains allowed. No Noetherian,
local, perfectness, bounded-below or finite Tor-dimension hypothesis was added.
Universe u is arbitrary for the ordinary module category, and w is independent
for the chosen derived localization. All universes and variables are explicitly bound.

Searches (prescribed `msearch.py`, group N8, this item):

- LeanFinder: `Derived tensor of bounded above n pseudo coherent and m pseudo coherent complexes is max(m+a,n+b) pseudo coherent`.
  Eight hits: good-tensor and derived t-structure definitions; no pseudo-coherence closure.
- Loogle: `"pseudo", "coherent"`. Zero hits.
- Mathlib grep: `PseudoCoherent|pseudo.?coherent`. Zero hits.
- LeanSearch: `Derived tensor product preserves pseudo coherent complexes over a commutative ring`.
  Eight hits about ordinary tensor flatness/finiteness and étale algebras; no derived closure theorem.
- `rg` in the full upstream `WeilConjectures` tree for pseudo-coherence found only
  a prose reference in `AlgebraicGeometry/Cohomology/DirectImage/FiniteFreeComplex.lean`.
  The exact node-id grep found no upstream declaration.
- `rg` in `lean/Sheaf` for tensor/pseudo-coherence names found the two existing
  local nonvanishing modules citing this node in their proof plans, plus existing
  pseudo-coherence definitions; no tensor-closure statement.
- The proposed full declaration names were searched in Mathlib, upstream,
  `dag/lean_names_upstream.json`, and `lean/Sheaf`; no collision was found.

No statement dispute or node fault was found. The prescribed `scompile.py`
compiled both its sandbox and final library views successfully (3.0 seconds each),
with no errors or warnings. Delivery preflight is run separately below.

## Second reading by N8

This is a second pass by the same worker; no separate agent was started, as the
dispatch brief forbids that. The maintainer performs the independent review.
I reopened the node, the source's two clauses, and the final module. The first
signature has exactly the two finite-stage hypotheses and the two strict upper
cohomology bounds, with `m+a` paired with `n+b` under max. The second signature
has only pseudo-coherence of each factor and concludes pseudo-coherence of their
canonical derived tensor. Both reuse the recorded dependency predicates. The
source's arbitrary-ring scope and unbounded-below cases survive. The chosen
derived localization binder records size, and no monoidal structure or resolution
was added as a hypothesis. No mismatch or statement correction was needed.
