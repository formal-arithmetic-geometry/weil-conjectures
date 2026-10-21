## Worker report

The module `Sheaf.Paper.CondensedBoundedHomContinuity` states
`AlgebraicGeometry.ProEtale.isIso_boundedConstructible_condensed_hom_colimit`.
Its only theorem has proof `sorry`. It introduces no definition and changes no natural-language
statement. The source read was paragraph 2 of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/lem-sfb-constructible-cocone-hom-surj.proof.md`.
The theorem docstring carries all four steps of the node's finite-cohomology devissage proof.

Hypotheses and conclusions, in order:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The fixed algebraic closure is `PadicAlgCl ℓ`.
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)` is a finite intermediate extension of
  `Padic ℓ` in that closure, with its induced topology and norm, exactly as in the recorded
  `PadicSubfieldConstructible` interface; the base field itself is included.
- The scheme is `(X : Scheme.{u})`, with `[TopologicalSpace.NoetherianSpace X]`.
  There is no locally Noetherian scheme hypothesis.
- The coefficient is the existing `padicSubfieldRingObj X ℓ E`, definitionally
  `condensedRingObj (Profinite.continuousMapRingObj E) X`, namely `p_X^* C(-,E)`.
  Modules are `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})` over that ring.
  Localization is the existing ordinary unbounded `DerivedCategory.Q`.
- `(K : PadicSubfieldConstructible X ℓ E)` uses the recorded definition directly.
  It is the full subcategory `BoundedConstructible (padicSubfieldRingObj X ℓ E)`;
  `K.obj` is its ambient derived object. Its property is bounded cohomology and
  `IsConstructibleModuleObject` for every cohomology module, using local finite presentations
  on a finite stratification. No completeness or finite-constant-model restriction is added.
- `{I : Type (u + 1)} [SmallCategory I] [IsFiltered I]` is a small filtered category in the
  module/Hom universe. Filteredness includes nonemptiness and is not restricted to posets.
- `N : I ⥤ CochainComplex (Mod ... (padicSubfieldRingObj X ℓ E)) ℤ` is the specified
  diagram of complexes, without term or cohomology constructibility assumptions.
- `(c : Cocone N)` is the supplied cocone, not a replacement by a chosen cocone.
  `hc : ∀ r : ℤ, IsColimit ((HomologicalComplex.eval _ _ r).mapCocone c)` is precisely
  its termwise module-colimit universal property. Evaluation picks the term and term map.
  It can also be turned into a complex colimit by `HomologicalComplex.isColimitOfEval`;
  neither formulation asks that its localized cocone be a derived-category colimit.
- `hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r)` is one common
  termwise lower bound for all indices. The bound is neither object-dependent nor merely
  a cohomological bound; no upper bound is present.
- `(n : ℤ)` covers every requested shift, including negative shifts and zero.
- The conclusion is `IsIso (colimit.desc _ ((DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
  preadditiveCoyoneda.obj (op K.obj)).mapCocone c))`. Additive coyoneda takes values in
  abelian groups, so this is an isomorphism of exactly the displayed abelian groups.
  Its diagram has values `Hom(K.obj,(Q.obj (N.obj i))⟦n⟧)` and its target is
  `Hom(K.obj,(Q.obj c.pt)⟦n⟧)`. Functorial mapping of the cocone makes its i-th leg
  postcomposition with `(shiftFunctor _ n).map (DerivedCategory.Q.map (c.ι.app i))`.
  The defining factorization of `colimit.desc` therefore gives exactly the displayed rule
  on a representative `u_i`. This clause is built into the actual arrow, not added as an
  unrelated existence or bijection assertion.

Dependency declarations read and used:

- `def-weil-pbc-condensed-e-module-category`: public import
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`, which reexports the existing
  condensed-ring/module framework; its coefficient commutativity instance was read.
  `padicSubfieldRingObj` in upstream `ModuleObject.Colimit.Compatibility` is the exact
  continuous coefficient specialization. No coefficient object is redefined.
- `def-sfb-dcons-subfield`: `AlgebraicGeometry.ProEtale.PadicSubfieldConstructible`,
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`.
  Its full definition and the upstream `BoundedConstructible`, `boundedConstructible` and
  `mem_boundedConstructible_iff` signatures/docstrings were read.
- `def-weil-pbc-category-colimit`: Mathlib `Limits.Cocone`, `Limits.IsColimit`,
  `Limits.colimit.desc` and `CategoryTheory.IsFiltered`, using the recorded HasLimits module.
  The evaluation and degreewise colimit interface in HomologicalComplexLimits was read.
- All stated proof dependencies are imported: the formal closure theorem and comparison
  definitions in `Sheaf.Paper.ConstructibleHomContinuityDevissage`, the general bounded
  constructible interface reexported by
  `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`,
  `Sheaf.Paper.CondensedSheafExtContinuity`,
  `Sheaf.CategoryTheory.DerivedCategory.BoundedCohomologyConeWitness`, and Mathlib's
  triangulated category. These are ordinary imports when only the future proof needs them.

Edge cases checked before writing: `K=0` makes all Hom groups zero; `K=M[0]` recovers the
existing constructible-sheaf base case; arbitrary shifts include negative degrees; the
empty scheme has the zero module category. A one-object filtered category gives the
ordinary cocone identification. Empty indexing is already excluded by the definition of
filtered, as in the node. Complexes unbounded above and second arguments with
nonconstructible terms remain permitted. No stagewise bound is substituted for the common
bound. Arbitrary supplied termwise colimits and non-poset filtered categories are included.

Searches made for an existing declaration:

- `msearch.py ... leanfinder`: “Hom from a bounded constructible complex of condensed
  modules commutes with filtered colimits of uniformly bounded below complexes”. Eight hits
  included `Condensed.instAB5CondensedMod`, `instHasColimitsCondensedMod`,
  `CondensedMod.hom_naturality_apply` and light-condensed/solid constructions; none is this theorem.
- `msearch.py ... loogle 'DerivedCategory, "colimit"'`: zero hits.
- `msearch.py ... leansearch`: “Derived Hom from bounded constructible condensed complexes
  commutes with filtered colimits of uniformly bounded below complexes”. Eight hits concern
  complex filtered colimits, exactness, colimit/limit interchange and abelian-group colimits;
  `HomologicalComplex.isColimitOfEval` is useful for the cocone interpretation, but no hit
  states the constructible Hom continuity theorem.
- `msearch.py ... grep 'constructible|filtered.*colimit|colimit.*[Hh]om'
  Algebra/Homology/DerivedCategory`: only Ext/Basic.lean's `BinaryCofan.IsColimit.hom_ext`.
- `rg` over the read-only `lean/WeilConjectures` and `lean/Sheaf` trees for Hom-continuity,
  Hom-colimit and bounded-constructible patterns found the single-sheaf base case, the
  general closure interfaces and integral coefficient analogues, which were read; none
  states this bounded condensed theorem for an arbitrary supplied termwise colimit.
  Upstream's private `bounded_factors` is only a factorization result and adds monomorphism
  assumptions on the cocone legs, so cannot be an exact existing match.
- `grep -rn 'lem-sfb-condensed-bounded-hom-continuity' lean/WeilConjectures`: no matches.

No node faults, statement corrections, new nodes or dependency repairs were necessary.
The initial server compile passed for both sandbox and library forms in 5.7 s and 6.4 s.
Delivery preflight recompiles the final module after adding the explicit HasLimits import.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
