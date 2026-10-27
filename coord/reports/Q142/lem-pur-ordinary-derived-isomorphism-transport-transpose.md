## Worker report

The module Sheaf.Paper.OrdinaryDerivedIsomorphismTransportTranspose states the
ordinary unbounded transport lemma. The definition
WeilConjectures.PurityFiniteSetting.ordinaryDerivedIsomorphismTransport is the
three-factor arrow S_d written in the node, with real data. The single postponed
theorem is ordinaryDerivedIsomorphismTransport_transpose. Its proof is `sorry`;
its docstring carries all five steps of the current reviewed DAG proof.
No statement correction, new node, or dependency replacement is needed.

The previous attempt confused the stage-1 review with a stage-2 attachment. The
current node is split and reviewed PASS by Q72, but has no Lean record or
reviewed_lean record. There is no repair note for this item. This delivery adds
only its first Lean record, and preserves its reviewed statement and proof.

Hypothesis and clause correspondence:

- The finite field, coefficient extension, uniformizer quotient and positive level
  are the existing binder `P : PurityFiniteSetting.{u}`. `P.Coefficient` is the
  published size lift ULift of P.Ring = O_E/(varpi_E^n), not a new coefficient ring.
- B, X and X' are `Scheme.{u}` with their `.Over (Spec (.of P.field.k))`
  instances. Each structure map has `IsSeparated`, `LocallyOfFiniteType` and
  `QuasiCompact`, the precise separated finite-type assumptions. No properness,
  boundedness, constructibility, finite Tor amplitude or nonemptiness is assumed.
- The isomorphism is `s : X ≅ X'`, and the scheme morphism is `q : X' ⟶ B`.
  The map c is always the literal composite `s.hom ≫ q`; there is no arbitrary
  supplied composite or missing compatibility equality. The node says scheme
  morphisms, so no additional commutation with the structure maps is imposed.
- D(T) is the entire `DerivedCategory (Sheaf (Scheme.ProEt.topology T)
  (ModuleCat.{u + 1} P.Coefficient))`. This is the canonical fixed-scalar
  module-sheaf presentation already used by the recorded finite compositor.
  Objects of this category are ordinary sheaves of modules over the constant
  coefficient ring, equivalently the intrinsic constant-ring module sheaves.
  The small pro-etale site is unchanged (object universe u+1, Hom universe u).
- P_f is the existing `L(upperStar (ModuleCat.{u + 1} P.Coefficient) f)`,
  R_f is `R(lowerStar (ModuleCat.{u + 1} P.Coefficient) f)`. Exact inverse image
  identifies this K-flat-derived pullback canonically with termwise descent.
  The actual unit and counits are those of the published
  `derivedUpperStarLowerStarAdjunction`, not a supplied adjunction or equivalence.
- Alpha is precisely the existing `leftDerivedUpperStarComp ... s.hom q`,
  composite-to-iterated in direction. This is the published derived comparison
  of the canonical underived upperStarComp. Constant coefficients are built into
  these fixed-scalar functors. The recorded constant-ring composition theorem
  identifies their structural maps with the intrinsic ring-sheaf presentation;
  it is imported, together with the recorded general pullback composition.
- K' and K are arbitrary objects in those categories; d is the explicit
  isomorphism `L(upperStar ... s.hom).obj K' ≅ K`.
- S_d is defined exactly as `Rq.map (eta_s.app K') ≫ kappa.inv.app (Ps.obj K')
  ≫ Rc.map d.hom`. Kappa is the recorded `finiteDirectImageComposition
  P.Coefficient s.hom q`, including its K-injective normalization, not another
  mate or unspecified isomorphism. This explicit definition expresses the
  canonical site-isomorphism transport followed by d.
- Invertibility is the first conclusion `IsIso (ordinaryDerivedIsomorphismTransport
  P s q K' K d)`. It is an assertion about this specific arrow.
- The remaining conclusion quantifies over every `M : D(B)` and every
  `u : M ⟶ Rq.obj K'`. The left side is `Pc.map (u ≫ S_d) ≫ epsilon_c.app K`.
  The right side is `alpha.hom.app M ≫ Ps.map (Pq.map u ≫ epsilon_q.app K')
  ≫ d.hom`, exactly the displayed transpose equation with Lean's diagrammatic
  order. No equalities of isomorphism classes or per-degree weakenings occur.
- The canonical adjunction-compatible ringed normalization is not an extra
  hypothesis: the proof uses the existing ringed comparison theorem to identify
  this precise compositor and pullback comparison with the composite adjunction.
  Both sides explicitly use the canonical derived units and counits.

Dependency declarations read and used:

- Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting, Ring,
  Coefficient, coefficientCommRing, and the source-implied invertibility theorem.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations: the recorded
  proEtaleConstantRingDerivedPullback and its public finite-coefficient interface;
  the existing fixed-scalar operations are used in the compositor's presentation.
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition:
  AlgebraicGeometry.Scheme.proEtaleCoefficientInverseImageMap_comp.
- Sheaf.Paper.IntegralFinitePullbackComposition:
  WeilConjectures.integralTowerGeneralPullbackComposition and the publicly
  reexported canonical constant-ring pullback comparison. In fixed-scalar
  coordinates its existing counterpart is ProEtale.leftDerivedUpperStarComp.
- Sheaf.Paper.FiniteDirectImageComposition:
  AlgebraicGeometry.ProEtale.finiteDirectImageComposition, used verbatim.
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
  (publicly imported by the dependencies): leftDerivedUpperStarComp and
  derivedUpperStarLowerStarAdjunction; upperStar and lowerStar and their derived
  functors are the existing operations, with no new definition of any of them.
- Sheaf.SixFunctors.RingedDerivedMonoidalComparisons:
  CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons,
  whose reexported Composition includes the precise Hom/counit normalization.
- Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage:
  AlgebraicGeometry.Scheme.isoSectionwiseInverseImage_equivalence and its
  publicly reexported canonical site/constant-module equivalence interface.
- Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence:
  AlgebraicGeometry.Scheme.finiteTorsionDerivedPullback_isEquivalence_of_isIso,
  imported as a proof dependency.
- Mathlib.CategoryTheory.Adjunction.FullyFaithful: the equivalence-adjunction
  unit/counit isomorphism instances (the proof's Mathlib leaf).
- def-weil-scheme-morphism-properties is a convention node without a module;
  the properties are Mathlib's IsSeparated, LocallyOfFiniteType and QuasiCompact.

Edge cases checked before stating: s = identity and d = identity give the
normalized identity transport; q = identity leaves exactly the s-adjunction
triangle. Arbitrary d remains present in both sides. Zero objects and u = 0
are retained; empty schemes are allowed. Negative degrees and unbounded inputs
are retained by the ordinary DerivedCategory. Positive level n is supplied by
P.level_pos, including n = 1. No equality of site object and morphism universes
is introduced. Tensor symmetry and signs are not part of this extracted lemma.

Searches actually run:

- msearch.py leanfinder, query "Derived direct image transport through an
  isomorphism and its canonical adjunction transpose": eight hits including
  Functor.mapDerivedCategorySingleFunctor, Adjunction.derived,
  Functor.isRightDerivedFunctor_iff_of_iso, Functor.isLeftDerivedFunctor_iff_of_iso,
  Functor.mapDerivedCategoryFactorsh_hom_app,
  Functor.sheafPushforwardContinuousIso, rightDerivedNatIso and leftDerivedNatIso.
  None states this canonical three-factor isomorphism transport and its transpose.
- msearch.py loogle, query "CategoryTheory.Adjunction.comp_homEquiv": one exact
  hit, the abstract composite Hom bijection, only an ingredient.
- msearch.py grep, query "left_triangle_components|comp_homEquiv" in
  CategoryTheory/Adjunction: 24 hits in Basic, Triple, Mates, FullyFaithful,
  Opposites, Whiskering and other adjunction files; no specialized statement.
- rg over lean/WeilConjectures and lean/Sheaf for the node id and likely names
  ordinaryDerivedIsomorphismTransport/isomorphismTransportTranspose: no match.
  The separate required grep -rn of the node id in lean/WeilConjectures also
  found no match.
- Broader rg for transport/transpose found FiniteProperProductTranspose,
  FiniteSiteCounitProjectionTransport and PurNormalizedReconstructionAdjunctionCalculus.
  Their declarations were read: the first concerns the particular product-swap
  map and its product arrows, the second an etale/pro-etale compact-support
  comparison on bounded constructibles, and the third realization of arbitrary
  adjunctions under fixed equivalences. None states transport for arbitrary s,
  d and u with this finite direct-image compositor. The parent is not imported:
  this extracted lemma is one of its proof dependencies, so that would cycle.

Source checked: sites-cohomology.tex, lemma-derived-pushforward-composition
(Tag 0D6E) and its adjunction proof; the main-20261015 blueprint's
lem-sf-kunneth-coherence.proof.md proper symmetry paragraph.

Validation: the module compiled through the prescribed scompile.py server
wrapper in both sandbox and module identity, with no errors or warnings.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
