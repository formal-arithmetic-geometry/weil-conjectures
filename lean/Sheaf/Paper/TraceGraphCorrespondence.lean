/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.TraceFixedScheme
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.IntrinsicRealizationOriginComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# Graph cohomological correspondences

Source: Weil conjectures blueprint main-20261015,
sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-trf-graph-correspondence.md
(blueprint: def-trf-graph-correspondence).

The fixed-scalar presentation and positive stage `A_{E,n+1}` are those of the recorded
correspondence definition. The identity exceptional comparison is the transpose of the
canonical compact-support identity comparison under the specified constructible adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
  (hl : l ≠ F.p) (X : Over (Spec (.of F.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  (K : (trfFiniteTorFixed l E n X.left).FullSubcategory)

set_option linter.unusedSectionVars false in
/-- The etale-origin witness needed to read the constructible identity adjunction.
Source: blueprint def-trf-graph-correspondence, `K ∈ Dᵇ_ctf`
(blueprint: def-trf-graph-correspondence).

Proof: finite-Tor constructibility includes bounded constructibility. The finite-coefficient
constructible-origin theorem identifies such a complex with the comparison pullback of a
bounded below etale complex. Transport through the canonical fixed-scalar realization gives
exactly the displayed origin property. This uses no condition on the endomorphism. -/
theorem trfGraphOrigin :
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      X.left K.obj := by
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let R := ProEtale.finiteCoefficientIntrinsicRealization X.left B
  let J := (sfIntrinsicDerivedEquivalence X.left B).functor.obj K.obj
  have hJ := K.property.1
  change Set.Finite {i : ℤ | ¬ IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj J)} ∧
    (∀ i, IsConstructibleProEtaleModuleSheaf X.left B
      ((_root_.DerivedCategory.homologyFunctor _ i).obj J)) at hJ
  obtain ⟨a, ha⟩ := hJ.1.bddBelow
  obtain ⟨b, hb⟩ := hJ.1.bddAbove
  have hbounded : _root_.DerivedCategory.TStructure.t.bounded J := by
    constructor
    · refine ⟨a, (_root_.DerivedCategory.isGE_iff J a).mpr ?_⟩
      intro i hi
      by_contra hn
      exact (not_le_of_gt hi) (ha hn)
    · refine ⟨b, (_root_.DerivedCategory.isLE_iff J b).mpr ?_⟩
      intro i hi
      by_contra hn
      exact (not_le_of_gt hi) (hb hn)
  have hKbounded : _root_.DerivedCategory.TStructure.t.bounded K.obj :=
    _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso
      ((sfIntrinsicDerivedEquivalence X.left B).unitIso.app K.obj).symm
      ((sfIntrinsicModuleEquivalence X.left B).inverse.bounded_mapDerivedCategory_obj hbounded)
  apply ProEtale.DerivedCategory.boundedConstructible.plusEtaleOrigin
  apply ProEtale.DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1, u} B) hKbounded
  intro i
  obtain ⟨e⟩ := ProEtale.intrinsicRealization_restriction X.left B
  let H := (_root_.DerivedCategory.homologyFunctor _ i).obj K.obj
  have eH : R.obj H ≅ (_root_.DerivedCategory.homologyFunctor _ i).obj J :=
    (R.mapDerivedCategoryHomologyFunctorIso i).app K.obj
  have hc := (proEtaleModuleRestriction_constructible_iff X.left B _).mp (hJ.2 i)
  exact ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    (ULift.{u + 1, u} B)
    (ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction X.left B).mapIso eH.symm ≪≫ e.app H) hc)

set_option linter.unusedSectionVars false in
/-- The ordinary etale identity exceptional functor preserves bounded below objects.
This supplies the identity case of the constructible adjunction without assuming an
ambient pro-etale adjoint. Source: blueprint def-trf-graph-correspondence, identity unit
(blueprint: def-trf-graph-correspondence).

Proof: the compact-support identity comparison on D+ comes from the trivial
compactification. For bounded below L, adjunction against bounded below test complexes
therefore identifies the etale right adjoint of R(id)_! with L. Bounded below tests detect
the lower cohomology bound by t-structure orthogonality. Thus this right adjoint preserves
bounded below objects; its existence is the finite-coefficient etale adjoint theorem. -/
theorem trfGraphIdentityBoundedBelow :
    Etale.HasBoundedBelowUpperShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      (𝟙 X.left) := by
  let := trfCorrespondenceCompactifiable F X X (𝟙 X)
  let : CompactSpace X.left :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ X.hom inferInstance inferInstance
  infer_instance

/-- The identity exceptional unit transported along `R(id)_! ≅ id`. We transpose the
canonical compact-support identity map using the published exceptional Hom equivalence,
which is the constructible adjunction, rather than choosing an arbitrary adjunction.
Source: blueprint def-trf-graph-correspondence, the definition of `ι_{X,K}`
(blueprint: def-trf-graph-correspondence). -/
def trfGraphIdentityMap : K.obj ⟶
    (trfCorrespondenceExceptional F l E n X X (𝟙 X)).obj K.obj := by
  letI := trfCorrespondenceCompactifiable F X X (𝟙 X)
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      (HasCompactification.compactification (𝟙 X.left))).IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriek (𝟙 X.left)
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
  letI := trfGraphIdentityBoundedBelow F l E n X
  exact ProEtale.rightDerivedUpperShriekHomEquiv (𝟙 X.left)
    (trfGraphOrigin F l E n X K) (trfGraphOrigin F l E n X K).plus
    (((ProEtale.originCompactSupportId
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X.left).hom.app
        ⟨K.obj, trfGraphOrigin F l E n X K⟩).hom)

/-- The transported identity unit is invertible.
Source: blueprint def-trf-graph-correspondence, `ι_{X,K} : K ≃ R(id)^! K`
(blueprint: def-trf-graph-correspondence).

Proof: the canonical compact-support identity isomorphism is obtained from the trivial
compactification `(id,id)` and compactification independence on etale-origin inputs.
Restrict the specified exceptional Hom bijection to the full constructible finite-Tor
category. Its transpose identifies the right adjoint of the identity with the identity.
The two triangle identities give inverse maps. The forward map is precisely the transpose
of the compact-support identity comparison, which defines `trfGraphIdentityMap`. -/
theorem isIso_trfGraphIdentityMap : IsIso (trfGraphIdentityMap F l E n X K) := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  let := trfCorrespondenceCompactifiable F X X (𝟙 X)
  let := trfGraphIdentityBoundedBelow F l E n X
  let P := ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X.left
  let L := ProEtale.originCompactSupport A (𝟙 X.left)
  let R := P.lift (P.ι ⋙ ProEtale.rightDerivedUpperShriek
    (ModuleCat.{u + 1} A) (𝟙 X.left))
    (fun M ↦ ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj (𝟙 X.left) M.property.plus)
  let adj : L ⊣ R := ProEtale.rightDerivedUpperShriekAdjunction (𝟙 X.left) P P
    (fun _ h ↦ h) (fun _ h ↦ h.plus)
    (fun _ h ↦ h.rightDerivedLowerShriek_obj (𝟙 X.left))
    (fun _ h ↦ ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj (𝟙 X.left) h.plus)
  let α := ProEtale.originCompactSupportId A X.left
  have : L.IsEquivalence := Functor.isEquivalence_of_iso α.symm
  let M : P.FullSubcategory := ⟨K.obj, trfGraphOrigin F l E n X K⟩
  have hunit : IsIso (adj.unit.app M) := inferInstance
  have hi : IsIso (adj.homEquiv M M (α.hom.app M)) := by
    rw [adj.homEquiv_unit]
    infer_instance
  have hm := (P.ι).map_isIso (adj.homEquiv M M (α.hom.app M))
  dsimp only [adj] at hm
  rw [ProEtale.rightDerivedUpperShriekAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at hm
  exact hm

/-- The canonical identity exceptional identification; only its invertibility proof is
postponed, and its forward map has already been constructed.
Source: blueprint def-trf-graph-correspondence, `ι_{X,K}`
(blueprint: def-trf-graph-correspondence). -/
def trfGraphIdentityIso : K.obj ≅
    (trfCorrespondenceExceptional F l E n X X (𝟙 X)).obj K.obj :=
  @asIso _ _ _ _ (trfGraphIdentityMap F l E n X K) (isIso_trfGraphIdentityMap F l E n X K)

/-- The graph of `(h,v)`: support `X`, exceptional leg `id`, ordinary leg `h`, and
coefficient `v ≫ ι`. Being an over-morphism says exactly that `h` is a `k`-endomorphism;
its separated finite-type properties follow from those of `X`.
Source: blueprint def-trf-graph-correspondence, displayed graph data
(blueprint: def-trf-graph-correspondence). -/
def trfGraphCorrespondence (h : X ⟶ X)
    (v : ((ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      h.left).leftDerivedFunctor).obj K.obj ⟶ K.obj) :
    TrfCohomologicalCorrespondence F l E n hl X K where
  C := X
  c₁ := 𝟙 X
  c₂ := h
  u := v ≫ (trfGraphIdentityIso F l E n X K).hom

/-- The fixed scheme of the cohomological graph is the geometric endomorphism fixed
scheme, whose first projection is the scheme-theoretic equalizer by
`trfEndomorphismFixedScheme_equalizer`. The equality retains the full structure sheaf.
Source: blueprint def-trf-graph-correspondence, final sentence
(blueprint: def-trf-graph-correspondence).

Proof: the two graph legs are `id` and `h`, hence its map to `X ×_s X` is the unique
fibre-product lift with these projections, namely `trfFixedGraphMap X h`. Both fixed
schemes are the pullback of this map along the same diagonal. The dependency's equalizer
universal property applies to every test scheme and includes the empty fixed scheme. -/
theorem trfGraphCorrespondence_fixedScheme (h : X ⟶ X)
    (v : ((ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      h.left).leftDerivedFunctor).obj K.obj ⟶ K.obj) :
    (trfGraphCorrespondence F l E n hl X K h v).fixedScheme =
      trfEndomorphismFixedScheme X h := by
  rfl

/-- Separation in the bundled over-scheme presentation of the recorded geometric fibre.
Source: blueprint def-trf-graph-correspondence, X in the conventions
(blueprint: def-trf-graph-correspondence). -/
instance TraceFormulaCoefficientConventions.graphBaseSeparated
    (T : TraceFormulaCoefficientConventions.{u}) : IsSeparated (Over.mk T.structureMap).hom :=
  T.geometricSeparated

/-- Finite type locally for the same bundled geometric fibre.
Source: blueprint def-trf-graph-correspondence, X in the conventions
(blueprint: def-trf-graph-correspondence). -/
instance TraceFormulaCoefficientConventions.graphBaseFiniteType
    (T : TraceFormulaCoefficientConventions.{u}) :
    LocallyOfFiniteType (Over.mk T.structureMap).hom :=
  T.geometricFiniteType

/-- Quasi-compactness for the same bundled geometric fibre.
Source: blueprint def-trf-graph-correspondence, X in the conventions
(blueprint: def-trf-graph-correspondence). -/
instance TraceFormulaCoefficientConventions.graphBaseQuasiCompact
    (T : TraceFormulaCoefficientConventions.{u}) : QuasiCompact (Over.mk T.structureMap).hom :=
  T.geometricQuasiCompact

/-- The graph correspondence in the precise global coefficient conventions: `X` is
`X₀ ×_{k₀} k`, the finite extension is the chosen subfield of the fixed algebraic closure,
and the coefficient exponent is `T.level`. The index `T.level - 1` represents this exponent
since `T.level_pos` gives `(T.level - 1) + 1 = T.level`. Objects and arrows are in the
canonical fixed-scalar presentation used by the recorded correspondence definition.
Source: blueprint def-trf-graph-correspondence, all hypotheses and graph display
(blueprint: def-trf-graph-correspondence). -/
def TraceFormulaCoefficientConventions.graphCorrespondence
    (T : TraceFormulaCoefficientConventions.{u}) :=
  trfGraphCorrespondence T.datum T.coefficients.l T.coefficientField (T.level - 1)
    T.coefficients.different (Over.mk T.structureMap)

end WeilConjectures
