/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFixedScheme
import WeilConjectures.AlgebraicGeometry.IntrinsicRealizationOriginComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# Graph cohomological correspondences

Source: latest Weil blueprint, sec-smooth-purity/sk-cor-sp-all-coefficients,
def-trf-graph-correspondence (blueprint: def-trf-graph-correspondence).

We use the recorded fixed-scalar presentation of the intrinsic finite-Tor category.
The coefficient index `n` denotes exponent `n + 1`. The identity exceptional map is
specified by transposing the canonical compact-support identity comparison, not by
choosing an unrelated identification with the identity functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The bounded finite-Tor input is bounded below of etale origin in the canonical
fixed-scalar coordinates. Source: graph correspondence, the input `K ∈ Dᵇ_ctf`
(blueprint: def-trf-graph-correspondence).

Proof: discard finite Tor amplitude. Intrinsic bounded constructibility bounds the
finite set of nonzero cohomology degrees above and below. The exact scalar equivalence
transports these bounds. Its homology comparison, intrinsicRealization_restriction,
and proEtaleModuleRestriction_constructible_iff identify its cohomology with
constructible fixed-module sheaves. Apply boundedConstructible_of_homology and then
boundedConstructible.plusEtaleOrigin. Zero objects and empty schemes are included. -/
theorem trfGraphOrigin (X : Scheme.{u})
    (K : (trfFiniteTorFixed l E n X).FullSubcategory) :
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      X K.obj := by
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let R := ProEtale.finiteCoefficientIntrinsicRealization X B
  let J := (sfIntrinsicDerivedEquivalence X B).functor.obj K.obj
  have hJ := K.property.1
  change Set.Finite {i : ℤ | ¬ IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj J)} ∧
    (∀ i, IsConstructibleProEtaleModuleSheaf X B
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
      ((sfIntrinsicDerivedEquivalence X B).unitIso.app K.obj).symm
      ((sfIntrinsicModuleEquivalence X B).inverse.bounded_mapDerivedCategory_obj hbounded)
  apply ProEtale.DerivedCategory.boundedConstructible.plusEtaleOrigin
  apply ProEtale.DerivedCategory.boundedConstructible_of_homology
    (ULift.{u + 1, u} B) hKbounded
  intro i
  obtain ⟨e⟩ := ProEtale.intrinsicRealization_restriction X B
  let H := (_root_.DerivedCategory.homologyFunctor _ i).obj K.obj
  have eH : R.obj H ≅ (_root_.DerivedCategory.homologyFunctor _ i).obj J :=
    (R.mapDerivedCategoryHomologyFunctorIso i).app K.obj
  have hc := (proEtaleModuleRestriction_constructible_iff X B _).mp (hJ.2 i)
  exact ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    (ULift.{u + 1, u} B)
    (ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction X B).mapIso eH.symm ≪≫ e.app H) hc)

variable (X : Over (Spec (.of F.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- Identify the published transported etale right adjoint with the precise exceptional
functor recorded for the identity correspondence leg. This is the canonical uniqueness
isomorphism of right adjoints, whiskered by the comparison functors.
Source: graph correspondence, the identity exceptional leg
(blueprint: def-trf-graph-correspondence). -/
def trfGraphExceptionalIso :
    ProEtale.rightDerivedUpperShriek
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (𝟙 X.left) ≅
      trfCorrespondenceExceptional F l E n X X (𝟙 X) := by
  letI := trfCorrespondenceCompactifiable F X X (𝟙 X)
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  letI : (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification (𝟙 X.left))).IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriek A (𝟙 X.left)
  exact Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    ((Etale.rightDerivedUpperShriekAdjunction A (𝟙 X.left)).rightAdjointUniq
      (Adjunction.ofIsLeftAdjoint _)) _)

/-- The canonical map `ι : K → R(id_X)^! K`: transpose the compact-support identity
comparison under the specified exceptional Hom equivalence, then use uniqueness of
etale right adjoints to read its codomain in the recorded correspondence interface.
Source: graph correspondence, the identification suppressed by `u = v`
(blueprint: def-trf-graph-correspondence). -/
def trfGraphIdentityMap (K : (trfFiniteTorFixed l E n X.left).FullSubcategory) :
    K.obj ⟶ (trfCorrespondenceExceptional F l E n X X (𝟙 X)).obj K.obj := by
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ProEtale.rightDerivedUpperShriekHomEquiv (𝟙 X.left)
      (trfGraphOrigin l E n X.left K) (trfGraphOrigin l E n X.left K).plus
      (((ProEtale.originCompactSupportId
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X.left).hom.app
          ⟨K.obj, trfGraphOrigin l E n X.left K⟩).hom ≫
    (trfGraphExceptionalIso F l E n X).hom.app K.obj

/-- The identity exceptional map is invertible on the stated finite-Tor category.
Source: graph correspondence, `ι_{X,K}` (blueprint: def-trf-graph-correspondence).

Proof: restrict the exceptional Hom equivalence to the bounded-below etale-origin
subcategory. The canonical originCompactSupportId identifies its left adjoint with
identity, so its adjunction unit is invertible. The transpose of the identity comparison
is the unit followed by the right functor applied to that comparison. Both factors are
invertible. The final right-adjoint uniqueness comparison is an isomorphism as well.
This proves invertibility of exactly the map defined above, including on zero inputs. -/
theorem isIso_trfGraphIdentityMap
    (K : (trfFiniteTorFixed l E n X.left).FullSubcategory) :
    IsIso (trfGraphIdentityMap F l E n X K) := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  let := trfCorrespondenceCompactifiable F X X (𝟙 X)
  let : CompactSpace X.left :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ X.hom inferInstance inferInstance
  let P := ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X.left
  let L := ProEtale.originCompactSupport A (𝟙 X.left)
  let R := P.lift (P.ι ⋙ ProEtale.rightDerivedUpperShriek A (𝟙 X.left))
    (fun M ↦ ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj (𝟙 X.left) M.property.plus)
  let adj : L ⊣ R := ProEtale.rightDerivedUpperShriekAdjunction (𝟙 X.left) P P
    (fun _ h ↦ h) (fun _ h ↦ h.plus)
    (fun _ h ↦ h.rightDerivedLowerShriek_obj (𝟙 X.left))
    (fun _ h ↦ ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj (𝟙 X.left) h.plus)
  let α := ProEtale.originCompactSupportId A X.left
  have hL : L.IsEquivalence := Functor.isEquivalence_of_iso α.symm
  let M : P.FullSubcategory := ⟨K.obj, trfGraphOrigin l E n X.left K⟩
  have hunit : IsIso (adj.unit.app M) := inferInstance
  have hi : IsIso (adj.homEquiv M M (α.hom.app M)) := by
    rw [adj.homEquiv_unit]
    infer_instance
  have hm := (P.ι).map_isIso (adj.homEquiv M M (α.hom.app M))
  dsimp only [adj] at hm
  rw [ProEtale.rightDerivedUpperShriekAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at hm
  change IsIso (ProEtale.rightDerivedUpperShriekHomEquiv (𝟙 X.left)
    (trfGraphOrigin l E n X.left K) (trfGraphOrigin l E n X.left K).plus
    ((α.hom.app M).hom)) at hm
  haveI := hm
  haveI : IsIso ((trfGraphExceptionalIso F l E n X).hom.app K.obj) := by
    infer_instance
  dsimp [trfGraphIdentityMap]
  infer_instance

/-- The canonical identity exceptional isomorphism used in the coefficient map.
Source: graph correspondence, `ι_{X,K}` (blueprint: def-trf-graph-correspondence). -/
def trfGraphIdentityIso (K : (trfFiniteTorFixed l E n X.left).FullSubcategory) :
    K.obj ≅ (trfCorrespondenceExceptional F l E n X X (𝟙 X)).obj K.obj :=
  @asIso _ _ _ _ (trfGraphIdentityMap F l E n X K)
    (isIso_trfGraphIdentityMap F l E n X K)

set_option synthInstance.maxHeartbeats 80000 in
-- Derived pullback requires the same search budget as TrfCohomologicalCorrespondence.
/-- The graph correspondence: support `X`, exceptional leg identity, ordinary leg `h`,
and coefficient `v ≫ ι`. A morphism in `Over (Spec k)` is precisely a `k`-endomorphism;
its separated finite-type properties follow from those of its source over the field.
Source: graph correspondence, displayed data (blueprint: def-trf-graph-correspondence). -/
def trfGraphCorrespondence (hl : l ≠ F.p)
    (K : (trfFiniteTorFixed l E n X.left).FullSubcategory) (h : X ⟶ X)
    (v : ((ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      h.left).leftDerivedFunctor).obj K.obj ⟶ K.obj) :
    TrfCohomologicalCorrespondence F l E n hl X K where
  C := X
  c₁ := 𝟙 X
  c₂ := h
  u := v ≫ trfGraphIdentityMap F l E n X K

set_option synthInstance.maxHeartbeats 80000 in
-- The derived-pullback binder repeats the correspondence dependency's instance search.
/-- The fixed scheme of the graph is the recorded scheme-theoretic equalizer, with
its full scheme structure. Source: graph correspondence, final sentence
(blueprint: def-trf-graph-correspondence).

Proof: the toProduct map is trfFixedGraphMap: both are the pullback lift of `(id,h)`.
Their commuting-square proofs agree by proof irrelevance. Both fixed schemes are
therefore the same chosen pullback along the diagonal. The coefficient `v` is unused;
the identity, empty fixed schemes, and nonreduced equalizers are all retained. -/
theorem trfGraphCorrespondence_fixedScheme (hl : l ≠ F.p)
    (K : (trfFiniteTorFixed l E n X.left).FullSubcategory) (h : X ⟶ X)
    (v : ((ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      h.left).leftDerivedFunctor).obj K.obj ⟶ K.obj) :
    (trfGraphCorrespondence F l E n X hl K h v).fixedScheme =
      trfEndomorphismFixedScheme X h := by
  rfl

/-- The geometric fibre in the coefficient conventions is separated over `k`.
Source: graph correspondence, the stipulated base scheme
(blueprint: def-trf-graph-correspondence). -/
instance TraceFormulaCoefficientConventions.graphBaseSeparated
    (T : TraceFormulaCoefficientConventions.{u}) :
    IsSeparated (Over.mk T.structureMap).hom :=
  T.geometricSeparated

/-- The geometric fibre in the coefficient conventions is locally of finite type.
Source: graph correspondence, the stipulated base scheme
(blueprint: def-trf-graph-correspondence). -/
instance TraceFormulaCoefficientConventions.graphBaseFiniteType
    (T : TraceFormulaCoefficientConventions.{u}) :
    LocallyOfFiniteType (Over.mk T.structureMap).hom :=
  T.geometricFiniteType

/-- The geometric fibre in the coefficient conventions is quasi-compact.
Source: graph correspondence, the stipulated base scheme
(blueprint: def-trf-graph-correspondence). -/
instance TraceFormulaCoefficientConventions.graphBaseQuasiCompact
    (T : TraceFormulaCoefficientConventions.{u}) :
    QuasiCompact (Over.mk T.structureMap).hom :=
  T.geometricQuasiCompact

/-- The graph correspondence with exactly the finite-field and coefficient conventions
of the source. The positive coefficient level is reindexed by `T.level - 1` in the
recorded correspondence interface; the input is in its canonical fixed-scalar coordinates.
Source: latest blueprint, graph correspondence, displayed data and fixed-scheme sentence
(blueprint: def-trf-graph-correspondence). -/
def TraceFormulaCoefficientConventions.graphCorrespondence
    (T : TraceFormulaCoefficientConventions.{u}) :=
  trfGraphCorrespondence T.datum T.coefficients.l T.coefficientField (T.level - 1)
    (Over.mk T.structureMap) T.coefficients.different

end WeilConjectures
