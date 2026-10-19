/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom

/-!
# Closed support and the transported exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
first paragraph of lem-pur-gysin-structure.proof.md; Stacks Tags 001P and 09BM
(blueprint: lem-pur-closed-support-exceptional-comparison).

The compactification is exactly (id_Z,i). The compact-support identification below
uses the identity extension-by-zero adjunction and the unit-normalized exact derived
comparison, so the relative Hom map has the same source as the support Hom map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Identity extension by zero, normalized by its adjunction with identity pullback.
Source: blueprint closed-support comparison, proof step 2
(blueprint: lem-pur-closed-support-exceptional-comparison). -/
def closedSupportIdentityExtension (A : Type (u + 1)) [CommRing A] [Finite A]
    (Z : Scheme.{u}) : openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 Z) ≅ 𝟭 _ :=
  (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (upperStarId (ModuleCat.{u + 1} A) Z).symm)

/-- Compact support at (id_Z,i) is the exact termwise closed direct image on D+.
The isomorphism is constructed from identity extension by zero and the canonical
right-derived/termwise comparison, not supplied as free comparison data.
Source: blueprint closed-support comparison, proof step 2; Stacks Tag 09BM
(blueprint: lem-pur-closed-support-exceptional-comparison). -/
def closedSupportCompactIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    DerivedCategory.Plus.ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (Compactification.ofIsProper i) ≅
      supportClosedDerivedPlus A i j hPair ⋙ DerivedCategory.Plus.ι :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hPair
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso (closedSupportIdentityExtension A Z) ≪≫
            Functor.mapDerivedCategoryIdIso _)
          (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ≪≫
        Functor.leftUnitor _ ≪≫
        (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlusCompatibility.symm

/-- The precise comparison property, in fixed-scalar coordinates. All local instances
are consequences of the given finite coefficient setting and finite-type hypotheses.
The intrinsic constructibility predicate is applied through the existing canonical
constant-scalar realization. The two adjunction data are the data supplied by the
recorded support and comparison-class theorems, quantified to avoid an arbitrary choice.
Under the bounded intrinsic constructibility of the support value, the statement's
sentence "both B₀ and B are bounded below of etale origin" is asserted, not assumed.
The inverse relative Hom bijection is precomposed with closedSupportCompactIso.inv.
Source: blueprint closed-support comparison, statement and proof steps 1--4
(blueprint: lem-pur-closed-support-exceptional-comparison). -/
def closedSupportExceptionalComparisonProperty
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X V : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of P.field.k)) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) : Prop :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian aZ
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let c := Compactification.ofIsProper i
  let F := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) c
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification P.Coefficient c
  let B := sfFiniteExceptionalAt P.Coefficient c
  let S := supportClosedDerivedPlus P.Coefficient i j hPair
  let R₀ := (finiteClosedUpperShriek P.Coefficient i j).rightDerivedFunctorPlus
  let q := closedSupportCompactIso P.Coefficient i j hPair
  ∀ (adj₀ : S ⊣ R₀)
    (adj : FixedComparisonClassAdjunction P.Coefficient i c
      F.rightAdjoint (Adjunction.ofIsLeftAdjoint F)
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) Z)
      _root_.DerivedCategory.TStructure.t.plus)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))),
    Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos Z
      ((finiteCoefficientIntrinsicRealization Z P.Ring).mapDerivedCategory.obj (R₀.obj K).obj) →
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) Z (R₀.obj K).obj ∧
    ∃ hB : DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) Z (B.obj K.obj),
      ∃ φ : (R₀.obj K).obj ≅ B.obj K.obj,
          (∀ (T : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)))
            (wT : Scheme.FixedEtaleOriginWitness Z P.Coefficient T)
            (f : T.obj ⟶ (R₀.obj K).obj),
            q.inv.app T ≫ (adj.homEquiv c T.obj
              ⟨wT.complex.obj, wT.complex.property, ⟨wT.iso⟩⟩ K.obj K.property).symm
                (f ≫ φ.hom) =
              DerivedCategory.Plus.ι.map
                ((adj₀.homEquiv T K).symm (DerivedCategory.Plus.ι.preimage f))) ∧
          (∀ ψ : (R₀.obj K).obj ≅ B.obj K.obj,
            (∀ (T : DerivedCategory.Plus
                (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)))
              (wT : Scheme.FixedEtaleOriginWitness Z P.Coefficient T)
              (f : T.obj ⟶ (R₀.obj K).obj),
              q.inv.app T ≫ (adj.homEquiv c T.obj
                ⟨wT.complex.obj, wT.complex.property, ⟨wT.iso⟩⟩ K.obj K.property).symm
                  (f ≫ ψ.hom) =
                DerivedCategory.Plus.ι.map
                  ((adj₀.homEquiv T K).symm (DerivedCategory.Plus.ι.preimage f))) → ψ = φ) ∧
          DerivedCategory.Plus.ι.map (S.map (DerivedCategory.Plus.ι.preimage
              (X := R₀.obj K) (Y := ⟨B.obj K.obj, hB.plus⟩) φ.hom)) ≫
              (q.inv.app ⟨B.obj K.obj, hB.plus⟩ ≫
                (adj.homEquiv c (B.obj K.obj) hB K.obj K.property).symm (𝟙 _)) =
            DerivedCategory.Plus.ι.map (adj₀.counit.app K)

private theorem iso_of_restricted_homEquiv
    {C : Type*} [Category C] (P : ObjectProperty C) {X Y : C}
    (hX : P X) (hY : P Y)
    (e : ∀ (T : C), P T → ((T ⟶ X) ≃ (T ⟶ Y)))
    (he : ∀ (T T' : C) (hT : P T) (hT' : P T') (f : T ⟶ T') (g : T' ⟶ X),
      e T hT (f ≫ g) = f ≫ e T' hT' g) :
    ∃ φ : X ≅ Y, (∀ (T : C) (hT : P T) (f : T ⟶ X), f ≫ φ.hom = e T hT f) ∧
      ∀ ψ : X ≅ Y, (∀ (T : C) (hT : P T) (f : T ⟶ X),
        f ≫ ψ.hom = e T hT f) → ψ = φ := by
  let φ := e X hX (𝟙 X)
  let ψ := (e Y hY).symm (𝟙 Y)
  have hφ (T : C) (hT : P T) (f : T ⟶ X) : f ≫ φ = e T hT f := by
    simpa only [Category.comp_id] using (he T X hT hX f (𝟙 X)).symm
  have hψ (T : C) (hT : P T) (f : T ⟶ Y) : e T hT (f ≫ ψ) = f := by
    rw [he T Y hT hY f ψ]
    simp only [ψ, Equiv.apply_symm_apply, Category.comp_id]
  let z : X ≅ Y :=
    { hom := φ
      inv := ψ
      hom_inv_id := (e X hX).injective (by
        rw [hψ X hX φ])
      inv_hom_id := by
        rw [hφ Y hY ψ]
        exact (e Y hY).apply_symm_apply (𝟙 Y) }
  refine ⟨z, hφ, ?_⟩
  intro z' hz'
  apply Iso.ext
  simpa only [Category.id_comp] using (hz' X hX (𝟙 X)).trans (hφ X hX (𝟙 X)).symm

private theorem closedSupport_origin
    (P : WeilConjectures.PurityFiniteSetting.{u}) [Finite P.Ring] (Z : Scheme.{u})
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)))
    (hK : Scheme.intrinsicFiniteTorsionConstructible
      P.coefficients.l P.extension P.level P.level_pos Z
      ((finiteCoefficientIntrinsicRealization Z P.Ring).mapDerivedCategory.obj K.obj)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) Z K.obj := by
  classical
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let R := finiteCoefficientIntrinsicRealization Z P.Ring
  let C := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z
  let : R.Additive := finiteCoefficientIntrinsicRealization_additive Z P.Ring
  let : R.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact Z P.Ring).1
  obtain ⟨a, ha⟩ := hK.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.bddAbove
  have hv (i : ℤ) (hi : i < min a b ∨ max a b < i) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (R.mapDerivedCategory.obj K.obj)) := by
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hn)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hn)) (lt_of_le_of_lt (le_max_right _ _) hi)
  obtain ⟨L, ⟨eL⟩⟩ :=
    (Scheme.finiteRing_constructibleDerived_origin Z P.Ring).2.2.1
      (R.mapDerivedCategory.obj K.obj) |>.mpr ⟨hK.2, min a b, max a b, min_le_max, hv⟩
  have hL : _root_.DerivedCategory.TStructure.t.plus L.obj := by
    obtain ⟨c, d, _, hc⟩ := L.property.2
    exact ⟨c, (_root_.DerivedCategory.isGE_iff _ c).mpr
      (fun i hi ↦ hc i (Or.inl hi))⟩
  have e : R.mapDerivedCategory.obj (C.mapDerivedCategory.obj L.obj) ≅
      R.mapDerivedCategory.obj K.obj :=
    ((Functor.mapDerivedCategoryCompIso C R).app L.obj).symm ≪≫ eL
  exact ⟨L.obj, hL, ⟨R.mapDerivedCategory.preimageIso e⟩⟩

/-- Closed support and the finite exceptional inverse image have the unique
Hom-normalized, counit-compatible comparison in the ordinary pro-etale derived category.
No etale-origin hypothesis is imposed on K. Bounded intrinsic constructibility is
assumed only for the support value. The statement asserts that both representing
objects are bounded below of etale origin; these are conclusions, as the citer
lem-pur-gysin-structure uses them.
Source: blueprint main-20261015, first paragraph of lem-pur-gysin-structure.proof.md;
Stacks Tags 001P and 09BM (blueprint: lem-pur-closed-support-exceptional-comparison).

Proof:
1. The supplied support adjunction gives its natural Hom bijections. Convert the
finite support of intrinsic cohomology into an integer interval, and apply
lem-weil-pbc-finite-ring-constructible-derived-origin. Full faithfulness of the
canonical constant-scalar realization lifts its comparison isomorphism, proving
that B₀ has a bounded-below etale antecedent.
2. For c=(id_Z,i), specifiedExceptionalEtale_boundedBelow gives a bounded-below
etale antecedent for B. The canonical closedSupportCompactIso identifies compact
support with exact closed direct image. Compose this comparison, the two supplied
adjunction bijections, and the fully faithful D+ inclusions to obtain natural
bijections Hom(T,B₀) ≃ Hom(T,B) on bounded-below etale-origin objects.
3. Evaluate this natural bijection at id_B₀ and its inverse at id_B. Naturality
proves the two inverse equations and the required Hom normalization. Uniqueness
follows by evaluating any other normalized isomorphism at id_B₀, using a retained
etale antecedent of B₀.
4. Apply naturality of the exceptional Hom bijection and of closedSupportCompactIso
to the comparison morphism, and evaluate the normalization at id_B₀. The support
adjunction sends id_B₀ to its counit, giving the stated counit equation. -/
theorem closedSupportExceptionalComparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) {Z X V : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of P.field.k)) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (i : Z ⟶ X) [IsClosedImmersion i] (_hi : i ≫ aX = aZ)
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    closedSupportExceptionalComparisonProperty P aZ aX i j hPair := by
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace aZ
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian aZ
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  intro adj₀ adj K hK
  have h₀ := closedSupport_origin P Z
    ((finiteClosedUpperShriek P.Coefficient i j).rightDerivedFunctorPlus.obj K) hK
  refine ⟨h₀, ?_⟩
  let c := Compactification.ofIsProper i
  let := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification P.Coefficient c
  have hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) Z ((sfFiniteExceptionalAt P.Coefficient c).obj K.obj) :=
    DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
      (specifiedExceptionalEtale_boundedBelow P.Coefficient c K)
  let I := DerivedCategory.Plus.ι
    (C := Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient))
  let J := DerivedCategory.Plus.ι
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
  let ff := Functor.FullyFaithful.ofFullyFaithful I
  let fj := Functor.FullyFaithful.ofFullyFaithful J
  let B₀ := (finiteClosedUpperShriek P.Coefficient i j).rightDerivedFunctorPlus.obj K
  let B₁ : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)) :=
    ⟨(sfFiniteExceptionalAt P.Coefficient c).obj K.obj, hB.plus⟩
  let S := supportClosedDerivedPlus P.Coefficient i j hPair
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c
  let q := closedSupportCompactIso P.Coefficient i j hPair
  let O := fun T : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)) ↦
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) Z T.obj
  let e (T) (hT : O T) : (T ⟶ B₀) ≃ (T ⟶ B₁) :=
    (adj₀.homEquiv T K).symm.trans
      (fj.homEquiv.trans ((q.app T).homFromEquiv.symm.trans
        ((adj.homEquiv c T.obj hT K.obj K.property).trans
          (ff.homEquiv (X := T) (Y := B₁)).symm)))
  have he_map (T) (hT : O T) (f : T ⟶ B₀) :
      I.map (e T hT f) = (adj.homEquiv c T.obj hT K.obj K.property)
        (q.hom.app T ≫ J.map ((adj₀.homEquiv T K).symm f)) := by
    exact I.map_preimage _
  have he (T T') (hT : O T) (hT' : O T') (f : T ⟶ T') (g : T' ⟶ B₀) :
      e T hT (f ≫ g) = f ≫ e T' hT' g := by
    apply I.map_injective
    rw [I.map_comp, he_map, he_map]
    rw [adj₀.homEquiv_naturality_left_symm, J.map_comp, ← Category.assoc]
    have hq := q.hom.naturality f
    change F.map (I.map f) ≫ q.hom.app T' =
      q.hom.app T ≫ J.map (S.map f) at hq
    rw [← hq, Category.assoc]
    exact adj.naturality_left c T.obj T'.obj hT hT' K.obj K.property
      (I.map f) (q.hom.app T' ≫ J.map ((adj₀.homEquiv T' K).symm g))
  obtain ⟨φp, hφp, _hu⟩ := iso_of_restricted_homEquiv O h₀ hB e he
  let φ := I.mapIso φp
  have hφ (T) (hT : O T) (f : T.obj ⟶ B₀.obj) :
      q.inv.app T ≫ (adj.homEquiv c T.obj hT K.obj K.property).symm (f ≫ φ.hom) =
        J.map ((adj₀.homEquiv T K).symm (I.preimage f)) := by
    have hh := congrArg I.map (hφp T hT (I.preimage f))
    rw [I.map_comp, I.map_preimage, he_map] at hh
    change f ≫ φ.hom = _ at hh
    rw [hh, Equiv.symm_apply_apply, Iso.inv_hom_id_app_assoc]
  refine ⟨hB, φ, ?_, ?_, ?_⟩
  · intro T wT f
    exact hφ T ⟨wT.complex.obj, wT.complex.property, ⟨wT.iso⟩⟩ f
  · intro ψ hψ
    obtain ⟨L, hL, ⟨eL⟩⟩ := h₀
    have h₀ : O B₀ := ⟨L, hL, ⟨eL⟩⟩
    let w₀ : Scheme.FixedEtaleOriginWitness Z P.Coefficient B₀ := ⟨⟨L, hL⟩, eL⟩
    apply Iso.ext
    apply (adj.homEquiv c B₀.obj h₀ K.obj K.property).symm.injective
    apply (cancel_epi (q.inv.app B₀)).mp
    simpa only [Category.id_comp] using
      (hψ B₀ w₀ (𝟙 _)).trans (hφ B₀ h₀ (𝟙 _)).symm
  · have hn :
        (adj.homEquiv c B₀.obj h₀ K.obj K.property).symm φ.hom =
          F.map φ.hom ≫ (adj.homEquiv c B₁.obj hB K.obj K.property).symm (𝟙 _) := by
      apply (adj.homEquiv c B₀.obj h₀ K.obj K.property).injective
      rw [Equiv.apply_symm_apply,
        adj.naturality_left c B₀.obj B₁.obj h₀ hB K.obj K.property]
      simp only [Equiv.apply_symm_apply, Category.comp_id]
    have hq := q.inv.naturality (I.preimage (X := B₀) (Y := B₁) φ.hom)
    change J.map (S.map (I.preimage φ.hom)) ≫ q.inv.app B₁ =
      q.inv.app B₀ ≫ F.map (I.map (I.preimage φ.hom)) at hq
    rw [I.map_preimage] at hq
    change J.map (S.map (I.preimage φ.hom)) ≫
      (q.inv.app B₁ ≫ (adj.homEquiv c B₁.obj hB K.obj K.property).symm (𝟙 _)) = _
    rw [← Category.assoc, hq, Category.assoc, ← hn]
    have hid : I.preimage (X := B₀) (Y := B₀) (𝟙 B₀.obj) = 𝟙 B₀ :=
      Functor.preimage_id
    have hc := hφ B₀ h₀ (𝟙 _)
    rw [Category.id_comp, hid, adj₀.homEquiv_symm_id] at hc
    exact hc

end AlgebraicGeometry.ProEtale
