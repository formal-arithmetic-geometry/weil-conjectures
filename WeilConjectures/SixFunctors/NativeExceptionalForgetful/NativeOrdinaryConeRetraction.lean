/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData

/-! # Retraction half of the native ordinary cone criterion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/--
The rotated native cone gives a retraction of the underlying ordinary map.

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`,
final exceptional-adjunction sentence. Complete the cone of `q`, rotate it,
and apply the detection hypothesis to its first arrow. Realization and the
faithful section/closure equivalences identify the resulting zero map in the
ordinary category, where the distinguished triangle splits. This is the
retraction half only; the finite-stalk argument is recorded separately.
(blueprint: lem-sf-native-ordinary-cone-retraction).
-/
theorem native_ordinary_cone_retraction (R : Family l D) (T : Space D)
    (V : ForgetModel D l R T) (H M : W D l T) (q : H ⟶ M)
    (e : Nonempty (V.functor.obj H ≅ V.functor.obj M))
    (hq : ∀ (K : W D l T) (v : K ⟶ H),
      WeilComplex.forget.map (v ≫ q) = 0 → V.functor.map v = 0) :
    Nonempty (SplitMono (WeilComplex.forget.map q)) := by
  classical
  obtain ⟨_e⟩ := e
  let d := R.data (geometric D T)
  let := d.realization.commutative
  let := d.realization.sectionsAdditive
  let := d.realization.sectionsLimits
  let := d.realization.sectionsColimits
  let := d.realization.additive
  let S := sectionFunctor l (geometric D T).base.left d.realization
  let : S.IsEquivalence := d.presentation
  let : S.Additive := d.realization.sectionsAdditive
  let ecl := (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingEquiv
  let : IsIso (CommRingCat.ofHom ecl.toRingHom) := ecl.toCommRingCatIso.isIso_hom
  have : IsIso (closureMap D T) := by
    dsimp only [closureMap]
    infer_instance
  let P := ProEtale.adicLowerStar l (closureMap D T)
  let F := P.mapDerivedCategory ⋙ S.mapDerivedCategory
  have : F.Faithful := by dsimp [F]; infer_instance
  let c : U D l R T ≅ WeilComplex.forget ⋙ F :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft WeilComplex.forget P.rightDerivedFunctorIsoMapDerivedCategory) _
        ≪≫ Functor.associator _ _ _
  have hz (K : W D l T) (v : K ⟶ H) (hv : V.functor.map v = 0) :
      WeilComplex.forget.map v = 0 := by
    have hreal : (U D l R T).map v = 0 := by
      apply (cancel_epi (V.realization.hom.app K)).1
      rw [← V.realization.hom.naturality]
      change (rho D l R T).map (V.functor.map v) ≫ _ = _
      rw [hv]
      simp only [rho, ordinary, Functor.comp_map, Functor.map_zero, zero_comp, comp_zero]
    apply F.map_injective
    rw [Functor.map_zero]
    apply (cancel_epi (c.hom.app K)).1
    change c.hom.app K ≫ (WeilComplex.forget ⋙ F).map v = _
    rw [← c.hom.naturality]
    change (U D l R T).map v ≫ _ = _
    rw [hreal, zero_comp, comp_zero]
  let I := (WeilComplex.objectProperty D.k₀ l T.base.left).ι
  let J := (Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback D.k₀ l T.base.left)).mapDerivedCategory
  let : I.CommShift ℤ := by
    dsimp only [I]
    infer_instance
  let : J.CommShift ℤ := by
    dsimp only [J]
    infer_instance
  let : I.IsTriangulated := by
    dsimp only [I]
    infer_instance
  let : J.IsTriangulated := by
    dsimp only [J]
    infer_instance
  let G := WeilComplex.forget (k₀ := D.k₀) (l := l) (X := T.base.left)
  let : G.CommShift ℤ := by
    change (I ⋙ J).CommShift ℤ
    infer_instance
  let : G.IsTriangulated := by
    change (I ⋙ J).IsTriangulated
    infer_instance
  obtain ⟨K, v, w, htri⟩ := Pretriangulated.distinguished_cocone_triangle₁ q
  have hvq : v ≫ q = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ htri
  have hv : WeilComplex.forget.map v = 0 := hz K v (hq K v (by
    rw [hvq, Functor.map_zero]))
  have hmap := G.map_distinguished _ htri
  obtain ⟨r, hr⟩ := Pretriangulated.Triangle.yoneda_exact₂ _ hmap
    (𝟙 (G.obj H)) (by
      change G.map v ≫ 𝟙 _ = 0
      simpa only [Category.comp_id] using hv)
  exact ⟨⟨r, hr.symm⟩⟩

end WeilConjectures.NativeExceptionalForgetful
