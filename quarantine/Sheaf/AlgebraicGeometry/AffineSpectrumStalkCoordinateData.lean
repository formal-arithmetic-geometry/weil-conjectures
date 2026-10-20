/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Stalk coordinates for affine spectrum replacement

Source: Stacks Project, Tags 0098 and 0096.
(blueprint: lem-pc-affine-spectrum-stalk-coordinate-data).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

private theorem nonempty_isoPullback_stalk_complex
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j] (y : Y)
    (P : CochainComplex Z.Modules ℤ) :
    Nonempty
      ((((RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).mapHomologicalComplex
        (.up ℤ)).obj P) ≅
      ((ModuleCat.restrictScalars (j.stalkMap y).hom).mapHomologicalComplex (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
          (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj P))) := by
  let ρ := (j.stalkMap y).hom
  let eρ := RingEquiv.ofBijective ρ
    (ConcreteCategory.bijective_of_isIso (j.stalkMap y))
  have : (ModuleCat.restrictScalars.{u} ρ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eρ
  let E := ModuleCat.extendScalars.{u} ρ
  let U := ModuleCat.restrictScalars.{u} ρ
  let S := RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)
  let T := Scheme.Modules.tensorPullback j ⋙ RingedSpace.moduleStalkFunctor Y.toRingedSpace y
  have : E.IsEquivalence :=
    (ModuleCat.extendRestrictScalarsAdj ρ).isEquivalence_left_of_isEquivalence_right
  let e := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso j y)
  let b : S ≅ T ⋙ U :=
    (Functor.rightUnitor S).symm ≪≫
      Functor.isoWhiskerLeft S (asIso (ModuleCat.extendRestrictScalarsAdj ρ).unit) ≪≫
      (Functor.associator S E U).symm ≪≫ Functor.isoWhiskerRight e.symm U
  have : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive.{u, w} j
  have : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
    comparisonStalkAdditive Y y
  have : T.Additive := by dsimp [T]; infer_instance
  have hT : T.PreservesZeroMorphisms := by
    dsimp [T]
    have hp : (Scheme.Modules.tensorPullback j).PreservesZeroMorphisms := inferInstance
    have hs : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).PreservesZeroMorphisms :=
      inferInstance
    infer_instance
  have hU : U.PreservesZeroMorphisms := by dsimp [U]; infer_instance
  have hTU : (T ⋙ U).PreservesZeroMorphisms := inferInstance
  let q := (NatIso.mapHomologicalComplex b (.up ℤ)).app P
  exact ⟨q ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ U)) (.up ℤ)).app P ≪≫
    ((U.mapHomologicalComplex (.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl T) (.up ℤ)).app P))⟩

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem stalkCongr_eqToHom (Y : Scheme.{u}) (y y' : Y) (h : y = y') :
    (Y.presheaf.stalkCongr (.of_eq h)).hom = eqToHom (congrArg Y.presheaf.stalk h) := by
  subst y'
  simp [TopCat.Presheaf.stalkCongr]

private noncomputable def spectrumStalkEquiv
    (Y : Scheme.{u}) [IsAffine Y] (y : Y) (y0 : Spec Γ(Y, ⊤))
    (h : y = Y.isoSpec.inv y0) : Y.presheaf.stalk y ≃+* (Spec Γ(Y, ⊤)).presheaf.stalk y0 :=
  ((eqToIso (congrArg Y.presheaf.stalk h)) ≪≫
    asIso (Y.isoSpec.inv.stalkMap y0)).commRingCatIsoToRingEquiv

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem spectrumStalkEquiv_naturality
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (x : X) (x0 : Spec Γ(X, ⊤)) (hx : x = X.isoSpec.inv x0)
    (hy : f x = Y.isoSpec.inv ((Spec.map f.appTop) x0)) :
    (spectrumStalkEquiv X x x0 hx).toRingHom.comp (f.stalkMap x).hom =
      ((Spec.map f.appTop).stalkMap x0).hom.comp
        (spectrumStalkEquiv Y (f x) ((Spec.map f.appTop) x0) hy).toRingHom := by
  subst x
  have h := Scheme.Hom.stalkMap_congr_hom
    (X.isoSpec.inv ≫ f) (Spec.map f.appTop ≫ Y.isoSpec.inv)
    (Scheme.isoSpec_inv_naturality f).symm x0
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
  change (f.stalkMap (X.isoSpec.inv x0) ≫ X.isoSpec.inv.stalkMap x0).hom =
    (eqToHom (congrArg Y.presheaf.stalk hy) ≫
      Y.isoSpec.inv.stalkMap ((Spec.map f.appTop) x0) ≫
      (Spec.map f.appTop).stalkMap x0).hom
  have hc := stalkCongr_eqToHom Y (f (X.isoSpec.inv x0))
    (Y.isoSpec.inv ((Spec.map f.appTop) x0)) hy
  rw [hc] at h
  exact congrArg CommRingCat.Hom.hom h

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem spectrumStalkEquiv_congr
    (Y : Scheme.{u}) [IsAffine Y] (y y' : Y) (y0 y0' : Spec Γ(Y, ⊤))
    (hy : y = Y.isoSpec.inv y0) (hy' : y' = Y.isoSpec.inv y0')
    (h : y = y') (h0 : y0 = y0') (r : Y.presheaf.stalk y) :
    spectrumStalkEquiv Y y' y0' hy' ((Y.presheaf.stalkCongr (.of_eq h)).hom r) =
      ((Spec Γ(Y, ⊤)).presheaf.stalkCongr (.of_eq h0)).hom
        (spectrumStalkEquiv Y y y0 hy r) := by
  cases h
  cases h0
  simp only [stalkCongr_eqToHom, eqToHom_refl, CommRingCat.id_apply]

private theorem nonempty_spectrumStalk_complex
    (X : Scheme.{u}) [IsAffine X] (x : X) (x0 : Spec Γ(X, ⊤))
    (hx : x = X.isoSpec.inv x0) (P : CochainComplex X.Modules ℤ) :
    Nonempty
      ((((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (.up ℤ)).obj P) ≅
      ((ModuleCat.restrictScalars
        (spectrumStalkEquiv X x x0 hx).toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor
          (Spec Γ(X, ⊤)).toRingedSpace x0).mapHomologicalComplex (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
            (.up ℤ)).obj P))) := by
  subst x
  simpa only [spectrumStalkEquiv, eqToIso_refl, Iso.refl_trans,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom, asIso_hom] using
    nonempty_isoPullback_stalk_complex.{u, w} X.isoSpec.inv x0 P

private theorem tensorMap_tmul
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    ∀ (a : A g' z) (b : B f' z),
      tensorMap f f' g g' sq z (a ⊗ₜ[R f g' z] b) =
        (g'.stalkMap z).hom a * (f'.stalkMap z).hom b := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  intro a b
  have hl := (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1
  have hr := (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).2
  have h (a : A g' z) (b : B f' z) :
      a ⊗ₜ[R f g' z] b =
        algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z) a *
          Algebra.TensorProduct.includeRight b := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, map_mul]
  exact congrArg₂ (· * ·) (RingHom.congr_fun hl a) (RingHom.congr_fun hr b)

-- The fixed statement names the existential complex isomorphism q but its compatibility
-- clauses concern only the ring equivalences. Keep that original binder unchanged.
set_option linter.unusedVariables false in
/-- Compatible ring and input-complex coordinates under affine spectrum replacement.

Proof: For each affine scheme Y, the inverse affine-spectrum isomorphism
induces an invertible stalk map. For D use this map at z0. For A use the
stalk map of X.isoSpec.inv at (Spec.map g'.appTop) z0, after identifying its
image with g'(X'.isoSpec.inv z0) by isoSpec_inv_naturality. For B use the
stalk map of S'.isoSpec.inv at (Spec.map f'.appTop) z0, and for R use the
stalk map of S.isoSpec.inv at the image under the two spectrum maps. Point
congruence isomorphisms identify their source stalks with the stated rings.
Naturality of stalkMap under composition proves compatibility with the R-to-A
and R-to-B homomorphisms, including the point congruence in rightAlgebra.
The two projection maps to D likewise commute with their spectrum versions.
The defining restrictions of tensorMap then give its displayed formula on
a tensor b: it is the product of the two projection images, and the ring
isomorphism preserves multiplication.
For q, use exists_tensorPullback_stalk_iso along X.isoSpec.inv. Its stalk ring
map rho is invertible, so restriction of scalars along rho is an equivalence.
The extension/restriction adjunction is consequently an equivalence and its
unit is invertible. Whisker this unit with the original stalk functor and
compose with the inverse pullback-stalk isomorphism after restricting scalars.
This gives a natural linear isomorphism from the original stalk functor to
pullback followed by the new stalk functor and restriction of scalars.
Map this natural isomorphism to cochain complexes and use the composition
isomorphisms for mapHomologicalComplex. Equality induction on hA transports
the original stalk point and identifies rho with the ring equivalence eA.
This construction needs no flatness, boundedness or nonzero-ring hypothesis;
the zero complex has the same maps, and an empty spectrum has no z0.
Source: Stacks Project, Tag 0098, lemma-stalk-pullback-modules; Tag 0096,
pullback adjunction; Mathlib isoSpec_inv_naturality and extendRestrictScalarsAdj.
(blueprint: lem-pc-affine-spectrum-stalk-coordinate-data). -/
theorem exists_affineSpectrum_stalk_coordinate_data
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) := by
  dsimp only
  let z := X'.isoSpec.inv z0
  let f0 := Spec.map f.appTop
  let f0' := Spec.map f'.appTop
  let g0 := Spec.map g.appTop
  let g0' := Spec.map g'.appTop
  have hA : g' z = X.isoSpec.inv (g0' z0) :=
    (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X => k z0)
      (Scheme.isoSpec_inv_naturality g')).symm
  have hB : f' z = S'.isoSpec.inv (f0' z0) :=
    (congrArg (fun k : Spec Γ(X', ⊤) ⟶ S' => k z0)
      (Scheme.isoSpec_inv_naturality f')).symm
  have hR : f (g' z) = S.isoSpec.inv (f0 (g0' z0)) := by
    rw [hA]
    exact (congrArg (fun k : Spec Γ(X, ⊤) ⟶ S => k (g0' z0))
      (Scheme.isoSpec_inv_naturality f)).symm
  have hR' : g (f' z) = S.isoSpec.inv (g0 (f0' z0)) := by
    rw [hB]
    exact (congrArg (fun k : Spec Γ(S', ⊤) ⟶ S => k (f0' z0))
      (Scheme.isoSpec_inv_naturality g)).symm
  let eA := spectrumStalkEquiv X (g' z) (g0' z0) hA
  let eB := spectrumStalkEquiv S' (f' z) (f0' z0) hB
  let eR := spectrumStalkEquiv S (f (g' z)) (f0 (g0' z0)) hR
  let eD := spectrumStalkEquiv X' z z0 rfl
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := leftAlgebra f0 g0' z0
  let := rightAlgebra f0 f0' g0 g0' sq0 z0
  obtain ⟨q⟩ := nonempty_spectrumStalk_complex.{u, w} X (g' z) (g0' z0) hA P
  refine ⟨eR, eA, eB, eD, q, ?_, ?_, ?_⟩
  · intro r
    exact RingHom.congr_fun (spectrumStalkEquiv_naturality f (g' z) (g0' z0) hA hR) r
  · intro r
    have h : f (g' z) = g (f' z) :=
      congrArg (fun k : X' ⟶ S => k z) sq.w
    have h0 : f0 (g0' z0) = g0 (f0' z0) :=
      congrArg (fun k : Spec Γ(X', ⊤) ⟶ Spec Γ(S, ⊤) => k z0) sq0.w
    change eB ((g.stalkMap (f' z)).hom
      ((S.presheaf.stalkCongr (.of_eq h)).hom r)) =
      (g0.stalkMap (f0' z0)).hom
        (((Spec Γ(S, ⊤)).presheaf.stalkCongr (.of_eq h0)).hom (eR r))
    exact (RingHom.congr_fun
      (spectrumStalkEquiv_naturality g (f' z) (f0' z0) hB hR')
        ((S.presheaf.stalkCongr (.of_eq h)).hom r)).trans
      (congrArg (g0.stalkMap (f0' z0)).hom
        (spectrumStalkEquiv_congr S (f (g' z)) (g (f' z))
          (f0 (g0' z0)) (g0 (f0' z0)) hR hR' h h0 r))
  · intro a b
    change eD (tensorMap f f' g g' sq z (a ⊗ₜ[R f g' z] b)) =
      tensorMap f0 f0' g0 g0' sq0 z0
        (eA a ⊗ₜ[R f0 g0' z0] eB b)
    rw [tensorMap_tmul, map_mul, tensorMap_tmul]
    exact congrArg₂ (· * ·)
      (RingHom.congr_fun (spectrumStalkEquiv_naturality g' z z0 rfl hA) a)
      (RingHom.congr_fun (spectrumStalkEquiv_naturality f' z z0 rfl hB) b)

end AlgebraicGeometry.SingleComplexBaseChange
