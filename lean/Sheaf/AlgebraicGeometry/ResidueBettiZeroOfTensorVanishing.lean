/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # A residue Betti number vanishes under a universal tensor test

Source: Stacks Project, Tag 09U9, stalkwise Tor amplitude criterion.
(blueprint: lem-sc-residue-betti-zero-of-tensor-vanishing).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

private theorem skyscraperStalkEval_bijective (S : Scheme.{u}) (x : S)
    (I : Type u) [AddCommGroup I] [Module (S.presheaf.stalk x) I] :
    Function.Bijective (Modules.skyscraperStalkEval x I) := by
  constructor
  · intro m n h
    obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (Modules.skyscraper x I).presheaf m
    obtain ⟨V, hxV, n, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (Modules.skyscraper x I).presheaf n
    rw [Modules.skyscraperStalkEval_germ, Modules.skyscraperStalkEval_germ] at h
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← TopCat.Presheaf.germ_res_apply (Modules.skyscraper x I).presheaf
      (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx m,
      ← TopCat.Presheaf.germ_res_apply (Modules.skyscraper x I).presheaf
        (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx n]
    congr 1
    apply Modules.SkyscraperSections.ext
    intro hx
    exact h
  · intro m
    let t : Modules.SkyscraperSections x I (⊤ : S.Opens) := fun _ ↦ m
    exact ⟨(Modules.skyscraper x I).presheaf.germ ⊤ x trivial t,
      Modules.skyscraperStalkEval_germ x I (U := ⊤) trivial t⟩

private local instance stalk_additive (S : Scheme.{u}) (x : S) :
    (RingedSpace.moduleStalkFunctor S.toRingedSpace x).Additive where
  map_add := by
    intro M N f g
    ext m
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map (f + g).val) m = _
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map (f.val + g.val)) m = _
    rw [Functor.map_add, Functor.map_add]
    rfl

private local instance stalk_homology (S : Scheme.{u}) (x : S) :
    (RingedSpace.moduleStalkFunctor S.toRingedSpace x).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro C hC
  exact ((RingedSpace.module_stalk_exact S.toRingedSpace C.f).2.2.2.2
    C.X₃ C.f C.g C.zero).mp hC x

private noncomputable def residueTensorIso (R : Type u) [CommRing R] [IsLocalRing R] :
    (curriedTensor (ModuleCat.{u} R)).flip.obj
        (ModuleCat.of R (IsLocalRing.ResidueField R)) ≅
      ModuleCat.extendScalars (IsLocalRing.residue R) ⋙
        ModuleCat.restrictScalars (IsLocalRing.residue R) :=
  NatIso.ofComponents (fun M ↦
    (TensorProduct.comm R M (IsLocalRing.ResidueField R)).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext m k
      rfl)

/-- Universal tensor vanishing in a fixed degree implies residue-fibre vanishing.
Source: Stacks Project, Tag 09U9, proof of the stalkwise Tor amplitude criterion;
Tags 06YI and 06YJ for computing the derived residue pullback on K-flat models.
(blueprint: lem-sc-residue-betti-zero-of-tensor-vanishing).

Proof: Let F be the module skyscraper at x with value kappa(x), its scalar action
induced by the germ map O_S -> O_S,x -> kappa(x). Apply h to F and use its K-flat
representative P of E. The total tensor of P with F in degree zero is canonically
isomorphic to termwise tensor of P with F. Its degree-j cohomology is zero by h.
Take the stalk at x. Exact stalks preserve this cohomology, and the natural tensor
comparison identifies the stalk complex with P_x tensor kappa(x). The stalk of
F at x is kappa(x); the neighbourhoods of x in its skyscraper formula are cofinal.
The K-flat residue-pullback comparison identifies this module with
derivedFiberCohomology S E j x. It is therefore zero and has finrank zero.
No finiteness, perfectness, degree bound, or affine neighbourhood is needed.
In particular an infinite-dimensional fibre is allowed, and no point exists on
an empty scheme. -/
theorem derivedFiberBetti_eq_zero_of_tensor_vanishes
    (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S) (j : ℤ) (x : S)
    (h : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      schemeDerivedTensorCohomologyVanishes S E F j) :
    derivedFiberBetti S E j x = 0 := by
  classical
  let R : Type u := S.presheaf.stalk x
  let κ : Type u := IsLocalRing.ResidueField R
  let F : SheafOfModules.{u} (moduleRings S.toRingedSpace) := Modules.skyscraper x κ
  let := SheafOfModules.monoidalCategory S.sheaf
  let : MonoidalPreadditive (SheafOfModules.{u} (moduleRings S.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed S.sheaf).1
  obtain ⟨P, hP, ⟨eP⟩, hz⟩ := h F
  let T := RingedSpace.moduleStalkFunctor S.toRingedSpace x
  let L := (curriedTensor (SheafOfModules.{u} (moduleRings S.toRingedSpace))).flip.obj F
  let N := (HomologicalComplex.single _ (.up ℤ) 0).obj F
  let C := (L.mapHomologicalComplex (.up ℤ)).obj P
  let er : CochainComplex.mapBifunctor P N (curriedTensor _) ≅ C :=
    CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) F P
  have hzC : IsZero (C.homology j) := hz.of_iso
    ((HomologicalComplex.homologyFunctor _ (.up ℤ) j).mapIso er).symm
  have hzT : IsZero (T.obj (C.homology j)) := by
    rw [IsZero.iff_id_eq_zero, ← T.map_id, hzC.eq_of_src (𝟙 _) 0]
    exact T.map_zero _ _
  let eF : T.obj F ≅ ModuleCat.of R κ :=
    (LinearEquiv.ofBijective (Modules.skyscraperStalkEval x κ)
      (skyscraperStalkEval_bijective S x κ)).toModuleIso
  obtain ⟨φ, _, hφ⟩ := SheafOfModules.stalkTensorIso S.toRingedSpace x
  let A := (curriedTensor (ModuleCat.{u} R)).flip.obj (ModuleCat.of R κ)
  let η : L ⋙ T ≅ T ⋙ A :=
    NatIso.ofComponents (fun M ↦ φ M F ≪≫ tensorIso (Iso.refl _) eF) (by
      intro M N g
      dsimp [L, A, curriedTensor]
      simp only [tensorIso_hom, Iso.refl_hom, ← tensorHom_id]
      change T.map (g ⊗ₘ 𝟙 F) ≫ ((φ N F).hom ≫ (𝟙 _ ⊗ₘ eF.hom)) =
        ((φ M F).hom ≫ (𝟙 _ ⊗ₘ eF.hom)) ≫ (T.map g ⊗ₘ 𝟙 _)
      rw [← Category.assoc, hφ]
      rw [(RingedSpace.moduleStalkFunctor S.toRingedSpace x).map_id F]
      simp only [Category.assoc, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
      rfl)
  let θ := η ≪≫ Functor.isoWhiskerLeft T (residueTensorIso R)
  let D := ModuleCat.extendScalars (IsLocalRing.residue R)
  have : D.Additive := (ModuleCat.extendRestrictScalarsAdj
    (IsLocalRing.residue R)).left_adjoint_additive
  let B := ModuleCat.restrictScalars (IsLocalRing.residue R)
  let CP := (T.mapHomologicalComplex (.up ℤ)).obj P
  let DP := (D.mapHomologicalComplex (.up ℤ)).obj CP
  let cmp : (T.mapHomologicalComplex (.up ℤ)).obj C ≅
      (B.mapHomologicalComplex (.up ℤ)).obj DP :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ T)) (.up ℤ)).app P ≪≫
      (NatIso.mapHomologicalComplex θ (.up ℤ)).app P ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ (D ⋙ B))) (.up ℤ)).symm.app P ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (D ⋙ B)) (.up ℤ)).symm.app CP
  let eH : T.obj (C.homology j) ≅ B.obj (DP.homology j) :=
    ((C.sc j).mapHomologyIso T).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (.up ℤ) j).mapIso cmp ≪≫
      (DP.sc j).mapHomologyIso B
  have hzB : IsZero (B.obj (DP.homology j)) := hzT.of_iso eH.symm
  have hsB : Subsingleton (B.obj (DP.homology j)) := ModuleCat.isZero_iff_subsingleton.mp hzB
  have hs : Subsingleton (DP.homology j) := hsB
  obtain ⟨eκ⟩ := nonempty_kFlat_stalk_residueCohomology_linearEquiv S E x P hP eP j
  let : Subsingleton (derivedFiberCohomology S E j x) :=
    eκ.injective.subsingleton
  exact Module.finrank_zero_of_subsingleton

end AlgebraicGeometry.Scheme
