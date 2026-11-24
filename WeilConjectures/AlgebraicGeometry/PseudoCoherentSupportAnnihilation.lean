/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherent
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.SupportedPerfectFactorization

/-! # Perfect annihilator for a map to a supported complex

## References

* [Stacks, Tag 0A9C]
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The structure sheaf is perfect. -/
theorem isPerfect_tensorUnit (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    Scheme.IsPerfect X (𝟙_ (schemeDerivedCategory X)) := by
  intro x
  let R := (moduleRings X.toRingedSpace).over (⊤ : X.Opens)
  let K := (CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj
    (SheafOfModules.unit R)
  refine ⟨⊤, trivial, K, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨0, 0, ?_⟩
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      let e : K.X 0 ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin 1)) :=
        (eqToIso (HomologicalComplex.single_obj_X_self _ _ _)) ≪≫
          (coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit R)).symm
      exact ⟨1, e.hom, e.inv, e.hom_inv_id⟩
    · have hz : IsZero (K.X n) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact ⟨0, 0, 0, by simpa using hz.eq_of_src (0 : K.X n ⟶ K.X n) (𝟙 _)⟩
  · let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) ⊤
    let eunit : 𝟙_ (schemeDerivedCategory X) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace)) :=
      (DerivedCategory.quotientCompQhIso _).app _
    exact ⟨F.mapDerivedCategory.mapIso eunit ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (SheafOfModules.unit R)⟩
private theorem module_restriction_zero
    (Y : Scheme.{u}) (V : Y.Opens)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hM : ∀ x : Y, x ∈ V →
      Subsingleton (↑(TopCat.Presheaf.stalk M.val.presheaf x))) :
    IsZero ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V).obj M) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext U z
  change z = 0
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj M)
  intro x hx
  change TopCat.Presheaf.germ M.val.presheaf _ x hx _ =
    TopCat.Presheaf.germ M.val.presheaf _ x hx _
  exact (hM x (leOfHom U.unop.hom hx)).elim _ _

/-- A map `α : P → Q` in D_QCoh(Y), from a perfect complex, or from a pseudo-coherent
complex into a bounded below one, with `Q` supported on `T = Y \ V`, is killed by the tensor
action of a perfect `I → 𝒪_Y[0]` that is an isomorphism over `V`. The tensor is the derived
tensor `schemeDerivedTensorMonoidal`, with unit
`𝒪_Y[0]`; support on `T` means every cohomology sheaf of `Q` has zero stalks at the points
of `V`. (Stacks, Tag 0A9C) -/
theorem exists_perfect_annihilator
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (V : Y.Opens) [CompactSpace (V : Set Y)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (P Q : schemeDerivedQCohCategory Y) (α : P ⟶ Q)
    (hcase : Scheme.IsPerfect Y P.obj ∨ Scheme.IsPseudoCoherent Y P.obj ∧
      ∃ n : ℤ, ∀ k : ℤ, k < n → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj))
    (hQ : ∀ (k : ℤ) (x : Y), x ∈ V →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj).val.presheaf x))) :
    ∃ (I : schemeDerivedCategory Y) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y)),
      Scheme.IsPerfect Y I ∧
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
        V).mapDerivedCategory.map i) ∧
      i ▷ P.obj ≫ (λ_ P.obj).hom ≫ α.hom = 0 := by
  let : Zero (schemeDerivedCategory Y) := HasZeroObject.zero' _
  let : Zero (DerivedCategory (SheafOfModules.{u}
    ((moduleRings Y.toRingedSpace).over V))) := HasZeroObject.zero' _
  let H := derivedInternalHom (Opens.grothendieckTopology Y.toRingedSpace)
    Y.toRingedSpace.sheaf
  let K := H.obj (Opposite.op P.obj, Q.obj)
  let F := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V
  have hcase' : (Scheme.IsPseudoCoherent Y P.obj ∧ ∃ n : ℤ, Q.obj.IsGE n) ∨
      Scheme.IsPerfect Y P.obj := by
    rcases hcase with hp | ⟨hp, n, hn⟩
    · exact Or.inr hp
    · exact Or.inl ⟨hp, n, (DerivedCategory.isGE_iff Q.obj n).mpr hn⟩
  obtain ⟨hpc, hp, hs⟩ := rhom_supported_quasiCoherent Y P.obj Q.obj Q.property
  have hK : schemeDerivedQCohProperty Y K := by
    rcases hcase' with ⟨hP, hn⟩ | hP
    · exact (hpc hP hn).1
    · exact hp hP
  have hKzero : IsZero (F.mapDerivedCategory.obj K) := by
    have hclosed : IsClosed ((V : Set Y)ᶜ) := V.isOpen.isClosed_compl
    have hopen : (⟨((V : Set Y)ᶜ)ᶜ, hclosed.isOpen_compl⟩ : Y.Opens) = V := by
      ext x
      simp
    have hQzero (n : ℤ) : IsZero
        ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
          ⟨((V : Set Y)ᶜ)ᶜ, hclosed.isOpen_compl⟩).obj
          ((DerivedCategory.homologyFunctor _ n).obj Q.obj)) :=
      by
        rw [hopen]
        exact module_restriction_zero Y V _ (hQ n)
    have hzero (n : ℤ) : IsZero (F.obj
        ((DerivedCategory.homologyFunctor _ n).obj K)) :=
      by
        have hh := hs (V : Set Y)ᶜ hclosed hcase' hQzero n
        rw [hopen] at hh
        exact hh
    have hhom (n : ℤ) : IsZero
        ((DerivedCategory.homologyFunctor _ n).obj (F.mapDerivedCategory.obj K)) :=
      (hzero n).of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm
    have hi : IsIso (0 : F.mapDerivedCategory.obj K ⟶ 0) :=
      (DerivedCategory.isIso_iff _ _).mpr (fun n ↦
        IsZero.isIso (hhom n) ((DerivedCategory.homologyFunctor _ n).map_isZero
          (isZero_zero _)) _)
    exact (isZero_zero _).of_iso (asIso (0 : F.mapDerivedCategory.obj K ⟶ 0))
  obtain ⟨e, _, _, he, _⟩ := scheme_derivedInternalHom_adjunction Y
  let a : 𝟙_ (schemeDerivedCategory Y) ⟶ K :=
    (e _ P.obj Q.obj).symm ((λ_ P.obj).hom ≫ α.hom)
  have hu : Scheme.IsPerfect Y (𝟙_ (schemeDerivedCategory Y)) := isPerfect_tensorUnit Y
  obtain ⟨R, b, c, hR, hRzero, hbc⟩ :=
    supported_perfect_factorization Y V _ K hu hK hKzero a
  obtain ⟨C, g, h, htri⟩ := Pretriangulated.distinguished_cocone_triangle b
  let T := (Pretriangulated.Triangle.mk b g h).invRotate
  have hT : T ∈ distTriang (schemeDerivedCategory Y) :=
    Pretriangulated.inv_rot_of_distTriang _ htri
  have hI : Scheme.IsPerfect Y T.obj₁ :=
    (Scheme.isPerfect_two_out_of_three Y T hT).2.1 hu hR
  have hiso : IsIso (F.mapDerivedCategory.map T.mor₁) := by
    exact ((F.mapDerivedCategory.mapTriangle.obj T).isZero₃_iff_isIso₁
      (F.mapDerivedCategory.map_distinguished T hT)).mp hRzero
  have hia : T.mor₁ ≫ a = 0 := by
    rw [← hbc, ← Category.assoc]
    change (T.mor₁ ≫ T.mor₂) ≫ c = 0
    rw [Pretriangulated.comp_distTriang_mor_zero₁₂ T hT, zero_comp]
  have hn (A B : schemeDerivedCategory Y) (i : A ⟶ B) (f : B ⟶ K) :
      e A P.obj Q.obj (i ≫ f) = i ▷ P.obj ≫ e B P.obj Q.obj f := by
    have hh := he B A P.obj P.obj Q.obj Q.obj i (𝟙 P.obj) (𝟙 Q.obj) f
    change e A P.obj Q.obj (i ≫ f ≫ H.map ((𝟙 P.obj).op, 𝟙 Q.obj)) =
      (i ⊗ₘ 𝟙 P.obj) ≫ e B P.obj Q.obj f ≫ 𝟙 Q.obj at hh
    have hid : H.map ((𝟙 P.obj).op, 𝟙 Q.obj) = 𝟙 K := H.map_id _
    simpa only [hid, Category.comp_id, tensorHom_id, Category.id_comp] using hh
  have hezero : e T.obj₁ P.obj Q.obj 0 = 0 := by
    -- Apply naturality to the inverse image of zero, so the right side composes with zero.
    have hh := hn T.obj₁ T.obj₁ (0 : T.obj₁ ⟶ T.obj₁) ((e T.obj₁ P.obj Q.obj).symm 0)
    simpa only [zero_comp, Equiv.apply_symm_apply, comp_zero] using hh
  refine ⟨T.obj₁, T.mor₁, hI, hiso, ?_⟩
  have hh := hn T.obj₁ (𝟙_ (schemeDerivedCategory Y)) T.mor₁ a
  rw [hia, hezero] at hh
  simpa only [a, Equiv.apply_symm_apply, Category.assoc] using hh.symm

end AlgebraicGeometry
