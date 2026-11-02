/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-! # Flatness of the internal supported diagonal coefficient

Source: closed/open localization and tensor detection; Stacks Tags 09AA and 09AH.
(blueprint: lem-sfb-diagonal-supported-flat).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem abZeroDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((upperStar Ab.{u + 1} i).obj F))
    (hj : IsZero ((upperStar Ab.{u + 1} j).obj F)) : IsZero F := by
  have := abelian_closed_support i j hU F hj
  exact ((lowerStar Ab.{u + 1} i).map_isZero hi).of_iso
    (asIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F))
private theorem modZeroDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
    (hi : IsZero ((ringSheafInverseImage i B).obj M))
    (hj : IsZero ((ringSheafInverseImage j B).obj M)) : IsZero M := by
  have h := abZeroDetect i j hU M.X ((Mod.forget _).map_isZero hi)
    ((Mod.forget _).map_isZero hj)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget _).map_injective
  exact h.eq_of_src _ _

private theorem modIsoDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B} (φ : M ⟶ N)
    [IsIso ((ringSheafInverseImage i B).map φ)]
    [IsIso ((ringSheafInverseImage j B).map φ)] : IsIso φ := by
  have hker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((ringSheafInverseImage f B).map φ)],
      IsZero ((ringSheafInverseImage f B).obj (kernel φ)) := fun f _ ↦
    (isZero_kernel_of_mono ((ringSheafInverseImage f B).map φ)).of_iso
      (PreservesKernel.iso _ φ)
  have hcoker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((ringSheafInverseImage f B).map φ)],
      IsZero ((ringSheafInverseImage f B).obj (cokernel φ)) := fun f _ ↦
    (isZero_cokernel_of_epi ((ringSheafInverseImage f B).map φ)).of_iso
      (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (modZeroDetect i j hU B _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (modZeroDetect i j hU B _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

private theorem flat_of_closed_open_restrictions
    {Z U X : Scheme.{u}}
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
    (hi : ObjectProperty.flat ((ringSheafInverseImage i B).obj F))
    (hj : ObjectProperty.flat ((ringSheafInverseImage j B).obj F)) :
    ObjectProperty.flat F := by
  let P := pairFunctor (ringSheafInverseImage i B) (ringSheafInverseImage j B)
  have hP : JointlyReflectIsomorphisms P :=
    jointlyReflectIsomorphisms_pairFunctor _ _ (fun {_ _} f hi hj ↦ by
      have := hi
      have := hj
      exact modIsoDetect i j hij B f)
  let (b : Bool) : Preadditive (cond b
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStar Ab.{u + 1} i).obj B)) (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        ((upperStar Ab.{u + 1} j).obj B))) :=
    Abelian.toPreadditive
  let T' : ∀ b : Bool, cond b
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStar Ab.{u + 1} i).obj B)) (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        ((upperStar Ab.{u + 1} j).obj B)) ⥤
      cond b (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStar Ab.{u + 1} i).obj B)) (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        ((upperStar Ab.{u + 1} j).obj B)) :=
    Bool.rec (motive := fun b ↦ cond b
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStar Ab.{u + 1} i).obj B)) (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        ((upperStar Ab.{u + 1} j).obj B)) ⥤
      cond b (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStar Ab.{u + 1} i).obj B)) (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        ((upperStar Ab.{u + 1} j).obj B)))
      (by
        change Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          ((upperStar Ab.{u + 1} j).obj B) ⥤ Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          ((upperStar Ab.{u + 1} j).obj B)
        exact tensorLeft ((ringSheafInverseImage j B).obj F))
      (by
        change Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          ((upperStar Ab.{u + 1} i).obj B) ⥤ Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          ((upperStar Ab.{u + 1} i).obj B)
        exact tensorLeft ((ringSheafInverseImage i B).obj F))
  let (b : Bool) : (T' b).Additive := by
    cases b
    · change (tensorLeft ((ringSheafInverseImage j B).obj F)).Additive
      infer_instance
    · change (tensorLeft ((ringSheafInverseImage i B).obj F)).Additive
      infer_instance
  have hT' (b : Bool) : exactFunctor _ _ (T' b) := by
    cases b
    · change exactFunctor _ _ (tensorLeft ((ringSheafInverseImage j B).obj F))
      exact hj.tensorLeft
    · change exactFunctor _ _ (tensorLeft ((ringSheafInverseImage i B).obj F))
      exact hi.tensorLeft
  apply (ObjectProperty.flat_iff_preservesFiniteLimits F).2
  exact (@JointlyReflectIsomorphisms.exactFunctor_of_iso
    _ _ _ _ _ _ Bool
    (fun b ↦ cond b (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStar Ab.{u + 1} i).obj B))
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        ((upperStar Ab.{u + 1} j).obj B)))
    (fun b ↦ inferInstance) (fun b ↦ inferInstance)
    (fun b ↦ cond b (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        ((upperStar Ab.{u + 1} i).obj B))
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        ((upperStar Ab.{u + 1} j).obj B)))
    (fun b ↦ inferInstance) (fun b ↦ inferInstance)
    P (fun b ↦ inferInstance) (fun b ↦ inferInstance)
    P (fun b ↦ inferInstance) (fun b ↦ inferInstance)
    hP (tensorLeft F) inferInstance T' (fun b ↦ by
      cases b
      · change (tensorLeft ((ringSheafInverseImage j B).obj F)).Additive
        infer_instance
      · change (tensorLeft ((ringSheafInverseImage i B).obj F)).Additive
        infer_instance)
    hT'
    (fun b ↦ by
      cases b
      · change tensorLeft F ⋙ ringSheafInverseImage j B ≅
          ringSheafInverseImage j B ⋙ tensorLeft ((ringSheafInverseImage j B).obj F)
        exact (Functor.Monoidal.commTensorLeft (ringSheafInverseImage j B) F).symm
      · change tensorLeft F ⋙ ringSheafInverseImage i B ≅
          ringSheafInverseImage i B ⋙ tensorLeft ((ringSheafInverseImage i B).obj F)
        exact (Functor.Monoidal.commTensorLeft (ringSheafInverseImage i B) F).symm)).1

/-- The regular module supported on the closed diagonal is flat, for arbitrary
commutative condensed coefficients.

Source: Stacks, proetale.tex, lemma-closed-immersion; the closed/open tensor
argument in the diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-sfb-diagonal-supported-flat).

Proof: Complementary exact module restrictions jointly reflect isomorphisms:
their underlying abelian restrictions detect zero kernels and cokernels. Tensoring
commutes with both restrictions. On a closed direct image the closed restriction
is the input, through the actual counit, and the open restriction is zero. Thus a
flat input gives two exact tensor functors. Joint reflection of exactness proves
flatness of the closed direct image. Apply this to the regular module after
restricting scalars through the canonical coefficient pullback isomorphism. This
restriction is the regular module for the pulled-back ring, hence flat. The
ordinary coefficient/direct-image comparison identifies its direct image with
the stated source. The Noetherian hypothesis ensures the open complement is
quasi-compact; no point or nonzero-ring hypothesis is needed. -/
theorem diagonal_supported_flat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    [IsNoetherian (diagonalSurface Y)] : ObjectProperty.flat (source Λ Y) := by
  let i := diagonalImmersion Y
  let B := condensedRingObj Λ (diagonalSurface Y)
  let M := (Mod.comap (condensedPullbackHom Λ i)).obj
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
  have hM : ObjectProperty.flat M := ObjectProperty.prop_of_iso ObjectProperty.flat
    (Mod.regularIsoComapRegular (condensedPullbackHom Λ i))
    (ObjectProperty.prop_unit ObjectProperty.flat)
  let j := i.openComplement.ι
  have hj : Set.range j.base = (Set.range i.base)ᶜ := by
    change Set.range i.openComplement.ι = (Set.range i)ᶜ
    classical
    ext x
    have hx := Set.ext_iff.mp i.range_eq_compl_range_openComplement_ι x
    change x ∈ Set.range i ↔ x ∉ Set.range i.openComplement.ι at hx
    change x ∈ Set.range i.openComplement.ι ↔ x ∉ Set.range i
    tauto
  have hc := ringSheaf_closed_localization i j hj B
  have : IsIso ((ringSheafAdjunction i B).counit.app M) := hc.2.1 M
  have hf : ObjectProperty.flat ((ringSheafDirectImage i B).obj M) := by
    apply flat_of_closed_open_restrictions B i j hj
    · exact ObjectProperty.prop_of_iso ObjectProperty.flat
        (asIso ((ringSheafAdjunction i B).counit.app M)).symm hM
    · exact ObjectProperty.flat_of_isZero (hc.2.2.1 M)
  exact ObjectProperty.prop_of_iso ObjectProperty.flat
    ((CondensedRing.comapPullbackHomCompIso Λ i).app
      (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))) hf

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
