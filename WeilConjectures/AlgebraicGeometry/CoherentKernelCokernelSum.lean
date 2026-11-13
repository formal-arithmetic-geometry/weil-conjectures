/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeSubKernel
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeImageExtension
import WeilConjectures.AlgebraicGeometry.CoherentCokernelRelations
import WeilConjectures.AlgebraicGeometry.CoherentExtensionRelations

/-! # Closure properties of coherent modules

Source: Stacks Project, Modules, Tag 01BY, parts (3) and (4).
-/

@[expose] public section

universe u v w

open CategoryTheory
open CategoryTheory.Limits ZeroObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.RingedSpace

private theorem finiteType_of_iso
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ U, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (e : F ≅ G) (hF : F.IsFiniteType) :
    G.IsFiniteType := by
  obtain ⟨q, hq⟩ := hF.exists_localGeneratorsData
  have : q.IsFiniteType := hq
  let q' : G.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i :=
        (q.generators i).ofEpi (((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom) }
  refine ⟨⟨q', ?_⟩⟩
  constructor
  intro i
  exact ⟨(hq.isFiniteType i).finite⟩

private theorem finiteType_free
    {C : Type v} [Category.{w} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : Type u) [Finite I] : (SheafOfModules.free (R := R) I).IsFiniteType := by
  let q : (SheafOfModules.free (R := R) I).GeneratingSections :=
    { I := I
      s := (SheafOfModules.free I).freeHomEquiv (𝟙 _)
      epi := by simp only [Equiv.symm_apply_apply]; infer_instance }
  have : q.IsFiniteType := ⟨inferInstance⟩
  refine ⟨⟨q.localGeneratorsData, ?_⟩⟩
  constructor
  intro i
  dsimp [SheafOfModules.GeneratingSections.localGeneratorsData]
  infer_instance

private theorem coherent_iso (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (e : F ≅ G) (hF : IsCoherent X F) :
    IsCoherent X G := by
  refine ⟨finiteType_of_iso.{u, u, u} e hF.1, ?_⟩
  intro U n f
  exact finiteType_of_iso.{u, u, u} (kernelCompMono f (e.inv.over U)) (hF.2 U n _)

private theorem coherent_zero (X : RingedSpace.{u}) :
    IsCoherent X (0 : SheafOfModules.{u} (moduleRings X)) := by
  have hfree := finiteType_free (R := moduleRings X) (ULift.{u} (Fin 0))
  have : (SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin 0))).IsFiniteType := hfree
  refine ⟨(finiteType_image_extension X).1
    (0 : SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin 0)) ⟶ 0), ?_⟩
  intro U n f
  have hf : f = 0 := by
    have hz := (SheafOfModules.overFunctor (moduleRings X) U).map_isZero (isZero_zero _)
    exact hz.eq_of_tgt _ _
  rw [hf]
  exact finiteType_of_iso.{u, u, u} kernelZeroIsoSource.symm (finiteType_free (ULift.{u} (Fin n)))


/-- Coherent modules are closed under kernels, cokernels, two out of three in short exact
sequences, finite direct sums (including the zero module), and isomorphisms (Stacks, Tag 01BY). -/
theorem coherent_kernel_cokernel_sum (X : RingedSpace.{u}) :
    (∀ (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G),
      IsCoherent X F → IsCoherent X G →
        IsCoherent X (kernel f) ∧ IsCoherent X (cokernel f)) ∧
    (∀ (S : ShortComplex (SheafOfModules.{u} (moduleRings X))), S.ShortExact →
      (IsCoherent X S.X₁ → IsCoherent X S.X₂ → IsCoherent X S.X₃) ∧
      (IsCoherent X S.X₁ → IsCoherent X S.X₃ → IsCoherent X S.X₂) ∧
      (IsCoherent X S.X₂ → IsCoherent X S.X₃ → IsCoherent X S.X₁)) ∧
    (∀ (r : ℕ) (F : Fin r → SheafOfModules.{u} (moduleRings X)),
      (∀ i : Fin r, IsCoherent X (F i)) → IsCoherent X (⨁ F)) ∧
    IsCoherent X (0 : SheafOfModules.{u} (moduleRings X)) ∧
    (∀ (F G : SheafOfModules.{u} (moduleRings X)) (_e : F ≅ G),
      IsCoherent X F → IsCoherent X G) :=
by
  have hker : ∀ (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G),
      IsCoherent X F → IsCoherent X G → IsCoherent X (kernel f) := by
    intro F G f hF hG
    exact (coherent_finiteType_submodule_kernel X).1 _ F (kernel.ι f)
      ((coherent_finiteType_submodule_kernel X).2 F G f hF.1 hG) hF
  have hcoker : ∀ (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G),
      IsCoherent X F → IsCoherent X G → IsCoherent X (cokernel f) := by
    intro F G f hF hG
    have : G.IsFiniteType := hG.1
    exact ⟨(finiteType_image_extension X).1 (cokernel.π f),
      coherent_cokernel_relations X F G f hF.1 hG⟩
  have hext : ∀ (S : ShortComplex (SheafOfModules.{u} (moduleRings X))),
      S.ShortExact → IsCoherent X S.X₁ → IsCoherent X S.X₃ → IsCoherent X S.X₂ := by
    intro S hS h₁ h₃
    have : S.X₁.IsFiniteType := h₁.1
    have : S.X₃.IsFiniteType := h₃.1
    exact ⟨(finiteType_image_extension X).2.2 S hS,
      coherent_extension_relations X S hS h₁ h₃⟩
  refine ⟨fun F G f hF hG ↦ ⟨hker F G f hF hG, hcoker F G f hF hG⟩,
    ?_, ?_, coherent_zero X, fun F G e hF ↦ coherent_iso X e hF⟩
  · intro S hS
    refine ⟨?_, hext S hS, ?_⟩
    · intro h₁ h₂
      exact coherent_iso X
        (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.gIsCokernel)
        (hcoker S.X₁ S.X₂ S.f h₁ h₂)
    · intro h₂ h₃
      exact coherent_iso X
        (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hS.fIsKernel)
        (hker S.X₂ S.X₃ S.g h₂ h₃)
  · intro r
    induction r with
    | zero =>
      intro F hF
      have hz : IsZero (⨁ F) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      exact coherent_iso X hz.isoZero.symm (coherent_zero X)
    | succ r ih =>
      intro F hF
      let T : Fin r → SheafOfModules.{u} (moduleRings X) := fun i ↦ F i.succ
      let a : (⨁ T) ⟶ ⨁ F := biproduct.desc fun i ↦ biproduct.ι F i.succ
      let b : (⨁ F) ⟶ F 0 := biproduct.π F 0
      have hab : a ≫ b = 0 := by
        apply biproduct.hom_ext'
        intro i
        simp [a, b]
      have ha (i : Fin r) : a ≫ biproduct.π F i.succ = biproduct.π T i := by
        apply biproduct.hom_ext'
        intro j
        simp [a, T, biproduct.ι_π]
      let S : ShortComplex (SheafOfModules.{u} (moduleRings X)) :=
        ShortComplex.mk a b hab
      have hs : S.Splitting :=
        { r := biproduct.lift fun i ↦ biproduct.π F i.succ
          s := biproduct.ι F 0
          f_r := by
            change a ≫ (biproduct.lift fun i : Fin r ↦ biproduct.π F i.succ) = 𝟙 _
            apply biproduct.hom_ext
            intro i
            simpa only [Category.assoc, biproduct.lift_π, Category.id_comp] using ha i
          s_g := by dsimp [S, b]; simp
          id := by
            change (biproduct.lift fun i : Fin r ↦ biproduct.π F i.succ) ≫ a +
              b ≫ biproduct.ι F 0 = 𝟙 _
            apply biproduct.hom_ext
            intro i
            simp only [Preadditive.add_comp, Category.assoc, Category.id_comp]
            cases i using Fin.cases with
            | zero =>
              change (biproduct.lift fun i : Fin r ↦ biproduct.π F i.succ) ≫ a ≫ b +
                b ≫ biproduct.ι F 0 ≫ b = b
              rw [hab]
              simp [b]
            | succ i =>
              rw [ha]
              simp [b, T, (Fin.succ_ne_zero i).symm] }
      have := hs.mono_f
      have := hs.epi_g
      exact hext S ⟨hs.exact⟩ (ih T fun i ↦ hF i.succ) (hF 0)

end AlgebraicGeometry.RingedSpace
