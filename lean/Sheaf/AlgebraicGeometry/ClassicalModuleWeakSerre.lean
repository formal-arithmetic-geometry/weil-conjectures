/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.Paper.ProEtaleConstantModuleEncoding
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Classical module sheaves form a weak Serre subcategory

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-cor-pe-classical-derived/sk-cor-pe-classical-derived-weak-serre.md
(blueprint: det-pe-classical-derived-weak-serre).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped ZeroObject

private theorem image_kernel {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (L : C ⥤ D) [L.Full] [L.Faithful]
    [Limits.PreservesFiniteLimits L] [L.PreservesZeroMorphisms]
    {X Y : D} (f : X ⟶ Y) (hX : L.essImage X) (hY : L.essImage Y) :
    L.essImage (Limits.kernel f) := by
  obtain ⟨A, ⟨eA⟩⟩ := hX
  obtain ⟨B, ⟨eB⟩⟩ := hY
  let g := L.preimage (eA.hom ≫ f ≫ eB.inv)
  refine ⟨Limits.kernel g, ⟨Limits.PreservesKernel.iso L g ≪≫ Limits.kernel.mapIso _ f eA eB ?_⟩⟩
  simp [g]

private theorem image_cokernel {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (L : C ⥤ D) [L.Full] [L.Faithful]
    [Limits.PreservesFiniteColimits L] [L.PreservesZeroMorphisms]
    {X Y : D} (f : X ⟶ Y) (hX : L.essImage X) (hY : L.essImage Y) :
    L.essImage (Limits.cokernel f) := by
  obtain ⟨A, ⟨eA⟩⟩ := hX
  obtain ⟨B, ⟨eB⟩⟩ := hY
  let g := L.preimage (eA.hom ≫ f ≫ eB.inv)
  refine ⟨Limits.cokernel g,
    ⟨Limits.PreservesCokernel.iso L g ≪≫ Limits.cokernel.mapIso _ f eA eB ?_⟩⟩
  simp [g]

private theorem image_extension {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [EnoughInjectives D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R) [L.Full] [L.Faithful]
    [L.Additive] [R.Additive] [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits R] {S : ShortComplex D} (hS : S.ShortExact)
    (h₁ : L.essImage S.X₁) (h₃ : L.essImage S.X₃)
    (hz : Limits.IsZero ((R.rightDerived 1).obj S.X₁)) : L.essImage S.X₂ := by
  obtain ⟨δ, hm, hall⟩ := hS.exists_rightDerived_full_long_exact R
  obtain ⟨hex, w₁, w₂, hr, hl⟩ := hall 0
  have hep : Epi ((R.rightDerived 0).map S.g) :=
    ((ShortComplex.mk _ _ w₁).exact_iff_epi (hz.eq_of_tgt _ _)).mp hr
  have hs0 : (S.map (R.rightDerived 0)).ShortExact := ShortComplex.ShortExact.mk' hex hm hep
  have hsR : (S.map R).ShortExact :=
    ShortComplex.shortExact_of_iso (S.mapNatIso R.rightDerivedZeroIsoSelf) hs0
  have := hsR.mono_f
  have := hsR.epi_g
  have hsLR : ((S.map R).map L).ShortExact := hsR.map L
  let φ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  have hi₁ : IsIso φ.τ₁ := adj.isIso_counit_app_iff_mem_essImage.mpr h₁
  have hi₃ : IsIso φ.τ₃ := adj.isIso_counit_app_iff_mem_essImage.mpr h₃
  have hi₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hsLR hS
  exact ⟨R.obj S.X₂, ⟨asIso φ.τ₂⟩⟩

private theorem image_derived_one {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives D] (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    [L.Additive] [R.Additive] [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [IsIso adj.derivedPlus.unit] (F : C) :
    Limits.IsZero ((R.rightDerived 1).obj (L.obj F)) := by
  let K := (DerivedCategory.Plus.singleFunctor C 0).obj F
  have hz := DerivedCategory.Plus.isZero_homology_of_isLE K 0 1 (by decide)
  let e := asIso (adj.derivedPlus.unit.app K) ≪≫
    R.rightDerivedFunctorPlus.mapIso ((L.mapDerivedCategoryPlusSingleFunctor 0).app F)
  exact hz.of_iso (((DerivedCategory.Plus.homologyFunctor C 1).mapIso e) ≪≫
    R.homologyRightDerivedFunctorPlusObjSingleFunctorIso (L.obj F) 1).symm

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Classical sheaves of modules over a discrete commutative coefficient ring contain
zero and are closed under kernels, cokernels and extensions.
Source: current blueprint, main-20261015, sk-cor-pe-classical-derived,
sk-cor-pe-classical-derived-weak-serre.md
(blueprint: det-pe-classical-derived-weak-serre).

Proof, following the seven steps of the node:
1. The existing proEtaleModuleEncoding identifies intrinsic modules over the
   constant ring sheaf with fixed-coefficient module-valued sheaves, preserving
   underlying additive sheaves up to the equivalence counit. By
   det-pe-classical-sheaves-modules, classical objects are the essential image
   of comparison inverse image L composed with the inverse encoding equivalence.
   This composite is exact and fully faithful and preserves zero.
2. Lift a morphism between classical objects to a morphism of etale module sheaves
   by full faithfulness. Exactness identifies its kernel and cokernel with the
   L-images of the lifted kernel and cokernel, so both are classical.
3. Work with fixed-coefficient sheaves in universe u+1. ModuleCat is Grothendieck
   abelian, and so is its pro-etale sheaf category by
   lem-sfb-proetale-sheaves-grothendieck. The latter has enough injectives by
   lem-sp-grothendieck-enough-injectives. The right adjoint R is additive and
   left exact, since comparison direct image is restriction on sections.
   Transport the short exact sequence through the encoding equivalence.
4. For a short exact sequence with classical outer terms G' = L F' and G = L F,
   apply sk-prop-sf-comparison to F'[0]. Its derived unit is invertible.
   lem-sp-derived-functor-single-identification identifies its degree-one
   cohomology on the right with the first right derived functor of R at L F'.
5. Apply degree-one cohomology, as in def-weil-abstract-derived-category. Since
   F'[0] has zero cohomology in degree one, the first right derived functor of R
   vanishes at G'. This also holds after transporting along the chosen isomorphism.
6. The beginning of lem-weil-pbc-derived-functor-long-exact, using the degree-zero
   identification of lem-sp-derived-well-defined, now shows that R takes this
   sequence to a short exact sequence.
7. Apply exact L to that sequence and use naturality of the counit to obtain a
   morphism to the original short exact sequence. Full faithfulness makes the
   unit invertible, and the triangle identity makes the counit invertible on
   L-images. Thus the outer vertical maps are invertible. By
   lem-weil-pbc-short-five-lemma so is the middle counit, showing that the middle
   term is in the essential image of L. Transporting back through the encoding
   equivalence shows that the original middle term is classical. -/
theorem classicalModule_weakSerre (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    IsClassicalModule (X := X) Λ 0 ∧
      ObjectProperty.IsClosedUnderKernels (IsClassicalModule (X := X) Λ) ∧
      ObjectProperty.IsClosedUnderCokernels (IsClassicalModule (X := X) Λ) ∧
      ObjectProperty.IsClosedUnderExtensions (IsClassicalModule (X := X) Λ) := by
  classical
  let R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} Λ)))
  let P : ObjectProperty (SheafOfModules.{u + 1} R) := IsClassicalModule Λ
  let L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) :=
    comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X
  let E := (Scheme.proEtaleModuleEncoding X Λ).symm
  let V := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) AddCommGrpCat.{u + 1})
  let e : E.functor ⋙ SheafOfModules.toSheaf.{u + 1} R ≅ V :=
    NatIso.ofComponents
      (fun F ↦ V.mapIso ((Scheme.proEtaleModuleEncoding X Λ).counitIso.app F))
      (fun f ↦ by
        exact congrArg V.map ((Scheme.proEtaleModuleEncoding X Λ).counitIso.hom.naturality f)
          |>.trans (by simp only [Functor.map_comp]; rfl))
  obtain ⟨adj, hlim, hcolim, hfull, hc, himage⟩ :=
    proEtaleClassicalSheavesModules X (ULift.{u + 1, u} Λ)
  let T : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) ⥤
      SheafOfModules.{u + 1} R := L ⋙ E.functor
  have : T.PreservesZeroMorphisms := inferInstance
  have : Limits.PreservesFiniteLimits T := inferInstance
  have : Limits.PreservesFiniteColimits T := inferInstance
  have hIso {F G : SheafOfModules.{u + 1} R} (i : F ≅ G) : P F ↔ P G := by
    rw [show P F = IsClassicalModule Λ F from rfl,
      show P G = IsClassicalModule Λ G from rfl,
      isClassicalModule_iff, isClassicalModule_iff]
    exact isClassical_iso_iff
      ((SheafOfModules.toSheaf.{u + 1} R ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).mapIso i)
  have hE (F : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) :
      P (E.functor.obj F) ↔ IsClassical
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))).obj F) := by
    rw [show P (E.functor.obj F) = IsClassicalModule Λ (E.functor.obj F) from rfl,
      isClassicalModule_iff]
    exact isClassical_iso_iff
      ((sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).mapIso
        (e.app F))
  have hP (G : SheafOfModules.{u + 1} R) : P G ↔ T.essImage G := by
    constructor
    · intro hG
      obtain ⟨F, ⟨i⟩⟩ := (himage (E.inverse.obj G)).mp
        ((hE _).mp ((hIso (E.counitIso.app G)).mpr hG))
      exact ⟨F, ⟨E.functor.mapIso i ≪≫ E.counitIso.app G⟩⟩
    · rintro ⟨F, ⟨i⟩⟩
      apply (hIso i).mp
      exact (hE _).mpr ((himage _).mpr ⟨F, ⟨Iso.refl _⟩⟩)
  have hk : ObjectProperty.IsClosedUnderKernels P := by
    constructor
    rintro Z ⟨f, k, hk, hA, hB⟩
    apply (hIso (hk.conePointUniqueUpToIso (Limits.kernelIsKernel f))).mpr
    exact (hP _).mpr (image_kernel.{u + 1, u + 2, u + 1, u + 2} (C :=
      Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) (D := SheafOfModules.{u + 1} R) T f
      ((hP _).mp hA) ((hP _).mp hB))
  have hck : ObjectProperty.IsClosedUnderCokernels P := by
    constructor
    rintro Z ⟨f, k, hk, hA, hB⟩
    apply (hIso (hk.coconePointUniqueUpToIso (Limits.cokernelIsCokernel f))).mpr
    exact (hP _).mpr (image_cokernel.{u + 1, u + 2, u + 1, u + 2} (C :=
      Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) (D := SheafOfModules.{u + 1} R) T f
      ((hP _).mp hA) ((hP _).mp hB))
  have hext : ObjectProperty.IsClosedUnderExtensions P := by
    constructor
    intro S hS h₁ h₃
    let A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
    let R₁ := comparisonLowerStar A X
    let adj₀ := comparisonAdjunction A X
    have hunit : IsIso adj₀.derivedPlus.unit := (boundedBelowComparison X (ULift.{u + 1, u} Λ)).1
    have hleft : L.essImage (E.inverse.obj S.X₁) :=
      (himage _).mp ((hE _).mp ((hIso (E.counitIso.app _)).mpr h₁))
    have hright : L.essImage (E.inverse.obj S.X₃) :=
      (himage _).mp ((hE _).mp ((hIso (E.counitIso.app _)).mpr h₃))
    have hz : Limits.IsZero ((R₁.rightDerived 1).obj (E.inverse.obj S.X₁)) := by
      obtain ⟨F, ⟨i⟩⟩ := hleft
      exact (image_derived_one L R₁ adj₀ F).of_iso ((R₁.rightDerived 1).mapIso i).symm
    have := hS.mono_f
    have := hS.epi_g
    have hSE : (S.map E.inverse).ShortExact := hS.map E.inverse
    have hI : L.essImage (E.inverse.obj S.X₂) :=
      image_extension (C := Sheaf X.smallEtaleTopology A)
        (D := Sheaf (Scheme.ProEt.topology X) A) L R₁ adj₀
        (S := S.map E.inverse) hSE hleft hright hz
    obtain ⟨F, ⟨i⟩⟩ := hI
    let j : E.functor.obj (L.obj F) ≅ E.functor.obj (E.inverse.obj S.X₂) :=
      E.functor.mapIso i
    let k : T.obj F ≅ S.X₂ := j ≪≫ E.counitIso.app S.X₂
    have hm : T.essImage S.X₂ := ⟨F, ⟨k⟩⟩
    exact @Iff.mpr (P S.X₂) (T.essImage S.X₂) (hP S.X₂) hm
  have hzero : P (0 : SheafOfModules.{u + 1} R) :=
    (hP _).mpr ⟨0, ⟨Functor.mapZeroObject.{u + 1, u + 1, u + 2, u + 2} T⟩⟩
  exact ⟨hzero, hk, hck, hext⟩

end AlgebraicGeometry.ProEtale
