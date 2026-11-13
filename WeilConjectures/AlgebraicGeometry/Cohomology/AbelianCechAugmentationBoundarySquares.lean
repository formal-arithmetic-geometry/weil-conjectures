/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechExtSectionIso
import WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechHorseshoeTotalBoundary
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechExtSectionBoundary

/-! # Boundary squares before taking the augmentation quotient

Source: Stacks Project, Tags 01EQ, 013T and 0117.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The coefficient and section augmentations have the same total boundary.
Source: Stacks 01EQ, augmented double complex. -/
theorem abelianCechAugmentation_boundary_squares
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) (q : ℕ)
    (I₁ : InjectiveResolution T.X₁) (I₃ : InjectiveResolution T.X₃)
    (e₁ : (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁ ≅
      (abelianCechSections I₁).homology (q + 1))
    (e₃ : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃ ≅
      (abelianCechSections I₃).homology q)
    (he₁ : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) (q + 1)).obj T.X₁),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₁.cocomplex.X (q + 1))
        (ha : a ≫ I₁.cocomplex.d (q + 1) ((q + 1) + 1) = 0)
        (z : (abelianCechSections I₁).cycles (q + 1)),
        I₁.extMk a ((q + 1) + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I₁).iCycles (q + 1) z ∧
        e₁.hom t = (abelianCechSections I₁).homologyπ (q + 1) z)
    (he₃ : ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj T.X₃),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I₃.cocomplex.X q)
        (ha : a ≫ I₃.cocomplex.d q (q + 1) = 0)
        (z : (abelianCechSections I₃).cycles q),
        I₃.extMk a (q + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I₃).iCycles q z ∧
        e₃.hom t = (abelianCechSections I₃).homologyπ q z) :
    ∃ (δ : ((abelianCechDouble U I₃).total (.up ℕ)).homology q ⟶
        ((abelianCechDouble U I₁).total (.up ℕ)).homology (q + 1)),
      TopCat.Sheaf.cechδ U hT hg q ≫
          HomologicalComplex.homologyMap (abelianCechBeta U I₁) (q + 1) =
        HomologicalComplex.homologyMap (abelianCechBeta U I₃) q ≫ δ ∧
      Sheaf.functorHδ hT q ≫ e₁.hom ≫
          HomologicalComplex.homologyMap (abelianCechAlpha U I₁) (q + 1) =
        e₃.hom ≫ HomologicalComplex.homologyMap (abelianCechAlpha U I₃) q ≫ δ :=
  by
    classical
    obtain ⟨I₂, α, β, hα, hβ, hαβ, hrows⟩ :=
      InjectiveResolution.exists_horseshoe_prescribed_resolutions T hT I₁ I₃
    let F := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation _ _).obj (op (⊤ : X.Opens))
    let S := (ShortComplex.mk α β hαβ).map (F.mapHomologicalComplex (.up ℕ))
    have hS : S.ShortExact := by
      apply HomologicalComplex.shortExact_of_degreewise_shortExact
      intro n
      have : Injective (((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval _ (.up ℕ) n)).X₁) := I₁.injective n
      exact ((hrows n).1.splittingOfInjective.map F).shortExact
    obtain ⟨δ, hbeta, halpha⟩ := abelianCechHorseshoe_total_boundary
      T hT I₁ I₂ I₃ α β hαβ hα hβ (fun n ↦ (hrows n).1) hS U hg q
    have he := abelianCechExtSection_boundary T hT I₁ I₂ I₃ α β hαβ hα hβ
      (fun n ↦ (hrows n).1) hS q e₁ e₃ he₁ he₃
    refine ⟨δ, hbeta, ?_⟩
    calc
      Sheaf.functorHδ hT q ≫ e₁.hom ≫
          HomologicalComplex.homologyMap (abelianCechAlpha U I₁) (q + 1) =
        (Sheaf.functorHδ hT q ≫ e₁.hom) ≫
          HomologicalComplex.homologyMap (abelianCechAlpha U I₁) (q + 1) :=
            (Category.assoc _ _ _).symm
      _ = (e₃.hom ≫ hS.δ q (q + 1) rfl) ≫
          HomologicalComplex.homologyMap (abelianCechAlpha U I₁) (q + 1) := by rw [he]
      _ = e₃.hom ≫ HomologicalComplex.homologyMap (abelianCechAlpha U I₃) q ≫ δ := by
        rw [Category.assoc, halpha]

end AlgebraicGeometry.Scheme.Modules
