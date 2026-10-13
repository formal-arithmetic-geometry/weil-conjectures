/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.DerivedTensorActionNaturality

/-! # Construction of the derived coefficient comparison

Source: Stacks Project, Tag 06Y6, and equation-bc (Tag 0DJ7).
(blueprint: lem-pc-base-tensor-derived-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

/-- The scalar-extension counit on homology, without an invertibility assumption.
Source: Stacks Project, Tag 06Y6.
(blueprint: lem-pc-base-tensor-derived-comparison). -/
def scalarExtensionHomologyMap {A D : Type u} [CommRing A] [CommRing D]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} D)] (ρ : A →+* D)
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} ρ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj (L.obj (DerivedCategory.Q.obj P)) ⟶
      (((extendScalars.{u, u, u} ρ).mapHomologicalComplex (.up ℤ)).obj P).homology i :=
  (DerivedCategory.homologyFunctor _ i).map
    (L.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        (((extendScalars.{u, u, u} ρ).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _) ≫
    (DerivedCategory.homologyFunctorFactors _ i).hom.app _

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} D)]

/-- The representative formula characterizing the derived coefficient comparison.
The coefficient map is quantified with its generator formula, so this condition
makes no choice of a tensor model.
Source: Stacks Project, Tag 06Y6; equation-bc, Tag 0DJ7.
(blueprint: lem-pc-base-tensor-derived-comparison). -/
def IsBaseTensorDerivedComparison
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (δ : DerivedCategory.Qh ⋙ F ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (i : ℤ)
    (τ : (restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙ F ⋙
        DerivedCategory.homologyFunctor _ i ⟶
      L ⋙ DerivedCategory.homologyFunctor _ i ⋙
        restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
          restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom) : Prop :=
  let r := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let t := restrictScalars.{u} (algebraMap (A ⊗[R] B) D)
  let c := fun P : CochainComplex (ModuleCat.{u} A) ℤ ↦
    ((extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj P
  ∀ (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (β : ((extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (r.mapHomologicalComplex (.up ℤ)).obj
        ((t.mapHomologicalComplex (.up ℤ)).obj (c P))),
    (∀ (j : ℤ) (b : B) (p : P.X j),
      β.f j (b ⊗ₜ[R, algebraMap R B] p) =
        (algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b) ⊗ₜ[A,
          (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))] p)) →
    (DerivedCategory.homologyFunctor _ i).map
      (F.map (((DerivedCategory.quotientCompQhIso _).app _ ≪≫
        (restrictScalars.{u} (algebraMap R A)).mapDerivedCategoryFactors.symm.app P).inv) ≫
        δ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj P))) ≫
      (DerivedCategory.homologyFunctorFactorsh _ i).hom.app _ ≫
      (HomotopyCategory.homologyFunctorFactors _ (.up ℤ) i).hom.app _ ≫
      HomologicalComplex.homologyMap β i ≫
      ((((t.mapHomologicalComplex (.up ℤ)).obj (c P)).sc i).mapHomologyIso r).hom ≫
      r.map (((c P).sc i).mapHomologyIso t).hom =
    τ.app (DerivedCategory.Q.obj P) ≫
      (restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
        restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map
          (scalarExtensionHomologyMap _ L ε P i)

/-- Construct the derived coefficient comparison before introducing cohomology models.

Proof: choose an A-K-flat resolution U to P and an R-K-flat resolution V to
its restricted complex. Compute F on V using its invertible resolution counit.
The augmentation V to the restriction of U, followed by coefficient extension,
gives a B-linear chain map V tensor_R B to the B-restriction of U tensor_A D:
on generators b tensor v maps to the image of 1 tensor b tensor v in D tensor U.
The invertible A-to-D counit on U identifies its target with L(Q(U)). Transport
by the quasi-isomorphism U to P to obtain the comparison at Q(P).
Comparison maps of resolutions commute with this coefficient map on generators.
For a roof representing a derived A-linear morphism, resolve its three complexes
and use those commuting squares; independence of refinements and compatibility
with composition give a natural transformation on D(A). Apply degree-i homology.
Compose the resulting comparison with the A-to-D counit at P, which need not be
invertible. Naturality of both resolution augmentations and the two counits gives
the displayed representative equation, with the specified localization factors.
Apply the restriction homology isomorphisms successively, first from D to the
tensor algebra and then to B. Tensor induction identifies every beta with the
coefficient map from its generator formula. The universal properties identify
arbitrary F and L with the resolution functors by their unique counit-compatible
isomorphisms. No flatness of A over R or of D is used.
Source: Stacks Project, Section 06Y5, Tag 06Y6 (derived change of rings), and
perfect.tex, the construction preceding equation-bc (Tag 0DJ7).
(blueprint: lem-pc-base-tensor-derived-comparison). -/
theorem exists_baseTensorDerivedComparison
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (δ : DerivedCategory.Qh ⋙ F ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hF : F.IsLeftDerivedFunctor δ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (L : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} D))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars.{u, u, u} ((algebraMap (A ⊗[R] B) D).comp
        (algebraMap A (A ⊗[R] B)))).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) (i : ℤ) :
    ∃ τ : (restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙ F ⋙
        DerivedCategory.homologyFunctor _ i ⟶
      L ⋙ DerivedCategory.homologyFunctor _ i ⋙
        restrictScalars.{u} (algebraMap (A ⊗[R] B) D) ⋙
          restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom,
      IsBaseTensorDerivedComparison R A B D F δ L ε i τ := by sorry

end ModuleCat
