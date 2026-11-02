/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleScalar.ConstantModuleScalarCenter
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Normalized finite-basis inclusions for exact constant scalar extension -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w i
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit
open scoped ChangeOfRings

namespace CategoryTheory.ConstantModuleScalar

/-- The scalar-unit inclusions are finite-biproduct inclusions with their prescribed
pure-tensor representatives on every unbounded complex.
Source: Stacks 03CY, 03CZ and 07A6; finite-coefficient transport Steps 1 and 3
(blueprint: lem-pur-constant-scalar-normalized-basis).
Proof: sheafify the basis of B over A and its dual coordinate functionals. They give
mutually inverse maps between restricted tensor extension of M and a finite power
of M. Define each inclusion as the scalar unit followed by multiplication by its
basis vector; the adjunction formula makes this precisely x maps to b_a tensor x.
The coordinate functional sends c tensor x to q_a(c)x. Tensor balancing proves
linearity, including for locally constant coefficient sections. The basis expansion
and Kronecker identities prove both finite-matrix identities before sheafification;
the universal property of sheafification preserves them. All maps are natural in M,
so they commute with differentials. Apply the exact localization to these cochain
maps and their matrix identities. The localized unit and both exact-functor
factorizations yield exactly the last equation below. Transport the matrix
identities along Q.objObjPreimageIso to arbitrary derived objects. The empty
basis gives the zero object and the same empty-sum identity. -/
theorem normalized_basis
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (A B : CommRingCat.{r}) [Algebra A B]
    [HasDerivedCategory.{w} (modules (constantRing J A))]
    [HasDerivedCategory.{w} (modules (constantRing J B))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))
    [PreservesFiniteLimits D.E] [PreservesFiniteColimits D.E]
    [PreservesFiniteLimits (restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))]
    [PreservesFiniteColimits (restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))]
    (a : D.E ⊣ restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))
    (ha : ∀ (M : modules (constantRing J A)) (N : modules (constantRing J B))
      (f : SheafOfModules.changeOfRings.{v, u, r}
        ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M ⟶ N)
      (V : Cᵒᵖ) (x : M.val.obj V),
      (a.homEquiv M N (eqToHom (D.obj_eq M) ≫ f)).val.app V x =
        f.val.app V ((toSheafify J
          (SheafOfModules.changeOfRingsPresheaf.{v, u, r}
            ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B)))
              M).presheaf).app V
                ((1 : (constantRing J B).obj.obj V)
                  ⊗ₜ[(constantRing J A).obj.obj V,(((constantSheaf J CommRingCat).map
                    (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x)))
    {I : Type i} [Fintype I] (b : Module.Basis I A B) :
    let U := (restriction ((constantSheaf J CommRingCat).map
      (CommRingCat.ofHom (algebraMap A B)))).mapDerivedCategory
    let S := D.E.mapDerivedCategory
    let ι := fun (M : DerivedCategory (modules (constantRing J A))) (c : I) ↦
      a.onDerivedCategory.unit.app M ≫ U.map ((derived J B (b c)).app (S.obj M))
    (∀ M, ∃ q : I → (U.obj (S.obj M) ⟶ M),
      (∀ c d : I, ι M c ≫ q d =
        @ite _ (c = d) (Classical.propDecidable _) (𝟙 M) 0) ∧
      ∑ c : I, q c ≫ ι M c = 𝟙 _) ∧
    ∀ (K : CochainComplex (modules (constantRing J A)) ℤ) (c : I),
      ∃ k : K ⟶ ((restriction ((constantSheaf J CommRingCat).map
        (CommRingCat.ofHom (algebraMap A B)))).mapHomologicalComplex (.up ℤ)).obj
          ((D.E.mapHomologicalComplex (.up ℤ)).obj K),
        (∀ (n : ℤ) (V : Cᵒᵖ) (x : (K.X n).val.obj V),
          (k.f n).val.app V x =
            (eqToHom (D.obj_eq (K.X n)).symm).val.app V
              ((toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, u, r}
                ((constantSheaf J CommRingCat).map
                  (CommRingCat.ofHom (algebraMap A B))) (K.X n)).presheaf).app V
                    ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V (b c)
                      ⊗ₜ[(constantRing J A).obj.obj V,
                        (((constantSheaf J CommRingCat).map
                          (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x))) ∧
        ι (DerivedCategory.Q.obj K) c ≫
            U.map (D.E.mapDerivedCategoryFactors.hom.app K) ≫
            (restriction ((constantSheaf J CommRingCat).map
              (CommRingCat.ofHom (algebraMap A B)))).mapDerivedCategoryFactors.hom.app
                ((D.E.mapHomologicalComplex (.up ℤ)).obj K) = DerivedCategory.Q.map k := by
  sorry

end CategoryTheory.ConstantModuleScalar
