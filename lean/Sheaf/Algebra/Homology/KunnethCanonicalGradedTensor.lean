/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Algebra.Homology.FilteredPageLocalizationSetup
public import Sheaf.Algebra.Homology.DerivedTensorModuleTorComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Algebra.Homology.KunnethCanonicalGradedCohomology

/-! # Graded cohomology of the canonical convolution tensor

Source: Stacks Project, More on Algebra, Tags 0H7X--0H7Z.
(blueprint: lem-kun-canonical-graded-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject

namespace DerivedCategory

variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Graded cohomology of the convolution of the two canonical truncation filtrations.
This assertion involves ordinary derived objects and their cohomology, without pages,
stationarity, Tor, or an abutment filtration.
Source: Stacks Project, Tags 0H7X and 0H7Y and the graded calculation in Tag 0H7Z.
(blueprint: lem-kun-canonical-graded-tensor).

Proof. Take the canonical lift T of bounded derived modules from
exists_derivedCanonicalFiltration and the convolution star from
filteredTensor_localization. Normalize their forgetful and graded functors by
comparing their localization squares on finite filtered complexes; full faithful
precomposition through the homotopy quotient and localization descends these unique
natural comparisons. Put U(C,D)=star(T(C),T(D)). The underlying convolution comparison
and the forgetful comparison of T give eTensor, naturally in both arguments.
For gr^a U choose a finite support for the graded convolution comparison. Replace
gr^i T(C) and gr^(a-i) T(D) by H^-i(C)[i] and H^-(a-i)(D)[a-i]. The tensor shift
isomorphism identifies each product with the degree-a shift of the tensor of the
corresponding modules in degree zero. Applying H^n changes the degree to n+a.
Cohomology preserves finite biproducts. Reindex i to (-i,-(a-i)); the sum of these
two indices is -a. Extend the finite coproduct to the displayed coproduct, whose
additional summands are zero because the bounded inputs have finite cohomological
support. For a pair of maps choose the union of the four supports. Naturality of
canonical grading, convolution grading, tensor shifts, and biproduct cohomology gives
the stated coproduct-map equation. The support extension equations show that the
comparison is independent of enlarging the support. Zero factors and the zero ring
satisfy the same construction; no flatness of the cohomology modules is needed. -/
theorem exists_kunnethCanonicalGradedTensor :
    let P (p q : ℤ) (C D : Bounded (ModuleCat.{u} R)) : ModuleCat.{u} R :=
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} ↦
        ((kunnethModuleTensorHomology R p).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C.obj)).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj)
    let m (p q : ℤ) {C C' D D' : Bounded (ModuleCat.{u} R)}
        (f : C ⟶ C') (g : D ⟶ D') : P p q C D ⟶ P p q C' D' :=
      Limits.Sigma.map fun ij ↦
        ((kunnethModuleTensorHomology R p).map
          ((homologyFunctor (ModuleCat.{u} R) ij.val.1).map f.hom)).app
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).obj D.obj) ≫
          ((kunnethModuleTensorHomology R p).obj
          ((homologyFunctor (ModuleCat.{u} R) ij.val.1).obj C'.obj)).map
            ((homologyFunctor (ModuleCat.{u} R) ij.val.2).map g.hom)
    ∃ (omega : finiteFilteredModuleDerivedCategory R ⥤ DerivedCategory (ModuleCat.{u} R))
      (gr : ℤ → finiteFilteredModuleDerivedCategory R ⥤ DerivedCategory (ModuleCat.{u} R))
      (eForget : ∀ P : CochainComplex.FiniteFilteredModuleComplex R,
        omega.obj ((finiteFilteredDerivedQuotient R).obj P) ≅ Q.obj P.obj.obj)
      (eGrade : ∀ (i : ℤ) (P : CochainComplex.FiniteFilteredModuleComplex R),
        (gr i).obj ((finiteFilteredDerivedQuotient R).obj P) ≅
          Q.obj (P.obj.filtration.gradedPiece i))
      (U : Bounded (ModuleCat.{u} R) ⥤ Bounded (ModuleCat.{u} R) ⥤
        finiteFilteredModuleDerivedCategory R)
      (eTensor : ∀ C D : Bounded (ModuleCat.{u} R),
        omega.obj ((U.obj C).obj D) ≅ C.obj ⊗ D.obj)
      (eGr : ∀ (C D : Bounded (ModuleCat.{u} R)) (n a : ℤ),
        (homologyFunctor (ModuleCat.{u} R) n).obj ((gr a).obj ((U.obj C).obj D)) ≅
          P (n + a) (-a) C D),
      (∀ {P P' : CochainComplex.FiniteFilteredModuleComplex R} (f : P ⟶ P'),
        omega.map ((finiteFilteredDerivedQuotient R).map f) ≫ (eForget P').hom =
          (eForget P).hom ≫ Q.map f.hom.hom) ∧
      (∀ (i : ℤ) {P P' : CochainComplex.FiniteFilteredModuleComplex R} (f : P ⟶ P'),
        (gr i).map ((finiteFilteredDerivedQuotient R).map f) ≫ (eGrade i P').hom =
          (eGrade i P).hom ≫ Q.map (FilteredObject.gradedMapSteps f.hom i)) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D'),
        omega.map ((U.map f).app D ≫ (U.obj C').map g) ≫ (eTensor C' D').hom =
          (eTensor C D).hom ≫ (f.hom ⊗ₘ g.hom)) ∧
      (∀ (C C' D D' : Bounded (ModuleCat.{u} R)) (f : C ⟶ C') (g : D ⟶ D') (n a : ℤ),
        (homologyFunctor (ModuleCat.{u} R) n).map
              ((gr a).map ((U.map f).app D ≫ (U.obj C').map g)) ≫
            (eGr C' D' n a).hom =
          (eGr C D n a).hom ≫ m (n + a) (-a) f g) := by
  dsimp only
  let d := (exists_kunnethCanonicalTensorData R).some
  obtain ⟨eGr, hGr⟩ := kunnethCanonicalGradedCohomology R d
  let U : Bounded (ModuleCat.{u} R) ⥤ Bounded (ModuleCat.{u} R) ⥤
      finiteFilteredModuleDerivedCategory R :=
    d.T ⋙ d.star ⋙ (Functor.whiskeringLeft _ _ _).obj d.T
  let eTensor (C D : Bounded (ModuleCat.{u} R)) :
      d.omega.obj ((U.obj C).obj D) ≅ C.obj ⊗ D.obj :=
    d.eta (d.T.obj C) (d.T.obj D) ≪≫ tensorIso (d.eTomega.app C) (d.eTomega.app D)
  refine ⟨d.omega, d.gr, d.eForget, d.eGrade, U, eTensor, eGr,
    d.hForget, d.hGrade, ?_, hGr⟩
  intro C C' D D' f g
  change d.omega.map ((d.star.map (d.T.map f)).app (d.T.obj D) ≫
      (d.star.obj (d.T.obj C')).map (d.T.map g)) ≫
        ((d.eta (d.T.obj C') (d.T.obj D')).hom ≫
          ((d.eTomega.app C').hom ⊗ₘ (d.eTomega.app D').hom)) =
    ((d.eta (d.T.obj C) (d.T.obj D)).hom ≫
      ((d.eTomega.app C).hom ⊗ₘ (d.eTomega.app D).hom)) ≫ (f.hom ⊗ₘ g.hom)
  rw [← Category.assoc, ← d.eta_naturality, Category.assoc, tensorHom_comp_tensorHom]
  have hf := d.eTomega.hom.naturality f
  have hg := d.eTomega.hom.naturality g
  change d.omega.map (d.T.map f) ≫ (d.eTomega.app C').hom =
    (d.eTomega.app C).hom ≫ f.hom at hf
  change d.omega.map (d.T.map g) ≫ (d.eTomega.app D').hom =
    (d.eTomega.app D).hom ≫ g.hom at hg
  rw [hf, hg, ← tensorHom_comp_tensorHom, Category.assoc]

end DerivedCategory
