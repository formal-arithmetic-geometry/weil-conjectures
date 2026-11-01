/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.IntegralStratumFiniteCdReductionsHeartBound
public import WeilConjectures.CategoryTheory.IntegralStratumFiniteCdReductionsSectionsBound
public import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralStratumHomFormula

/-!
# Hom bound for a bounded classical torsion complex on an integral stratum

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
the dual-tensor and bounded-heart steps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

private theorem subsingleton_hom_of_internal_sections
    {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasDerivedCategory.{u + 1} A]
    [MonoidalCategory (DerivedCategory A)]
    (R : A) (eunit : (DerivedCategory.singleFunctor A 0).obj R ≅
      𝟙_ (DerivedCategory A))
    (P K : DerivedCategory A) (H : DerivedCategory A ⥤ DerivedCategory A)
    (adj : tensorLeft P ⊣ H)
    (hz : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      ((preadditiveCoyoneda.obj (op R)).rightDerivedFunctor.obj (H.obj K)))) :
    Subsingleton (P ⟶ K) := by
  obtain ⟨e⟩ := derived_coyoneda_evaluation R 0
  have hz' := hz.of_iso (e.app (H.obj K))
  have hzero : Subsingleton (((DerivedCategory.singleFunctor A 0).obj R) ⟶
      (H.obj K) ⟦(0 : ℤ)⟧) := AddCommGrpCat.subsingleton_of_isZero hz'
  let E' := (Iso.homCongr (ρ_ P) (Iso.refl K)).symm |>.trans
    ((adj.homEquiv _ _).trans
      (Iso.homCongr eunit.symm ((shiftFunctorZero (DerivedCategory A) ℤ).symm.app
        (H.obj K))))
  exact E'.injective.subsingleton

/-- A finite local integral model has bounded Hom into any bounded complex with
classical locally ell-power torsion cohomology. This assertion does not involve
an ambient scheme, a closed support, a reduction functor, or a constructible target.

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
dual-tensor and bounded-heart steps; Stacks Tag 08JJ.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions-assembly).

Proof: transport the continuous integral coefficient to integralCoefficientRing.
Since cd_ell(S) <= s, choose its finite natural value s0 <= s. The finite local
model makes L[0] perfect, including its torsion summands, by the length-one DVR
resolutions. Put D=RHom(L[0],A[0]). The integral dual-torsion heart-sections theorem
places RΓ(D tensor F[0]) in [0,s0+1] for every classical local torsion module F;
use the equivalence of local torsion with the filtered prime-power-kernel union.
A K-flat representative of D makes tensoring triangulated, and derived sections
are triangulated. Bounded-heart devissage along the truncation triangles of K
therefore puts RΓ(D tensor K) in [a,b+s0+1]. The perfect-dual tensor adjunction
and the derived internal-Hom sections comparison identify Hom(L[0],K[r]) with
its r-th cohomology. This is zero when r>b+s+1, hence that Hom type is a
subsingleton. The zero module, zero complex and empty scheme satisfy the same
argument; no uniform prime-power annihilator is required. -/
theorem integralStratumFiniteCdReductions_assembly
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hL : HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X)
    (r : ℤ) (hr : b + (s : ℤ) + 1 < r) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj L ⟶ K⟦r⟧)  := by
  let D := ((derivedHom (IntegralQuotient.integral l E) S).obj (op
    ((DerivedCategory.singleFunctor _ 0).obj L))).obj
      (MonoidalCategory.tensorUnit
        (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (IntegralQuotient.integral l E) S))))
  have hheart := fun F hF ↦ integralStratumFiniteCdReductions_heart_bound
    l E S L hL D rfl s hs F hF
  have hz := integralStratumFiniteCdReductions_sections_bound l E S L hL D rfl s hs K a b hab
    hK hclass hheart r hr
  let R := Mod.regular (condensedRingObj (IntegralQuotient.integral l E) S)
  let P := (DerivedCategory.singleFunctor _ 0).obj L
  let H := (derivedHom (IntegralQuotient.integral l E) S).obj (op P)
  have hadj : tensorLeft P ⊣ H :=
    (derivedTensorHomAdjunction (IntegralQuotient.integral l E) P)
  have hzH : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      ((preadditiveCoyoneda.obj (op R)).rightDerivedFunctor.obj (H.obj (K⟦r⟧)))) := by
    simpa only [stratumModuleDerivedSections, R, H, P] using hz
  exact subsingleton_hom_of_internal_sections R
    (DerivedCategory.singleFunctorObjUnitIso _).symm P (K⟦r⟧) H hadj hzH

end CategoryTheory
