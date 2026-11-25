/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorComponents
import WeilConjectures.SixFunctors.IntegralHom.Signed.SignedHomTensorMap
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionTwoTermResolution
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomRepresentativeSquare
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # A signed complex representative of integral Hom reduction

The restricted integral Hom comparison has a signed Hom--tensor complex representative.

## Implementation details

The quotient at exponent `n + 1` is resolved by the free rank-one complex in degrees `-1, 0`
with differential multiplication by the `(n + 1)`-st power of a uniformizer, base changed to
the completed ring sheaf; it is K-flat. With a K-flat representative `P` of the source and a
K-injective representative `I` of the target, the representative is the chain map
`f (v ⊗ z) (x) = (-1)^(deg z * deg x) v x ⊗ z` from `Hom(P, I) ⊗ Q` to `Hom(P, I ⊗ Q)`.

## References

* Stacks Project, Tags 093M, 06YQ, 08J7, 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

-- Preserve the original existential binder names.
set_option linter.unusedVariables false in
-- Use the existing sheafification at the coefficient universe for this declaration.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The restricted comparison has the signed Hom--tensor complex representative.
This asserts its chain-level formula and the normalization square, with no
invertibility assertion about the representative map or its components. -/
theorem comparison_representative
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let U := scalarReductionDerivedRestriction l E Y n
    let F := integralDerivedReduction l E Y D hl n
    ∃ (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
      (_ : flat.{t, u} Y R P) (_ : I.IsKInjective)
      (_ : Nonempty (Iso (C := DerivedCategory (Modules.{t, u} Y R)) (DerivedCategory.Q.obj P) K))
      (_ : Nonempty (Iso (C := DerivedCategory (Modules.{t, u} Y R)) (DerivedCategory.Q.obj I) L))
      (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
      (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
      (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
      (f : ((totalTensor.{t, u} Y R).obj
          (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
        homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
          (((totalTensor.{t, u} Y R).obj I).obj Q)),
      IsSignedHomTensor.{t, u} Y R P I Q f ∧
      ∃ (s : U.obj (F.obj ((hom.{t, u} Y R).obj (op K, L))) ≅
          DerivedCategory.Q.obj (((totalTensor.{t, u} Y R).obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q))
        (t : U.obj ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
            (op (F.obj K), F.obj L)) ≅
          DerivedCategory.Q.obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
              (((totalTensor.{t, u} Y R).obj I).obj Q))),
        U.map (comparison l E Y D hl m K L) ≫ t.hom = s.hom ≫ DerivedCategory.Q.map f := by
  classical
  let R := completedIntegralCommRingSheaf l E Y D hl
  let A := Modules.{t, u} Y R
  have : IsGrothendieckAbelian.{max u (t + 1)} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R).1
  let G : CochainComplex A ℤ := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) G
  have : QuasiIso p := hp
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A p).2 hp
  let eP : Iso (C := DerivedCategory A) (DerivedCategory.Q.obj P) K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let G' : CochainComplex A ℤ := DerivedCategory.Q.objPreimage L
  let I := (CochainComplex.kInjectiveResolutionFunctor.{max u (t + 1)} A).obj G'
  have hI : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj A G'
  let eta := (CochainComplex.toKInjectiveResolution.{max u (t + 1)} A).app G'
  have heta : QuasiIso eta :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A G').2
  have : IsIso (DerivedCategory.Q.map eta) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A eta).2 heta
  let eI : Iso (C := DerivedCategory A) (DerivedCategory.Q.obj I) L :=
    (asIso (DerivedCategory.Q.map eta)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso L
  obtain ⟨Q, hQ, hzero, eNeg, eZero, epsilon, hepsilon⟩ :=
    integralReduction_twoTerm_resolution l E Y D hl n
  obtain ⟨f, hf⟩ := signedHomTensor_exists Y R P I Q
  obtain ⟨s, t, hsquare⟩ := comparison_representative_square l E Y D hl a n m K L
    P I Q hP hI eP eI hQ hzero eNeg eZero epsilon hepsilon f hf
  exact ⟨P, I, Q, hP, hI, ⟨eP⟩, ⟨eI⟩, hzero, eNeg, eZero, f, hf, s, t, hsquare⟩

end WeilConjectures.IntegralHom
