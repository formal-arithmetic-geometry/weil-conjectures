/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteTensorNaturality
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientKFlatRepresentatives
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientKFlatReflection
public import WeilConjectures.SixFunctors.Etale.EtaleKFlatTensorPresentation
/-! # Representatives for the finite coefficient site tensor comparison
The finite coefficient site comparison has a resolving tensor presentation on complexes whose
pro-etale inverse images are K-flat.

## References

* [Stacks, Tags 06YN and 07A4]
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d e f g w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
/-- A resolving tensor presentation: restriction to `P × P` is fully faithful on functor
categories, the source tensor comparison is presented on `P`, and the chain tensor comparison
is natural, with all functor data shared. -/
def FiniteHomTensorPresentationAux
    {K : Type a} {L : Type b} {A : Type c} (B : Type d)
    [Category.{e} K] [Category.{f} L] [Category.{g} A] [Category.{w} B]
    (q : K ⥤ A) (U : K ⥤ L) (t : K × K ⥤ K) (t' : L × L ⥤ L)
    (T : A × A ⥤ A) (P : ObjectProperty K)
    {M : K → K → Type g} (η : ∀ x y, M x y)
    {V : K → K → Type f} (ε : ∀ x y, V x y) : Prop :=
  Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (A × A) B).obj ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful) ∧
    FiniteHomSourceTensorPresentationAux q t T P η ∧
    FiniteHomChainTensorNaturalityAux U t t' ε

private theorem tensorPresentationOfParts
    {K : Type a} {L : Type b} {A : Type c} (B : Type d)
    [Category.{e} K] [Category.{f} L] [Category.{g} A] [Category.{w} B]
    (q : K ⥤ A) (U : K ⥤ L) (t : K × K ⥤ K) (t' : L × L ⥤ L)
    (T : A × A ⥤ A) (P : ObjectProperty K)
    {M : K → K → Type g} (η : ∀ x y, M x y)
    {V : K → K → Type f} (ε : ∀ x y, V x y)
    (ff : Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (A × A) B).obj ((P.ι ⋙ q).prod (P.ι ⋙ q))).FullyFaithful))
    (r : FiniteHomSourceTensorPresentationAux q t T P η)
    (b : FiniteHomChainTensorNaturalityAux U t t' ε) :
    FiniteHomTensorPresentationAux B q U t t' T P η ε := by
  exact ⟨ff, r, b⟩

attribute [local irreducible] coefficientTotalTensor finiteHomNuComplex
  finiteHomNuChainTensor finiteHomEtaleTensorModel finiteHomEtaleData

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The site comparison has a resolving tensor presentation before derived descent.
The assertions concern only restriction to representatives, the source localization
map, and the ordinary chain comparison; they supply no derived tensor comparison. -/
theorem finiteHomNuTensorPresentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :
    let K := CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ
    let P : ObjectProperty K := fun P ↦
      @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
        ((finiteHomNuComplex l E X n).obj P)
    let t : K × K ⥤ K := finiteHomCochainTensorGeneral _
    let Q := finiteHomEtaleQ l E X n
    let U := finiteHomNuComplex l E X n
    let S := (finiteHomEtaleClosed l E X n).tensor
    FiniteHomTensorPresentationAux (normalizedDVRDerived l E X n) Q U t
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)) S P
      (finiteHomEtaleTensorModel l E X n) (finiteHomNuChainTensor l E X n)  := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  dsimp only
  apply tensorPresentationOfParts
  · unfold finiteHomNuComplex finiteHomNuOrdinary
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    exact finiteCoefficientKFlatRepresentativesFullyFaithful
        (Padic.coefficientExtensionRing l E (n + 1)) X
        (hD := inferInstanceAs (HasDerivedCategory.{u + 1}
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))))
        (normalizedDVRDerived l E X n)
  · exact finiteHomEtaleKFlatTensorPresentation l E X n _
      (fun P hP ↦ finiteHomNuKFlatReflection l E X n P hP)
  · exact finiteHomNuChainTensor_naturalIso l E X n

end WeilConjectures
