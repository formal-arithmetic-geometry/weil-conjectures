/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalCoefficient.PrincipalCoefficientUniversalPair
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
import WeilConjectures.AlgebraicGeometry.PrincipalCoefficient.PrincipalCoefficientTensorModel
import WeilConjectures.AlgebraicGeometry.PrincipalCoefficient.PrincipalCoefficientTensorEvaluation

/-! # Tensor evaluation for principal coefficient coinduction

Source: latest blueprint lem-fix-operation-reduction, principal coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
attribute [local instance 2000] CommRing.toRing
namespace AlgebraicGeometry.PrincipalCoefficient

/-- Coinduction is extension tensored with coinduction of the coefficient unit.
Source: latest blueprint lem-fix-operation-reduction, the finite-free resolution argument;
Stacks 0A70, 0A71 and 0BZE (perfect tensor--Hom evaluation)
(blueprint: lem-principal-coefficient-coinduction-tensor).

Proof: write B = A/(a^n). The exact two-term complex A --a^n--> A resolves B;
regularity of a implies regularity of a^n. Its associated constant sheaf complex
is bounded finite free, including n = 0 when it is contractible. Choose a K-flat
complex P for the input and a K-injective resolution I of the A-coefficient unit.
The ordinary comparison sends x tensor h to the coinduced map b maps to h(b)x,
using the multiplication action (b h)(b') = h(b'b). It is therefore B-linear.
Compose with a K-injective replacement of the target. On forgetting B, compute
Hom from the two-term finite-free resolution of B. Finite sums commute with all
the products in this Hom complex, so tensor--Hom evaluation is invertible for
arbitrary unbounded P. K-flatness makes replacing the unit by I harmless.
Restriction detects quasi-isomorphisms, hence the B-linear derived comparison is
invertible. Its construction by the actual coinduction counit gives the displayed
objectwise isomorphism.
For the zero quotient both sides lie in the zero derived category. -/
theorem principalCoinductionTensor
    {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Nonempty
      ((extension X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {a} ^ n))).obj K ⊗
          (Etale.coextendScalars
            (Ideal.Quotient.mk (Ideal.span {a} ^ n)) X).rightDerivedFunctor.obj
              (𝟙_ (_root_.DerivedCategory
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) ≅
        (Etale.coextendScalars
            (Ideal.Quotient.mk (Ideal.span {a} ^ n)) X).rightDerivedFunctor.obj K) := by
  classical
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let φ := Ideal.Quotient.mk (Ideal.span {a} ^ n)
  let H := (Etale.coextendScalars φ X).rightDerivedFunctor
  let F := extension X.smallEtaleTopology φ ⋙ tensorRight (H.obj (𝟙_ _))
  let L := _root_.DerivedCategory.Q.objPreimage K
  let Λ := (Classical.choice (inferInstance : Abelian.HasFunctorialFlatResolution C)).reduced
  let P := Λ.resolutionFunctor.obj L
  let p := Λ.resolutionNatTrans.app L
  have hp : QuasiIso p := inferInstance
  have hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le L
  let eK : _root_.DerivedCategory.Q.obj P ≅ K :=
    asIso (_root_.DerivedCategory.Q.map p) ≪≫
      _root_.DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨I, hI, η, hη, J, hJ, q, hq, e, d, t, ht⟩ :=
    tensorCoinduction_chainModel φ X P hP
  let := hI
  let := hJ
  let := hq
  have := principalTensorEvaluation_quasiIso ha n X P I J hP q t ht
  exact ⟨(F.mapIso eK).symm ≪≫ e ≪≫ asIso (_root_.DerivedCategory.Q.map t) ≪≫
    d.symm ≪≫ H.mapIso eK⟩

end AlgebraicGeometry.PrincipalCoefficient
