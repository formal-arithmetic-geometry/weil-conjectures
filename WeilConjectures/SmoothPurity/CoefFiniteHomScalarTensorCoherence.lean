/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes

/-! # A proper subargument of finite coefficient internal-Hom comparison

Source: the latest blueprint `thm-coef-finite-hom` and its proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Tensor compatibility of the specified native scalar compositors, identities and symmetry.

Source: the latest blueprint `thm-coef-finite-hom.proof.md`, the tensor
associativity argument for successive and identity coefficient change
(blueprint: lem-coef-native-scalar-tensor-coherence).

Proof: use the actual sectionwise restriction compositor and identity. Under
the normalized derived scalar adjunctions their mates are finiteHomScalarComp
and finiteHomScalarId. On functorial flat resolutions the derived unit formula
identifies these mates with their ordinary balanced scalar analogues. Scalar
extension preserves flat terms and sends the chosen flat resolutions to K-flat
complexes, so this computation is valid for arbitrary, possibly nonflat ring
maps. Compute the two tensor routes on total pure generators: in both cases
successive scalar factors are multiplied in the same order and the tensor
factors have the same Koszul sign. For identity coefficients the generator
formula is scalar multiplication. Paste with the cochain counit normalization
squares for the native tensorators. Cancel the K-flat representative comparison
isomorphisms and transport along representative isomorphisms, proving the two
etale tensor equations. On the pro-etale site the core is transported from the
native side-framework derived scalar functor. Normalize its defining adjunction
uniqueness isomorphism with the same ordinary scalar unit formula; the same
balanced generator calculation and cancellation prove the two pro-etale
equations. For symmetry, the ordinary scalar oplax tensorator commutes with the
sheaf braiding by the scalar-adjunction mate formula. Derive this equality on
flat resolutions, where the total tensor swap has the same Koszul sign on both
routes. Descend to the derived category and transport the pro-etale equality
along the adjunction-uniqueness isomorphism defining proCore. These are only
tensor equations and their right-evaluation consequences. Naturality of braiding
moves the Hom comparison through the swap; left evaluation compatibility then
identifies both right-evaluation routes. Monoidal compatibility of the unit
and of internal Hom is derived separately by the parent theorem. -/
theorem finiteCoefficientHomScalarTensorCoherence
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C)
    (hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (hB : ∃ n : ℕ, (ell ^ n : B) = 0)
    (hC : ∃ n : ℕ, (ell ^ n : C) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    finiteHomLaw_tensor_successive_etale X φ ψ ∧
      finiteHomLaw_tensor_identity_etale (A := A) X ∧
      finiteHomLaw_tensor_successive_pro X φ ψ ∧
      finiteHomLaw_tensor_identity_pro (A := A) X ∧
      finiteHomLaw_tensor_symmetry_etale X φ ∧
      finiteHomLaw_tensor_symmetry_pro X φ ∧
      finiteHomLaw_evaluation_right_etale X φ ∧
      finiteHomLaw_evaluation_right_pro X φ := by
  sorry

end WeilConjectures
