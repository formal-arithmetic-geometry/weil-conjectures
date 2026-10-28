/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.SfIntegralReductionTower

/-! # One-level representative formula for the tensor mate

Source: Stacks Project, Modules on Sites, Tag 03CZ, and Cohomology on Sites,
Tag 07A4; the coefficient calculation in the integral Verdier proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The scalar-adjunction tensor mate is represented by the ordinary contraction.
This is a one-level calculation: no consecutive quotient map occurs in it.

Source: Stacks 03CZ, lemma-adjointness-tensor-restrict; 06YY,
lemma-derived-base-change; 07A4, lemma-pullback-tensor-product.

Proof: fix the K-flat first factor P. Tensoring with P sends acyclic complexes
to acyclic complexes, hence preserves quasi-isomorphisms, by the signed cone
comparison. Extend a.representative in the second argument along the K-flat
localization. This gives e, natural on all complexes, with its prescribed value
on K-flat Q. To calculate the mate, resolve the restricted extension of Q by a
K-flat complex S. Use naturality to replace e there by its value on S. Transpose
through the scalar adjunction. Its ordinary counit multiplies scalar factors.
ReductionPresentation.normalization fixes the two tensor comparisons on the
K-flat pairs (P,S) and (P,Q). Cancel these comparisons and the resolution of S.
On each homogeneous pure tensor the resulting chain map sends
x tensor (s tensor y) to s tensor (x tensor y). Thus it is b by the tensor
universal property, sheafification, and total-summand extensionality. Localize
this identity. The restriction comparison is the exact-restriction factor of
the scalar counit, giving precisely the displayed equation. The construction
of e is independent of the coefficient level; the calculation applies separately
to every n and every normalized m, so it assumes no compatibility between them.
(blueprint: lem-sf-integral-tensor-restriction-mate-model). -/
theorem restrictionTensor_mate_model
    (a : TensorPresentation.{u, u} X (completedIntegralCommRingSheaf l E X D hl))
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : flat.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P) :
    let R := completedIntegralCommRingSheafUnrestricted l E X
    let F := fun n : ℕ ↦ (sfReductionRestricted l E X n).mapHomologicalComplex (.up ℤ)
    let T := totalTensor.{u, u} X R
    let A := (Functor.curry.obj a.tensor).obj (DerivedCategory.Q.obj P)
    ∃ e : (T.obj P) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ A,
      (∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
          (hQ : flat.{u, u} X R Q),
        e.hom.app Q = a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ∧
      ∀ (n : ℕ) (m : ReductionPresentation l E X D hl a n)
          (b : ∀ Q : CochainComplex (scalarReductionSource l E X) ℤ,
            (T.obj P).obj ((F n).obj Q) ⟶ (F n).obj ((T.obj P).obj Q)),
        (∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
            (i j : ℤ) (U : X.ProEtᵒᵖ)
            (s : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
            (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
          ((b Q).f (i + j)).val.app U
              (totalPair.{u, u} X R P ((F n).obj Q) i j U x
                (sfReductionTensor l E X n (Q.X j) U s y)) =
            sfReductionTensor l E X n (((T.obj P).obj Q).X (i + j)) U s
              (totalPair.{u, u} X R P Q i j U x y)) →
        ∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
            (_hQ : flat.{u, u} X R Q),
          A.map (sfReductionRepresentativeComparison l E X n Q) ≫
              e.inv.app ((F n).obj Q) ≫ DerivedCategory.Q.map (b Q) =
            (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.homEquiv _ _
              (m.mu.hom.app (DerivedCategory.Q.obj P,
                  (sfDerivedReductionRestricted l E X n).obj (DerivedCategory.Q.obj Q)) ≫
                m.target.tensor.map
                  (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj
                    (DerivedCategory.Q.obj P)))
                    ((derivedScalarExtensionRestrictionAdjunction.{u, u}
                      l E X n).choose.counit.app
                        ((scalarReductionDerivedExtension l E X n).obj
                          (DerivedCategory.Q.obj Q)))) ≫
                m.mu.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
              (sfDerivedReductionRestricted l E X n).map (e.inv.app Q) ≫
              sfReductionRepresentativeComparison l E X n ((T.obj P).obj Q) := by sorry

end WeilConjectures.IntegralHom
