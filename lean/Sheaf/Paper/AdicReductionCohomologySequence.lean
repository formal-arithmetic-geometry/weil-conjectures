/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The cohomology sequence for a completed DVR quotient

Source: blueprint integral truncations, hypothesis paragraph, and the quotient-resolution
argument in steps 1 and 3 of lem-weil-pbc-adic-tor-flat-cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The universal-coefficient short exact sequence for the completed DVR coefficient
quotient. No flatness or bounded constructibility of the complex is assumed. The
endomorphism is multiplication by a uniformizer to the power n+1 on the unit module;
the existential formulation avoids choosing a uniformizer in downstream definitions.
Its monicity is independent of the complex. The first arrow is the scalar restriction
of the homology adjunct of the normalized derived unit.

Source: blueprint integral truncations, hypothesis paragraph; steps 1 and 3 of
lem-weil-pbc-adic-tor-flat-cohomology; Stacks Project, Tags 06YY and 03EK.
(blueprint: lem-weil-pbc-adic-reduction-cohomology-sequence).

Proof: choose a uniformizer of the finite extension's integer DVR. Flatness of its
completed constant coefficient sheaf, and the completed finite-quotient comparison,
give the exact two-term resolution B --varpi^(n+1)--> B of R_n. In particular its
first map f is monic. Tensor this resolution with a K-flat representative of K.
Its cone computes restriction of the derived quotient extension. The long exact
cohomology sequence gives a short exact sequence from the cokernel of multiplication
on H^q(K) to reduced H^q(K), followed by its connecting epimorphism onto the kernel
of multiplication on H^(q+1)(K). Right exactness of ordinary scalar extension
identifies that cokernel with restricted ordinary extension of H^q(K). The unit
normalization of both scalar adjunctions identifies this injection with the displayed
adjunct: on cocycles it sends z to z tensor 1. Tensoring the unit endomorphism f
with H^(q+1)(K) is its multiplication map, giving precisely the kernel displayed.
The argument works in every degree and for the zero and empty-site cases. -/
theorem pbc_adic_reduction_cohomology_sequence
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    let d := pbcPadicCoefficientDatum l E
    let B := pbcAdicCompletion T d
    let φ := pbcAdicProjection T d n
    let O := SheafOfModules.unit ((adicLisseForget T).obj B)
    ∃ f : O ⟶ O, Mono f ∧
      ∀ (K : PbcCompletedDerived T d) (q : ℤ),
        let H := (DerivedCategory.homologyFunctor _ (q + 1)).obj K
        let c := ((pbcScalarAdjunction φ).homEquiv _ _).symm
          ((DerivedCategory.homologyFunctor _ q).map
              ((pbcDerivedScalarAdjunction φ).unit.app K) ≫
            ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).inv.app
              ((pbcDerivedExtend φ).obj K))
        ∃ δ : (pbcRestrict φ).obj
            ((DerivedCategory.homologyFunctor _ q).obj ((pbcDerivedExtend φ).obj K)) ⟶
            kernel ((SheafOfModules.siteSheafTensorRight
              (J := ProEt.topology T) (A := B) H).map f),
          ∃ h : (pbcRestrict φ).map c ≫ δ = 0,
            (ShortComplex.mk ((pbcRestrict φ).map c) δ h).ShortExact := by
  sorry

end AlgebraicGeometry.Scheme
