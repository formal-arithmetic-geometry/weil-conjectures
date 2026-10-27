/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Sheaf.RingTheory.GradedLocalAttractionRegularity
import WeilConjectures.Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange

/-! # Smooth affine concentrators

Source: Milne, Algebraic Groups (2017), Definition 13.21, Propositions 13.22--13.24
and Lemmas 13.25--13.27, printed pp.261--263
(blueprint: lem-sfb-smooth-affine-concentrator).

Products and morphisms are in the category of k-schemes. Thus an extension from
Spec R × A¹ to X is equivalently an R-morphism A¹_R → X_R. Its restriction uses
the canonical inclusion of polynomials into Laurent polynomials, and its value
at zero uses polynomial evaluation, over arbitrary commutative test algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- The attracting functor of a smooth invariant closed subscheme of a smooth affine
scheme is represented by a smooth finite-type closed subscheme. Orbit extensions
are unique, and the displayed morphism to Z is evaluation at zero on every test algebra.

Source: Milne, Algebraic Groups (2017), Definition 13.21, Propositions 13.22--13.24,
printed pp.261--263 (blueprint: lem-sfb-smooth-affine-concentrator).

Proof, following the seven steps of the DAG node:
1. Write X = Spec A and Z = Spec(A/a). The action coaction decomposes A into its
   integer homogeneous pieces: comparing Laurent coefficients gives c(f_n) = f_n t^n,
   the counit gives f = Σ f_n, and multiplication respects degrees. Invariance makes
   a homogeneous. Put b = (a ∩ A_0, A_n for n < 0) and Y = Spec(A/b). This is a
   finite-type closed subscheme of X.
2. Over any commutative R, the orbit sends f to Σ x(f_n)t^n. Polynomial inclusion
   into Laurent polynomials is injective, including for nonreduced R. Extension is
   equivalent to killing the negative pieces and is unique. Its value at zero is
   f ↦ x(f_0); it factors through Z exactly when x kills a ∩ A_0. These conditions
   are precisely x(b) = 0. Degree-zero projection modulo b is multiplicative and
   kills a, giving the limit morphism Y → Z and the asserted evaluation identity.
3. The quotient construction commutes with field extension. Use
   lem-sfb-scheme-large-algclosed-jacobson to choose an algebraically closed extension
   with dense rational closed points. Smoothness of X and Z survives base change
   by lem-pc-proper-base-change, and their local rings are regular by
   lem-weil-pbc-smooth-scheme-over-field-regular.
4. For a closed point y of Y let z be its fixed limit. Localize A at the degree-zero
   functions not vanishing at z. The degree-zero ring is local, with homogeneous
   maximal ideal the kernel of evaluation at z. Noetherianity follows from
   lem-wf-affine-noetherian-components and localization. The local rings of A and
   A/a there are regular by step 3. Apply lem-sfb-graded-local-attraction-regularity
   to deduce regularity of the local ring of Y at z.
5. By lem-weil-pbc-regular-closed-point-smooth-source and
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine, Y has a smooth open neighbourhood
   of z. The extended orbit of y lies in Y and meets that neighbourhood at some
   nonzero scalar, since the algebraically closed field is infinite. Scalar action
   is an automorphism of Y, so its inverse supplies a smooth neighbourhood of y.
6. The complement of the smooth opens has no closed point and hence is empty by
   lem-sfb-scheme-large-algclosed-jacobson. Apply
   lem-weil-pbc-smooth-local-on-source, also when Y is empty.
7. The finite-type algebra A/b is finitely presented by
   lem-weil-pbc-finite-type-noetherian-finite-presentation. The field extension is
   flat and surjective by lem-pc-field-extension-flat and
   lem-pc-field-extension-surjective. Its base change is surjective by
   lem-weil-pbc-surjective-base-change. Descend smoothness pointwise using
   lem-sfb-scheme-lfp-smooth-flat-base-change, then apply
   lem-weil-pbc-smooth-local-on-source. Step 2 proves all functor and evaluation
   assertions over every commutative algebra without any reducedness assumption. -/
theorem exists_smooth_affine_concentrator
    {k : Type u} [Field k] (X Z : Over (Spec (.of k)))
    [IsAffine X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [Smooth X.hom] [Smooth Z.hom]
    (a : ModObj (StandardGroupSchemes.multiplicative k) X)
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (hi : ∃ aZ : ModObj (StandardGroupSchemes.multiplicative k) Z,
      (𝟙 (StandardGroupSchemes.multiplicative k) ⊗ₘ i) ≫ a.smul = aZ.smul ≫ i) :
    ∃ (Y : Over (Spec (.of k))) (j : Y ⟶ X) (π : Y ⟶ Z),
      IsClosedImmersion j.left ∧ Smooth Y.hom ∧
      LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
      (∀ (R : CommAlgCat.{u} k) (x : StandardGroupSchemes.affine k R ⟶ X),
        (∃ y, y ≫ j = x) ↔
          ∃ q : StandardGroupSchemes.affine k R ⊗ StandardGroupSchemes.additive k ⟶ X,
            (𝟙 (StandardGroupSchemes.affine k R) ⊗ₘ
                StandardGroupSchemes.map k (Polynomial.toLaurentAlg (R := k))) ≫ q =
              lift (snd _ _) (fst _ _ ≫ x) ≫ a.smul ∧
            ∃ z : StandardGroupSchemes.affine k R ⟶ Z,
              lift (𝟙 _) (StandardGroupSchemes.map k (Polynomial.aeval (0 : R))) ≫ q =
                z ≫ i) ∧
      (∀ (R : CommAlgCat.{u} k) (x : StandardGroupSchemes.affine k R ⟶ X)
        (q q' : StandardGroupSchemes.affine k R ⊗ StandardGroupSchemes.additive k ⟶ X),
        (𝟙 (StandardGroupSchemes.affine k R) ⊗ₘ
            StandardGroupSchemes.map k (Polynomial.toLaurentAlg (R := k))) ≫ q =
          lift (snd _ _) (fst _ _ ≫ x) ≫ a.smul →
        (𝟙 (StandardGroupSchemes.affine k R) ⊗ₘ
            StandardGroupSchemes.map k (Polynomial.toLaurentAlg (R := k))) ≫ q' =
          lift (snd _ _) (fst _ _ ≫ x) ≫ a.smul → q = q') ∧
      (∀ (R : CommAlgCat.{u} k) (y : StandardGroupSchemes.affine k R ⟶ Y)
        (q : StandardGroupSchemes.affine k R ⊗ StandardGroupSchemes.additive k ⟶ X),
        (𝟙 (StandardGroupSchemes.affine k R) ⊗ₘ
            StandardGroupSchemes.map k (Polynomial.toLaurentAlg (R := k))) ≫ q =
          lift (snd _ _) (fst _ _ ≫ y ≫ j) ≫ a.smul →
        lift (𝟙 _) (StandardGroupSchemes.map k (Polynomial.aeval (0 : R))) ≫ q =
          y ≫ π ≫ i) := by
  sorry

end AlgebraicGeometry
