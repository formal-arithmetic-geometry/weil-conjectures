/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.InvariantSymmetricPowerLifting
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.Maximal

/-! # Base change and local descent for invariant symmetric-power lifting

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemma 9.2.5(2),(5), pp.522--523, and Proposition 9.3.1(i),(ii), p.524.
(blueprint: lem-sfb-invariant-power-base-change-descent)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Pointwise

namespace AlgebraicGeometry.InvariantPower

/-- Expose the supplied group diagrams on the underlying scheme over its base.
Source: Mathlib Group/Affine, Tag 022S.
(blueprint: lem-sfb-invariant-power-base-change-descent) -/
instance coordinateGroup (A : CommRingCat.{u}) (H : Grp (Over (Spec A))) :
    GrpObj (H.X.left.asOver (Spec A)) := H.grp

/-- Pull back the actual group diagrams, along the spectrum of the supplied ring map.
Source: Alper, Proposition 9.3.1; Mathlib Cartesian Over pullback.
(blueprint: lem-sfb-invariant-power-base-change-descent) -/
noncomputable abbrev baseChange {A B : CommRingCat.{u}} (f : A ⟶ B)
    (H : Grp (Over (Spec A))) : Grp (Over (Spec B)) :=
  (Over.pullback (Spec.map f)).mapGrp.obj H

/-- Affineness of the actual fibre product, using the affine-morphism base-change instance.
Source: Mathlib Morphisms/Affine, Tag 01SD.
(blueprint: lem-sfb-invariant-power-base-change-descent) -/
noncomputable instance affineBaseChange {A B : CommRingCat.{u}} (f : A ⟶ B)
    (H : Grp (Over (Spec A))) [IsAffine H.X.left] :
    IsAffine (baseChange f H).X.left :=
  inferInstanceAs (IsAffine (pullback H.X.hom (Spec.map f)))

/-- Expose the canonical coordinate Hopf structure of the actual pullback group.
The bundled target ring is retained to guide inference for concrete localizations.
Source: Mathlib Group/Affine, Tag 022S.
(blueprint: lem-sfb-invariant-power-base-change-descent) -/
@[instance_reducible]
noncomputable def baseChangeCoordinateHopf {A B : CommRingCat.{u}} (f : A ⟶ B)
    (H : Grp (Over (Spec A))) [IsAffine H.X.left] :
    HopfAlgebra B Γ((baseChange f H).X.left, ⊤) := inferInstance

/-- The four base-change and descent assertions, without a Noetherian hypothesis.
Affineness of the total scheme equals affineness over the affine base; it also
makes quasi-compactness and quasi-separatedness automatic, so local finite
presentation is finite presentation here.
Source: Alper, Lemma 9.2.5(2),(5), pp.522--523, Proposition 9.3.1(i),(ii), p.524.
(blueprint: lem-sfb-invariant-power-base-change-descent)

Proof:
1. Put C = A[H]. Affine flatness makes C flat. Affine-chart base change identifies
   the new coordinate Hopf algebra with B tensor C. The symmetric-algebra
   base-change isomorphism preserves the tensor-image grading, evaluation and
   coaction, as is checked on degree-one generators.
2. For an arbitrary B-module quotient N -> B, restrict the C-coaction to
   E = {(x,a) in N directSum A | lambda(x) = a*1_B}. Flat tensor exactness makes
   this restriction well defined and proves its coaction identities. E -> A is
   equivariant and surjective; no flatness of B or N is used.
3. Apply P(A,H) to E -> A and send its invariant homogeneous lift through
   Sym_A(E) -> Sym_B(N). The universal property proves equivariance and
   evaluation compatibility on generators, giving assertion (1).
4. For (2), write V_n = ker(rho_n - (q -> q tensor 1)), with evaluation epsilon_n.
   Flat tensor exactness identifies B tensor V_n with the new invariants.
   A lift of 1 over B makes B tensor epsilon_n surjective. Faithfully flat
   exactness detection makes epsilon_n surjective, giving a lift over A.
5. For (3), exactness of localization and its tensor-product description identify
   local invariants with localized V_n. Clear denominators in a local lift of 1
   to find q in V_n whose evaluation is outside the chosen maximal ideal.
6. Thus the sum of all positive-degree evaluation ideals lies in no maximal ideal
   and is the unit ideal. Choose finitely many evaluations generating 1. Raise
   the corresponding invariants to a common positive degree. The powers of the
   evaluations still generate 1 (test maximal ideals), and a linear combination
   of those invariant powers evaluates to 1. Over the zero ring use n=1, q=0.
7. For (4), the finite product of the B_i is flat. Joint surjectivity gives a
   nonzero residue-field quotient over each maximal ideal, so this product is
   faithfully flat by the maximal-ideal criterion.
8. Raise local invariant lifts to a common degree. The finite-coordinate tensor
   isomorphism assembles them into a lift over the product; apply faithful flat
   exactness detection as in step 4. An empty jointly surjective cover forces
   the zero ring, where n=1, q=0 works.
-/
theorem invariantPower_baseChange_descent (A : CommRingCat.{u})
    (H : Grp (Over (Spec A))) [IsAffine H.X.left]
    [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom] :
    (∀ (B : CommRingCat.{u}) (f : A ⟶ B),
      InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u} A Γ(H.X.left, ⊤) →
      InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u}
        B Γ((baseChange f H).X.left, ⊤)) ∧
    (∀ (B : CommRingCat.{u}) (f : A ⟶ B),
      f.hom.FaithfullyFlat →
      InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u}
        B Γ((baseChange f H).X.left, ⊤) →
      InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u} A Γ(H.X.left, ⊤)) ∧
    ((∀ m : MaximalSpectrum A,
      let B : CommRingCat.{u} := .of (Localization.AtPrime m.asIdeal)
      let f : A ⟶ B := CommRingCat.ofHom (algebraMap A (Localization.AtPrime m.asIdeal))
      letI : HopfAlgebra B Γ((baseChange f H).X.left, ⊤) := baseChangeCoordinateHopf f H
      InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u}
        B Γ((baseChange f H).X.left, ⊤)) →
      InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u} A Γ(H.X.left, ⊤)) ∧
    (∀ (I : Type u) [Finite I] (B : I → CommRingCat.{u}) (f : ∀ i : I, A ⟶ B i),
      (∀ i : I, Etale (Spec.map (f i))) →
      (∀ x : Spec A, ∃ (i : I) (y : Spec (B i)), (Spec.map (f i)).base y = x) →
      (∀ i : I, InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u}
        (B i) Γ((baseChange (f i) H).X.left, ⊤)) →
      InvariantSymmetricPower.HasInvariantPowerLifting.{u, v, u} A Γ(H.X.left, ⊤)) := by
  sorry

end AlgebraicGeometry.InvariantPower
