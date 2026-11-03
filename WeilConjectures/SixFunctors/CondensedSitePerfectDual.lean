/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeSitePerfectDual

/-! # Perfect duals over pulled-back condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-prop-sf-dualizable-biduality/prop-sf-dualizable.md and its proof
(blueprint: prop-sf-dualizable).

The coefficient index lists the finite quotient, integers, field and condensed algebraic
closure. All four use the same ordinary derived category of internal modules over p_X^*Λ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The four coefficient choices, in the order A_{E,n}, O_E, E, Qbar_ell.
The finite quotient has the discrete topology; O_E and E have the spectral topology.
The closure is the existing condensed ring of finite-subextension-valued sections.
This only indexes the existing coefficient constructions, with no completion or localization.
Source: prop-sf-dualizable, opening coefficient convention (blueprint: prop-sf-dualizable). -/
def sfPerfectDualCoefficient (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) :
    Fin 4 → CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  | 0 =>
      letI : TopologicalSpace (Padic.coefficientExtensionRing ell E n) := ⊥
      letI : DiscreteTopology (Padic.coefficientExtensionRing ell E n) := ⟨rfl⟩
      CommMon.mk (Profinite.continuousCoefficientRingObj
        (Padic.coefficientExtensionRing ell E n))
  | 1 =>
      letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
      CommMon.mk (Profinite.continuousCoefficientRingObj
        (Padic.coefficientExtensionIntegers ell E))
  | 2 =>
      letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
      CommMon.mk (Profinite.continuousCoefficientRingObj E)
  | _ => CommMon.mk (Profinite.padicAlgClRingObj ell)

/-- Evaluation is the counit at the coefficient unit of the recorded relative
K tensor - / RHom(K,-) adjunction. It is global and independent of local models.
Source: prop-sf-dualizable, last sentence; proof step 4 (blueprint: prop-sf-dualizable). -/
def sfCondensedPerfectEvaluation
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X))) :
    ((CondensedRing.derivedTensor Λ.X X).obj K).obj
        (((CondensedRing.derivedHom Λ.X X).obj (op K)).obj (𝟙_ _)) ⟶ 𝟙_ _ :=
  (CondensedRing.derivedTensorHomAdjunction Λ.X K).counit.app (𝟙_ _)

/-- A site-perfect object of D^b_ctf has site-perfect coefficient dual.
The accompanying evaluation is sfCondensedPerfectEvaluation, the actual adjunction counit.
A coefficient presentation identifies Λ with one of the four indicated condensed rings;
it does not supply a different tensor, Hom, or derived category.
Source: current blueprint prop-sf-dualizable, entire statement
(blueprint: prop-sf-dualizable).

Proof, following the four DAG steps:
1. Choose a bounded finite-projective representative on each covering slice, refining
   the covers of its finitely many terms to obtain finite-free retractions. Exact slice
   restriction preserves the quasi-isomorphism. The internal-Hom sections model and
   exact-restriction comparison identify the restricted dual with RHom(P,Lambda[0]).
2. The split-perfect dual Tor-window lemma represents this Hom by the signed termwise
   dual D^j = Hom(P^{-j},Lambda), with differential (-1)^{j+1} phi d_P^{-j-1}.
   A model supported in [a,b] gives a dual supported in [-b,-a].
3. Precomposition dualizes each finite-free retraction; Hom(Lambda^r,Lambda) = Lambda^r.
   Thus every dual term is finite projective, giving the required local perfect models.
   The bounds and ranks may vary across the cover.
4. The tensor-Hom adjunction counit at the unit gives sfCondensedPerfectEvaluation
   globally, independently of representatives. No coefficient-stage descent is used. -/
theorem sfCondensed_sitePerfect_dual
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (_S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ : ∃ i : Fin 4, Nonempty (Λ ≅
      (CommMon.forget₂Mon _).obj (sfPerfectDualCoefficient C.l E n i)))
    (K : ConstantModelConstructibleFiniteTor Λ.X X.obj.left)
    (_hK : CondensedRing.IsPerfectOnCoefficientSite Λ.X X.obj.left K.obj) :
    CondensedRing.IsPerfectOnCoefficientSite Λ.X X.obj.left
      (((CondensedRing.derivedHom Λ.X X.obj.left).obj (op K.obj)).obj (𝟙_ _)) := by
  simpa only [CondensedRing.derivedHom, MonoidalClosed.internalHom] using
    (CondensedRing.native_sitePerfect_dual Λ.X X.obj.left K.obj _hK).1

end WeilConjectures
