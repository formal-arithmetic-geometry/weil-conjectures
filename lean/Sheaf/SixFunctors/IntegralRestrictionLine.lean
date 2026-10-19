/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.SixFunctors.IntegralBrownAdjoint
public import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.SixFunctors.IntegralTensorInverseImage
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.IntegralProperProjectionFormula
import Sheaf.Paper.IntegralOpenImageProperFormulas
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.AffineTraceTower
import Sheaf.Paper.IntegralExtensionByZero
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias
import Sheaf.Paper.DiagonalTowerLimit
import Sheaf.Paper.FormalClosedSupportSheaves
import Sheaf.Paper.ProjectionSectionNormalization
import Sheaf.Paper.TraceBaseChangeFirst
import Sheaf.Paper.TraceBaseChangeSecond
import Sheaf.SixFunctors.IntegralLocalizingCompactSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Integral purity for the projective line and affine space

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
sk-thm-int-restriction-line.md, clauses (1)--(3)
(blueprint: det-thm-int-restriction-line).

The twists use the published integral Tate line and its signed powers. The sectionwise
module equivalence transports that line into the same internal-module category as Brown's
adjunction. All functors below use ordinary unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The published signed Tate line, transported back to internal modules by the existing
sectionwise module equivalence. No new coefficient line or scalar action is chosen.
Source: blueprint sk-thm-int-restriction-line, Tate twist convention
(blueprint: det-thm-int-restriction-line). -/
def tateLine (X : Scheme.{u}) (d : ℤ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)).inverse.obj
      (spSignedTwist X _ (spIntegralTwist X ℓ E) d)

/-- The actual functor f^*(-)(d)[2d]: derived pullback, right tensor with the published
Tate line in degree zero, and shift by 2d.
Source: blueprint sk-thm-int-restriction-line, displayed right adjoints
(blueprint: det-thm-int-restriction-line). -/
def pullTwistShift {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) Y ⥤
      IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) X :=
  IntegralCompactSupport.pull (Profinite.padicIntegersRingObj ℓ E.val) f ⋙
    (derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).flip.obj
      ((DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X (d : ℤ))) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- Restriction of f^*(-)(d)[2d] to the recorded Loc(Dbc) categories. The membership
witness only restricts its codomain and does not replace any functor or morphism.
Source: blueprint sk-thm-int-restriction-line, localizing-category convention
(blueprint: det-thm-int-restriction-line). -/
def restrictedPull {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X
        ((pullTwistShift ℓ E f d).obj K)) :
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory :=
  (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X).lift
    ((IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).ι ⋙
      pullTwistShift ℓ E f d) (fun K ↦ h K.obj K.property)

/-- Restriction of the actual Rf_* to Loc(Dbc), once its preservation is supplied.
Source: blueprint sk-thm-int-restriction-line, projective-line left adjoint
(blueprint: det-thm-int-restriction-line). -/
def restrictedPush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f).obj K)) :
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory ⥤
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory :=
  (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).lift
    ((IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X).ι ⋙
      IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f)
    (fun K ↦ h K.obj K.property)

/-- Comparison with any Brown right adjoint for the chosen boundary compactification.
Brown's theorem does not choose an adjoint, so its isomorphism class is stated using
its defining adjunction. Quantification over compactifications includes the fixed one.
Source: blueprint sk-thm-int-restriction-line, the two f^! comparisons
(blueprint: det-thm-int-restriction-line). -/
def brownComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory) : Prop :=
  ∀ (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.image (Profinite.padicIntegersRingObj ℓ E.val)
          c.obj.obj).obj K))
    (J : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory),
    Nonempty (IntegralCompactSupport.lowerShriek
      (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ J) → Nonempty (J ≅ G)

/-- Projective-line adjunction, affine-space purity, and preservation of Dbc by both
explicit candidate right adjoints, on exactly Loc(Dbc) for condensed integral coefficients.
Source: blueprint main-20261015, sk-thm-int-restriction-line.md, clauses (1)--(3)
(blueprint: det-thm-int-restriction-line).

Proof plan:
1. The Tate sheaves of sk-def-sp-tate-twist are locally free of rank one. The single
stratum and scalar model put them in Dbc (sk-def-sfb-constructible). Pullback and tensor
preserve Dbc by sk-lem-int-tensor; shifts reindex cohomology. Exact pullback is Cartesian
(sk-prop-sfb-cartesian-coefficients) and left adjoint to Rf_* by
 def-sfb-module-derived-pushpull-adjunction, hence preserves sums. Twists and shifts are
exact equivalences preserving sums. Minimality of sk-def-localizing-closure extends
preservation to Loc(Dbc). det-def-localizing-closure-ctf-equals-bc identifies it with
Loc(Dctf) on the standing qcqs schemes. This also proves clause (3).
2. Put P = P1_Y, W = P times_Y P, with projections p1,p2 and diagonal Delta.
The projections are proper (lemma-nagata-projective-space-base-change-proper), Delta
is closed and proper (def-weil-proper-morphism, lem-weil-pbc-closed-immersion-proper).
Use det-prop-int-brown-construction to identify their compact-support and ordinary
pushforwards, compatibly with composition. For Delta the latter is exact by
 det-lem-formal-closed-support-sheaves.
3. det-thm-sf-pf-adic-projection gives a_M : p1^*M tensor Delta_*R_P iso Delta_*M.
Use delta : Delta_*R_P -> R_W(1)[2] and trace t_q from det-prop-diagonal-tower-limit,
 det-prop-diagonal-tower-coefficients and det-prop-diagonal-tower-trace. Set
v_M = Rp2_*(1 tensor delta) Rp2_*(a_M inverse). The base-change mates b_i and projection
formula give B_M : Rp2_*(p1^*M tensor R_W(1)[2]) iso q^*Rq_*M(1)[2]. Define eta_M = B_M v_M
and epsilon_K = (1 tensor t_q) pi_q inverse. Use def-weil-pbc-adjunction-mate,
 sk-thm-sf-pf-adic and lem-weil-pbc-ringed-topoi-derived-tensor-pullback for these comparisons.
4. lem-sfb-trace-base-change-first rewrites epsilon_RqM Rq_*(B_M) as
Rq_*(1 tensor t_p1) Rq_*(pi_p1 inverse). Precompose with Rq_*v_M and move delta by
projection naturality. lem-sfb-projection-section-normalization for (p1,Delta) cancels
a_M with pi_p1. The remaining scalar t_p1 Rp1_*delta is one by
 det-prop-diagonal-tower-trace(2), extended integrally by coefficients(1).
5. lem-sfb-trace-base-change-second similarly rewrites G(epsilon_K) B_GK.
Identify p1^*GK with p2^*GK using Cartesian twists and pullback/tensor comparison.
Precompose with v_GK; normalization for (p2,Delta) leaves
1_GK tensor (t_p2 Rp2_*delta), again one. The two even shifts introduce no sign.
6. The two triangles make h |-> G(h) eta and a |-> epsilon F(a) inverse natural Hom
bijections, so Rq_* is left adjoint to G = q^*(-)(1)[2]. For any Brown adjoint transport
its adjunction using the proper compactification comparison of
 det-prop-int-brown-construction. det-sp-unique-right-adjoint identifies it with G.
7. For the standard chart j : A1_T -> P1_T (def-amb-affine-trace-tower), quasi-compactness
is checked over the two affine charts: their inverse images are Spec B[t] and
Spec B[s,s^-1]. det-cor-int-compactness-ii-extension-zero preserves Loc(Dbc), so the
open adjunction of def-sfb-dc-open-lower-shriek-adjunction restricts to those categories.
The compactification comparison gives Ru_! iso Rq_* j_! for u = qj.
8. Compose this open adjunction with the projective-line adjunction by
 def-weil-pbc-composite-adjunction. Composition of pullback and Cartesian twists gives
right adjoint u^*(-)(1)[2]. Transport to the chosen compactification before applying
 det-prop-int-brown-adjoint and det-sp-unique-right-adjoint.
9. Induct on d using def-amb-affine-trace-tower. At zero the affine projection is an
isomorphism, and its compact-support functor is the identity under the canonical
identification; use the identity adjunction. At the successor compose the line
adjunction with the induction adjunction, identify pullbacks and tensor powers, and
add the even shifts to obtain d+1 and 2d+2. Compactification comparisons are compatible
with composition (det-prop-int-brown-construction), so uniqueness identifies this
adjoint with the Brown adjoint. This proves clause (2), including d=0.
-/
theorem integralRestrictionLine (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (d : ℕ) :
    ∃ (hq : ∀ K, IntegralCompactSupport.localizing
          (Profinite.padicIntegersRingObj ℓ E.val) Y K →
        IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
          ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
      (hp : ∀ K, IntegralCompactSupport.localizing
          (Profinite.padicIntegersRingObj ℓ E.val) Y K →
        IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
          (AffineSpace (ULift.{u} (Fin d)) Y)
          ((pullTwistShift ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) d).obj K))
      (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
        IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
          ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K)),
      Nonempty (restrictedPush ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) hr ⊣
        restrictedPull ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1 hq) ∧
      brownComparison ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)
        (restrictedPull ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1 hq) ∧
      brownComparison ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
        (restrictedPull ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) d hp) ∧
      (∀ K, constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K →
        constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
          ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K)) ∧
      (∀ K, constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K →
        constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val)
          (AffineSpace (ULift.{u} (Fin d)) Y)
          ((pullTwistShift ℓ E (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) d).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
