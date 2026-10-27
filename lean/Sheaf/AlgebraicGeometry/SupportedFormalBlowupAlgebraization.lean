/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.SupportedCenteredBlowupTowers
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Blowup.Gluing

import WeilConjectures.Blowup.Affine.Defs
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.FlatBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper

/-! # Algebraization of supported formal blowup towers, retaining the centers

Source: Temkin, Non-embedded Desingularization, Lemma 2.4.3(i)--(ii), printed
pp.15--16, with §§2.2.1--2.2.2 and 2.4.1--2.4.11
(blueprint: lem-per-supported-formal-blowup-algebraization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AdicFormal

/-- Completion is a correspondence up to unique centered isomorphism in each finite
length, in both directions. Every center is canonically the same ordinary scheme at
any order containing the whole formal center. Terminal regularity descends when the
base singular locus is contained in the completion locus and centers lie over it.
For reduced X those ordinary centers are nowhere dense.

Source: Temkin, Lemma 2.4.3(i)--(ii), printed pp.15--16
(blueprint: lem-per-supported-formal-blowup-algebraization).

Proof, following the node's ten steps:
1. On Spec A in any ordinary level, put K=I O and complete A. A formal supported
ideal H contains K^N. The canonical quotient identification
lem-weil-pbc-adic-completion-mod-power identifies Ahat/K^N with A/K^N.
The inverse image J of H/K^N in A contains K^N, extends to H, and has
A/J canonically equal to Ahat/H. Extension and contraction are inverse by this
same quotient calculation, independently of a larger exponent.
2. On a principal open the quotient map localizes to the same map of finite
quotients, so the recovered ideals glue on principal affine refinements by
lem-weil-pbc-affine-ideals-closed-subscheme. Their finite presentations follow
from Noetherianity, hence coherence in pqf-def-coherent. A finite cover gives a
common exponent. The center identifications glue over the same closed thickening.
3. thm-nagata-global-blowup-proper and def-weil-proper-morphism make each
ordinary blowup finite type. lem-weil-pbc-finite-type-over-noetherian makes its
source Noetherian, including zero and unit centers, so induction can continue.
4. Completion is flat by lem-weil-pbc-noetherian-completion-flat. Apply
thm-nagata-blowup-flat-base-change with def-nagata-blowup-flat-base-change-map.
For a blowup affine C, (C tensor Ahat)/K^n is C/K^n, compatibly in n, by the
canonical finite quotient theorem. Inverse limits identify the completed charts
and their restrictions. This is exactly the formal blowup. Noetherianity of
completed charts is lem-weil-pbc-adic-completion-noetherian.
5. Induct on r, starting with the specified base for r=0. Recover the next ideal
by steps 1--2, take its ordinary blowup, and compare completions by step 4.
Conversely complete each level and each ordered ideal. The quotient calculation
recovers each original ideal. No identity stage is deleted.
6. For uniqueness use thm-nagata-blowup-principalizes-center and
prop-nagata-affine-blowup-chart-cover. On an intrinsic a-chart A[J/a] inside A_a,
multiplication by a is injective, and a(j/a)=j forces any base automorphism to
fix every ratio. It therefore fixes the chart. After completion multiplication
by a remains injective by flatness; continuity and separatedness extend the
identity from the dense chart ring. Induct to get unique centered tower isomorphisms.
7. Step 2 identifies actual center schemes over the same finite thickening.
Nonemptiness and regularity therefore agree. Their maps to the base identify
singular support. thm-nagata-global-blowup-complement identifies each ordinary
level off the inverse image of Z with X minus Z.
8. For terminal regularity, the complement of Z is regular by the singular-locus
hypothesis. At y over Z take Spec A and its prime p containing K. The finite
quotient isomorphism lifts p to q in Ahat. The local map A_p to Ahat_q is flat;
the target is regular from the formal chart hypothesis. Apply
lem-weil-pbc-flat-under-regular. These points and the complement cover the last level.
9. If X is reduced, its component generic local rings are fields. Inductively
each blowup level is reduced Noetherian by lem-per-reduced-noetherian-blowup-geometry,
and its component generics map to component generics of X. Indeed the effective
Cartier exceptional ideal is a unit at each field-valued generic stalk, by
thm-nagata-blowup-principalizes-center, so the generic lies in the complement
isomorphism of thm-nagata-global-blowup-complement. Centers supported over X_sing
miss these generic points; a closed subset missing every component generic is
nowhere dense. This proves the claim at every level, without normalization.
10. For Z empty supported ideals are unit ideals and completion is empty. For
I=0 the systems are constant and the correspondence is the identity. Nilpotent
I uses the same quotients. Empty centers and zero centers are retained; a zero
center gives an empty blowup by def-nagata-affine-blowup and def-nagata-affine-proj,
whereas a unit center gives the identity by lemma-nagata-affine-blowup-top.
Empty bases, subsequent empty levels and r=0 require no selected point or center.
-/
theorem supportedFormalBlowupAlgebraization
    (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]
    (toRat : X ⟶ Spec (.of (ULift.{u} ℚ)))
    (hQE : ∀ U : X.affineOpens, _root_.IsQuasiExcellent Γ(X, U.1))
    (I : X.IdealSheafData) (hI : RingedSpace.IsCoherent X.toRingedSpace I.toModules)
    (r : ℕ) :
    (∀ T : OrdinaryTower I r, ∃ F : FormalTower I r, Nonempty (Completion T F)) ∧
    (∀ F : FormalTower I r, ∃ T : OrdinaryTower I r, Nonempty (Completion T F)) ∧
    (∀ (T S : OrdinaryTower I r) (F : FormalTower I r),
      Nonempty (Completion T F) → Nonempty (Completion S F) →
        Nonempty (Unique (OrdinaryIso T S))) ∧
    (∀ (T : OrdinaryTower I r) (F G : FormalTower I r),
      Nonempty (Completion T F) → Nonempty (Completion T G) →
        Nonempty (Unique (FormalIso F G))) ∧
    ∀ (T : OrdinaryTower I r) (F : FormalTower I r) (c : Completion T F),
      c.CentersAgree ∧
        ((∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) → x ∈ I.support) →
          IsRegular (F.level (Fin.last r)) → F.HasSingularCenters →
            IsRegularScheme (T.level (Fin.last r)) ∧ T.HasSingularCenters ∧
              (AlgebraicGeometry.IsReduced X → T.HasNowhereDenseCenters)) := by
  sorry

end AlgebraicGeometry.AdicFormal
