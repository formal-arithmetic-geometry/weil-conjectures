module

public import Sheaf.AlgebraicGeometry.NormalizedTowerRecoveryTests
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationCompletionNoetherian

/-! # Recovery of normalized towers by restriction and flat tests

Source: ILO, Travaux de Gabber, VIII 2.1.18--2.1.20 and 2.2.11--2.2.12,
printed pp.89--91, and proof of 3.4.15, printed p.114.
(blueprint: lem-per-normalized-tower-support-recovery).

Equality is expressed by the existing center-preserving stage isomorphisms, over the
specified base. The comparison includes the equality of original lengths.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Monoscheme.NormalizedTower

/-- Restriction along the flat monomorphism is an uncontracted scheme pullback, and
schematic closure recovers each ideal center on its original stage. `IdealSheafData.map`
is the kernel of O -> pushforward of the restricted closed center's structure sheaf.

Source: ILO VIII 2.1.18--2.1.20 and 2.2.12
(blueprint: lem-per-normalized-tower-support-recovery).

Proof (node steps 1--3): base change preserves flatness, quasi-compactness and the
monomorphism. The local-structure lemma makes each local ring map an isomorphism and
the morphism regular. The regular-pullback lemma gives the cartesian normalized tower,
with no index removed. On principal affine opens of a finite Noetherian affine cover,
use lem-sfb-affine-associated-points-primes to identify associated points of the center.
Every such point lifts to the restriction. A section in the displayed kernel vanishes
in every localization of A/I at an associated prime. The injection of a finite module
into these localizations (lem-weil-pbc-module-injects-localizations-associated-primes)
puts the section in I. The reverse inclusion is immediate. Equality on this basis
gives the ideal-sheaf equality. Induction reconstructs each next normalized blowup
from that same ideal. Unit centers and length zero are retained. -/
theorem normalizedTower_support_recovery {n : ℕ} (T : NormalizedTower.{u} n)
    (hNoeth : ∀ i, IsNoetherian (T.level i)) {U : Scheme.{u}}
    (j : U ⟶ T.level 0) [Flat j] [Mono j] [QuasiCompact j]
    (hAss : T.associatedCenterImages ⊆ Set.range j) :
    Nonempty (PullbackOver T (𝟙 _) j) ∧
      ∀ i : Fin n,
        ((T.center i).comap (pullback.fst (T.toFirst i.castSucc) j)).map
          (pullback.fst (T.toFirst i.castSucc) j) = T.center i := by
  sorry

/-- Equal uncontracted restrictions recover the original lengths and ordered centers.
Both associated-point sets must lie in the image of the same flat monomorphism.

Source: ILO VIII 2.2.12 (blueprint: lem-per-normalized-tower-support-recovery).

Proof (node steps 2--3): the restricted comparison already includes equality of
lengths. Reconstruct the first ideal on X by schematic closure, using the preceding
kernel calculation for both towers. Their normalized blowups are then canonically
identified over X. Repeat on successive stages. The resulting center-preserving
isomorphism retains every original stage; no unit-center isomorphism is deleted. -/
theorem normalizedTower_restriction_injective {n m : ℕ}
    (T : NormalizedTower.{u} n) (S : NormalizedTower.{u} m)
    (hT : ∀ i, IsNoetherian (T.level i)) (hS : ∀ i, IsNoetherian (S.level i))
    (e : S.level 0 ≅ T.level 0) {U : Scheme.{u}}
    (j : U ⟶ T.level 0) [Flat j] [Mono j] [QuasiCompact j]
    (hAssT : T.associatedCenterImages ⊆ Set.range j)
    (hAssS : e.hom '' S.associatedCenterImages ⊆ Set.range j)
    (PT : PullbackOver T (𝟙 _) j) (PS : PullbackOver S e.hom j) :
    SameOver PT.tower PS.tower PT.baseIso.hom PS.baseIso.hom →
      SameOver T S (𝟙 _) e.hom := by
  sorry

/-- The rational localization is a quasi-compact flat monomorphism, and the same
schematic-closure formula applies under the associated-point hypothesis. It is not
assumed open, and no characteristic restriction is imposed on X.

Source: ILO VIII proof of 3.4.15, p.114
(blueprint: lem-per-normalized-tower-support-recovery).

Proof (node step 4): on Spec A this is Spec(S^{-1}A), for S the image of the
nonzero integers. Localization is flat. Multiplication S^{-1}A tensor_A S^{-1}A ->
S^{-1}A is an isomorphism, so its spectrum is a monomorphism. It is affine, hence
quasi-compact. Apply normalizedTower_support_recovery, without any openness premise. -/
theorem normalizedTower_rational_recovery {n : ℕ} (T : NormalizedTower.{u} n)
    (hNoeth : ∀ i, IsNoetherian (T.level i)) :
    Flat (Scheme.towerTestRationalMap (T.level 0)) ∧
      Mono (Scheme.towerTestRationalMap (T.level 0)) ∧
      QuasiCompact (Scheme.towerTestRationalMap (T.level 0)) ∧
      (T.associatedCenterImages ⊆ Set.range (Scheme.towerTestRationalMap (T.level 0)) →
        Nonempty (PullbackOver T (𝟙 _) (Scheme.towerTestRationalMap (T.level 0))) ∧
          ∀ i : Fin n,
            ((T.center i).comap (pullback.fst (T.toFirst i.castSucc)
              (Scheme.towerTestRationalMap (T.level 0)))).map
                (pullback.fst (T.toFirst i.castSucc)
                  (Scheme.towerTestRationalMap (T.level 0))) = T.center i) := by
  sorry

/-- An fpqc test compares the actual centers and the same finite stage indices,
provided the two specified scheme-theoretic uncontracted pullbacks exist.

Source: ILO VIII 2.2.11 (blueprint: lem-per-normalized-tower-support-recovery).

Proof (node step 5): every base-changed stage is flat and surjective. Surjectivity
follows by taking a lift of the base point and using the nonempty spectrum of the
faithfully flat residue-field base change. At a lifted point the flat local stalk
map is faithfully flat. Contract equal extended ideals by
lem-weil-pbc-faithfully-flat-ideal-contraction; equality of all stalk ideals gives
equality of ideal sheaves. Induct on the original stage indices and construct the
next normalized blowup from the common ideal. Equality of the pulled uncontracted
towers supplies the length equality, including when X is empty. Conversely a
center-preserving tower comparison pulls back along the given cartesian squares. -/
theorem normalizedTower_fpqc_test {n m : ℕ}
    (T : NormalizedTower.{u} n) (S : NormalizedTower.{u} m)
    (hT : ∀ i, IsNoetherian (T.level i)) (hS : ∀ i, IsNoetherian (S.level i))
    (e : S.level 0 ≅ T.level 0) {Y : Scheme.{u}}
    (f : Y ⟶ T.level 0) [Flat f] [QuasiCompact f] [Surjective f]
    (PT : PullbackOver T (𝟙 _) f) (PS : PullbackOver S e.hom f) :
    SameOver PT.tower PS.tower PT.baseIso.hom PS.baseIso.hom ↔
      SameOver T S (𝟙 _) e.hom := by
  sorry

/-- The completion is at the maximal ideal of the recorded strict local ring. The
canonical local map from O_{X,x} to its completion is faithfully flat; its spectrum
is characterized over X, so an arbitrary ring map cannot serve as this test.

Source: ILO VIII proof of 3.4.15, p.114; Stacks Tags 04HX, 07QM and 06LJ
(blueprint: lem-per-normalized-tower-support-recovery).

Proof (node steps 6--7): choose a Noetherian affine chart at x. The affine strict
local comparison identifies the recorded colimit with the strict henselization of
O_{X,x}, preserving its structural map and residue embedding. Its maximal ideal
is the kernel of the canonical geometric evaluation. The pair and triple colimit
index categories agree by sending a residue map to its kernel prime and residue
embedding. Strict henselization is a faithfully flat local extension; its completion
is a faithfully flat local extension by the Noetherian strict-henselization completion
lemma. Their composite is faithfully flat and local. The structural-map equation
and the monomorphism Spec O_{X,x} -> X uniquely specify the composite. -/
theorem normalizedTower_completedStrict_local {X : Scheme.{u}} [IsNoetherian X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    (∃ h : IsLocalRing (Scheme.strictHenselizationRing s),
      @IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s) _ h =
        RingHom.ker (Scheme.strictHenselizationPointEvaluation s)) ∧
      IsLocalRing (Scheme.towerTestCompletedStrictRing s) ∧
      ∃! φ : X.presheaf.stalk (s (IsLocalRing.closedPoint Ω)) →+*
          Scheme.towerTestCompletedStrictRing s,
        Spec.map (CommRingCat.ofHom φ) ≫
            X.fromSpecStalk (s (IsLocalRing.closedPoint Ω)) =
          Scheme.towerTestCompletedStrictMap s ∧ IsLocalHom φ ∧ φ.FaithfullyFlat := by
  sorry

/-- Completed strict local tests are jointly conservative for uncontracted towers.
When X is empty, the displayed extra length premise supplies precisely the datum
lost by the empty test family. When X is nonempty, any geometric point supplies it.

Source: ILO VIII proof of 3.4.15, p.114
(blueprint: lem-per-normalized-tower-support-recovery).

Proof (node step 7): faithfully flat residue-field base change makes the completed
strict local family jointly surjective on every stage. Each stage map is flat.
Contract the extended stalk ideals as in step 5 and induct without deleting a stage.
On a nonempty base choose a geometric point; equality of its uncontracted towers
implies n=m. On the empty base the family is empty, and the separately supplied
length equality is necessary and sufficient since there is only one ideal per
empty stage. The converse pulls the global comparison back to every test. -/
theorem normalizedTower_completedStrict_test {n m : ℕ}
    (T : NormalizedTower.{u} n) (S : NormalizedTower.{u} m)
    (hT : ∀ i, IsNoetherian (T.level i)) (hS : ∀ i, IsNoetherian (S.level i))
    (e : S.level 0 ≅ T.level 0)
    (PT : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ T.level 0),
      PullbackOver T (𝟙 _) (Scheme.towerTestCompletedStrictMap s))
    (PS : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ T.level 0),
      PullbackOver S e.hom (Scheme.towerTestCompletedStrictMap s)) :
    ((IsEmpty (T.level 0) → n = m) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T.level 0),
        SameOver (PT Ω s).tower (PS Ω s).tower (PT Ω s).baseIso.hom
          (PS Ω s).baseIso.hom) ↔ SameOver T S (𝟙 _) e.hom := by
  sorry

/-- A point of an actual ideal center over x gives a point after passage to the
completed strict local scheme at any geometric point over x.

Source: ILO VIII proof of 3.4.15, p.114
(blueprint: lem-per-normalized-tower-support-recovery).

Proof (node step 7): the canonical local map at x is faithfully flat. Its base
change to the residue field of the chosen point of the center is faithfully flat,
so its spectrum is nonempty by faithfully-flat surjectivity on spectra. This
spectrum maps to the scheme-theoretic pullback of the center. No normalized
tower base-change assertion is needed for this nonemptiness clause. -/
theorem normalizedTower_center_completedStrict_nonempty {n : ℕ}
    (T : NormalizedTower.{u} n) (hNoeth : ∀ i, IsNoetherian (T.level i))
    (i : Fin n) (z : (T.center i).subscheme)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T.level 0)
    (hz : T.toFirst i.castSucc ((T.center i).subschemeι z) =
      s (IsLocalRing.closedPoint Ω)) :
    Nonempty (pullback (C := Scheme.{u}) ((T.center i).subschemeι ≫ T.toFirst i.castSucc)
      (Scheme.towerTestCompletedStrictMap s)) := by
  sorry

end AlgebraicGeometry.Monoscheme.NormalizedTower
