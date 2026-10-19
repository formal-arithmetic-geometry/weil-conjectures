/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.Paper.CondensedSurjectiveClosedEquivalence
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.Paper.CartesianCoefficients

/-!
# Common stratifications and restriction of coefficient modules

Source: Weil blueprint, sec-six-functors-basics/sk-lem-coefficient-heart/
sk-lem-coefficient-heart-common-stratification.md, clauses (1)--(3)
(blueprint: det-lem-coefficient-heart-common-stratification).

Refinement means containment of stratum images, with their given scheme structures.
No factorization through a stratum is inferred from containment of images.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Lisse means pro-etale locally free of finite rank, with ranks allowed to vary on the
cover. Source: blueprint sk-lem-coefficient-heart, introductory paragraph
(blueprint: det-lem-coefficient-heart-common-stratification). -/
def IsLisseCoefficientModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
    Mod.IsFree (condensedRingObj Λ (U.X i)) ((CondensedRing.upperStar Λ (U.f i)).obj M)

/-- The underlying ring object of a condensed ring, with its canonical multiplication.
Source: blueprint sk-def-sfb-condensed-ring, first paragraph
(blueprint: det-lem-coefficient-heart-common-stratification). -/
abbrev coefficientHeartRingObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ

/-- All three assertions, with exactness of a pair of arbitrary arrows expressed as equality
of its image and kernel subobjects. This also forces their composite to vanish. Longer
sequences are exact precisely when this condition holds at each term.
Source: blueprint sk-lem-coefficient-heart-common-stratification, clauses (1)--(3)
(blueprint: det-lem-coefficient-heart-common-stratification). -/
def CoefficientHeartStratificationAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  (∀ (n : ℕ) (P : Fin n → X.FiniteLocallyClosedStratification),
    ∃ R : X.FiniteLocallyClosedStratification,
      (∀ (j : Fin n) (a : Fin R.n), ∃ b : Fin (P j).n,
        R.stratum a ⊆ (P j).stratum b) ∧
      (∀ a : Fin R.n, ConnectedSpace (R.domain a)) ∧
      ∀ k : Fin (R.n + 1),
        IsOpen (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)) ∧
  ((∀ (S T : Scheme.{u}) (i : S ⟶ X), IsImmersion i →
      ∀ j : T ⟶ S, IsImmersion j →
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
        IsLisseCoefficientModule Λ M →
          IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ j).obj M)) ∧
    (∀ (P R : X.FiniteLocallyClosedStratification)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (∀ a : Fin P.n,
        HasFiniteConstantLocalModel Λ (P.domain a)
          ((CondensedRing.upperStar Λ (P.immersion a)).obj M)) →
      (∀ a : Fin R.n, ∃ b : Fin P.n, R.stratum a ⊆ P.stratum b) →
        ∀ a : Fin R.n,
          IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (R.immersion a)).obj M))) ∧
  (∀ R : X.FiniteLocallyClosedStratification,
    (∀ a : Fin R.n,
      PreservesFiniteLimits (CondensedRing.upperStar Λ (R.immersion a)) ∧
      PreservesFiniteColimits (CondensedRing.upperStar Λ (R.immersion a)) ∧
      Nonempty (CondensedRing.upperStar Λ (R.immersion a) ⋙
          Mod.forget (condensedRingObj Λ (R.domain a)) ≅
        Mod.forget (condensedRingObj Λ X) ⋙ upperStar Ab.{u + 1} (R.immersion a))) ∧
    (∀ (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : A ⟶ B),
      (Mono f ↔ ∀ a : Fin R.n, Mono ((CondensedRing.upperStar Λ (R.immersion a)).map f)) ∧
      (Epi f ↔ ∀ a : Fin R.n, Epi ((CondensedRing.upperStar Λ (R.immersion a)).map f))) ∧
    ∀ (A B C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : A ⟶ B) (g : B ⟶ C),
      imageSubobject f = kernelSubobject g ↔
        ∀ a : Fin R.n,
          imageSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map f) =
            kernelSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map g))

/-- Common refinement, lisse restriction, and detection of exactness on strata.
Source: blueprint sk-lem-coefficient-heart-common-stratification (1)--(3)
(blueprint: det-lem-coefficient-heart-common-stratification).

Proof plan (the seven steps of the DAG node):
1. Iterate lemma-constructible-common-refinement on the finite input family, starting
with X itself when the input is empty. Empty X also allows the empty stratification.
This only asserts containment of images, not scheme factorizations.
2. Express each resulting locally closed piece as F intersect O. Take the atoms of the
finite list of closed sets F and X minus O (def-weil-locally-closed-subset). Order their
membership subsets by increasing cardinality. Prefixes are downward closed; their
complements are finite unions of intersections of closed sets, hence prefixes are open
(Stacks 09Y3, finite closed-set construction).
3. Realize each atom by the reduced closed subscheme in the appropriate open part of
an original scheme stratum (lem-weil-pbc-reduced-induced-closed-subscheme). The immersion
definitions and lem-weil-pbc-proper-fp-permanence show its composite is an immersion.
4. Noetherian open subschemes and closed subsets have finitely many irreducible
components (lem-weil-pbc-noetherian-open-subscheme-noetherian and
lem-sc-noetherian-closed-subset-finite-components). The connected components are the
unions of components connected by the finite intersection graph. They are clopen in
the atom. Replace each ordered atom by these connected pieces; partial unions remain
open because their complements in the corresponding prefix are closed.
5. Base-change a pro-etale cover trivializing a lisse module
(def-weil-proetale-inverse-image). Cartesian coefficients give exact pullback preserving
finite free modules (sk-prop-sfb-cartesian-coefficients). A finite scalar presentation
over either field has a finite basis, so the scalar models of sk-def-sfb-constructible
are locally finite free.
6. For an arbitrary refined stratum T whose image lies in S, use W = T times_X S;
the projection W to T is a surjective immersion, hence closed
(lem-weil-pbc-immersion-base-change-lft and lem-weil-pbc-fibre-product-points).
Pullback to W is lisse by step 5. Lift its trivializing cover to T using
new-lem-weil-pbc-proetale-surjective-closed-cover-refinement. The base changes are still
surjective closed immersions (lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism).
Their coefficient pullbacks are equivalences
(new-lem-weil-pbc-condensed-surjective-closed-equivalence). Fullness and faithfulness
lift the finite-free trivializations and their inverses. Thus any given refined scheme
structure works, even when the original strata are nonreduced.
7. Exactness and the underlying inverse-image comparison come from cartesian
coefficients. Apply lem-weil-pbc-noetherian-stratum-detection to underlying abelian
sheaves. A kernel or cokernel vanishes iff every restriction vanishes, giving mono and
epi detection. For arbitrary f,g, first detect that the image of their composite is
zero. Then detect vanishing of ker(g)/im(f). This proves exactness iff every restriction
is exact; apply it at each term of a longer sequence. -/
theorem coefficientHeart_commonStratification (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (X : Scheme.{u}) [IsNoetherian X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ) :
    CoefficientHeartStratificationAssertions (coefficientHeartRingObj Λ) X := by
  sorry

end AlgebraicGeometry.ProEtale
