/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.ModuleProjectionSectionInverse
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.RingedProjectionTensorComposition
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Projection normalization for a proper retraction and its closed section

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md, clause (1), diagonal
projection identification and cancellations on p_i Delta = id
(blueprint: lem-sfb-projection-section-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale

namespace ProjectionSection

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Both normalized equalities, with the inverse equality conditional on invertibility.
Source: blueprint clause (1), the two displayed normalization identities
(blueprint: lem-sfb-projection-section-normalization). -/
def Normalized {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) : Prop :=
  forward Λ r i h M = 𝟙 M ∧
    ∀ [IsIso (projection Λ r M
      ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))]
      [IsIso (sectionArrow Λ r i h M)], backward Λ r i h M = 𝟙 M


end ProjectionSection

/-- Projection normalization for a proper retraction and a closed section, on the
localizing closure of bounded constructible O_E-complexes. Source: blueprint
sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md, clause (1)
(blueprint: lem-sfb-projection-section-normalization).

Proof: transport the internal-module derived categories, K-flat relative tensors and
units to the section-ring sheaf categories by lem-pd-module-ringed-topos-derived-comparison.
That comparison identifies the actual derived pullback, pushforward, adjunction,
counit and tensor map, hence also their projection mates. The canonical direct-image
comparison of lem-weil-pbc-ringed-topoi-derived-pushforward-composition is the mate of
pullback composition, so agrees with pushforwardSection. Apply the final section clause
of lem-sfb-ringed-projection-tensor-composition with p = r, i the section and V = R_X.
Its symmetry convention gives exactly the two projections in forward. Under
pullbackSection and the right unitor the second projection is sectionArrow. Conjugating
the resulting identity of M tensor R_X by the right unitor gives the first equality.
When both displayed projections are inverted, invert this identity; functoriality
of Rr_* identifies the inverted middle factor with Rr_*(a_M inverse). This is backward.
-/
theorem projection_section_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    (X V : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (r : V ⟶ X) (i : X ⟶ V) [IsProper r.left] [IsClosedImmersion i.left]
    (h : i.left ≫ r.left = 𝟙 X.left)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)))
    (_hM : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X.left) M) :
    ProjectionSection.Normalized (Profinite.padicIntegersRingObj ℓ E.1) r.left i.left h M := by
  sorry

end AlgebraicGeometry.ProEtale
