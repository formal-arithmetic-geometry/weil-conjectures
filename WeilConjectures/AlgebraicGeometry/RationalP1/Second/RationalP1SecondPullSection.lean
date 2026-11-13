/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectivePullSectionCompatibility
import WeilConjectures.AlgebraicGeometry.RationalP1.PullSectionTransport
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullSectionTransportData
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparisonExpansion
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullSectionCoreComm

/-! # The second pullback comparison restricted to the diagonal -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist firstProjection secondProjection
attribute [local irreducible] square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] projectionMap singleUnitIso secondLineComparison

/-- The ambient pullback comparison restricts to the identity on the diagonal for the
untwisted base object. This is the composition-coherence part of the second pull-section
argument; the Tate-line and tensor transport are handled by `second_pull_section`.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, first factor before the Tate twist.
(blueprint: lem-sfb-rational-p1-second-pull-section-core).
Proof: expand the ambient square comparison into the normalized inverse-image
compositors. Both composites with the diagonal are the identity because
`diagonalImmersion Y ≫ firstProjection Y` and `diagonalImmersion Y ≫ secondProjection Y`
are the identity; the pullback-composition coherence and identity compositor then give
the displayed equality. -/
theorem second_pull_section_core
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    PullSectionCompatibility
      (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
      (moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
      (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)
      ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K).inv := by
  exact ⟨second_pull_section_core_comm l c k p hpl Y K⟩

-- The statement compares the fixed derived pullback and tensor interfaces.
/-- The two canonical pullback identifications agree after restriction to the diagonal.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, cancellation on the diagonal.
(blueprint: lem-sfb-rational-p1-second-pull-section).

Proof: expand into the two pullTwistIso maps and the square
comparison on q*K. Pullback composition coherence, applied to Delta p1 = id and
Delta p2 = id, identifies the restriction of the square comparison with identity
on q*K. On each finite root sheaf the Cartesian comparison commutes with restriction
to Delta. The same equation passes to the inverse limit, extension to the finite
coefficient ring, and inversion of l; in the closure case it is checked on every
finite-subextension coprojection. Hence both restrictions give the same identity
pullback comparison on the Tate line. For the tensor factor use the unrestricted
delta_comparison and composition_comparison clauses of ModuleRingedComparison,
not its theorem restricted to finite-type schemes over fields. On K-flat terms,
the pullback tensor comparison sends a pure tensor to the tensor of its pullbacks;
this commutes with the preceding composition comparison, and descends to the
unbounded derived category. Shift coherence gives the same equation on
M=q*K(1)[2]. Compose with the inverse comparison
to give the displayed equation. This uses no tensor projection, diagonal class,
supported-source normalization, or trace. The same coherence equations hold for
K=0 and for empty schemes. -/
theorem second_pull_section
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    PullSectionCompatibility
      (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
      (moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
      (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      ((twist (coefficient l c).X (ProjectiveLine Y)
        (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      (secondPullComparison l c k p hpl Y K).inv := by
  let : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (secondProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  obtain ⟨data, _⟩ := second_pull_section_transport_data l c k p hpl Y K
  refine ⟨?_⟩
  rw [second_pull_comparison_inv_map_expansion l c k p hpl Y K]
  exact pull_section_transport _ _ _ _ _ _ data
    (second_pull_section_core l c k p hpl Y K).comm

end AlgebraicGeometry.ProEtale.RationalP1
