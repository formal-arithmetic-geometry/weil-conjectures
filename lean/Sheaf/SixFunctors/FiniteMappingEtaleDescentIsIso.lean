/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.SixFunctors.FiniteMappingAdjunctionData
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.Paper.FiniteStageVerdierBiduality
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # FiniteMappingEtaleDescentIsIso

The descent step of the finite mapping-complex adjunction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  (c : Compactification (X ↘ Spec (.of D.k)))

/-- Every component of a transformation with the specified etale comparison square
is invertible. No transpose normalization is needed for this assertion.
Source: integral-dualizing proof, paragraph 2, and finite mapping node, steps 1--4.
(blueprint: lem-sf-finite-mapping-etale-descent-is-iso).

Proof: Choose an etale finite-Tor constructible origin of the given intrinsic object
using constructible origin and reflection of Tor amplitude, or the equivalence in
finite duality comparison. The etale global Hom comparison is invertible: biduality
puts the dualizing complex in the finite-Tor constructible class, duality preserves
that class, and global comparison is invertible on bounded-below complexes. The
site evaluation comparison and the dualizing-object comparison are invertible by
finite duality comparison. The dual compact-support comparison is an isomorphism
on this bounded-below origin. Its global comparison is invertible since ordinary
etale compact support preserves bounded-below complexes. Every factor of the etale
adjunction list is an isomorphism: Leray, internal exceptional adjunction, change of
compactification, and point internal-Hom comparison. The agreement equation therefore
forces the middle component to be an isomorphism by cancellation of its surrounding
isomorphisms. Finally naturality transports invertibility along the origin isomorphism
to the given intrinsic object. This also covers the zero object and the empty scheme. -/
theorem finiteMappingEtaleDescent_isIso (hl : l ≠ D.p)
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (τ : finiteMappingGlobalHom D l E n X c ⟶
      (finiteMappingCompactSections D l E n X c).op ⋙
        coefficientDerivedDual
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    (hτ : (∀ (J : Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X)
        (hJ : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X J),
        ∃ (hplus : DerivedCategory.TStructure.t.plus J)
          (hpro : finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) X
            ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u}
                (Padic.coefficientExtensionRing l E (n + 1)))) X).mapDerivedCategory.obj J)),
          FiniteMappingSameComposite
            (finiteMappingHomComparisonArrows
                (Padic.coefficientExtensionRing l E (n + 1)) c J ++
              [Arrow.mk (τ.app (op ⟨_, hpro⟩))] ++
                finiteMappingDualTransportArrows
                  (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
                  c ⟨J, hplus⟩)
            (finiteMappingEtaleGammaArrows
              (Padic.coefficientExtensionRing l E (n + 1)) D.k c J))) :
    ∀ M, IsIso (τ.app M) := by sorry

end WeilConjectures
