/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.SixFunctors.FiniteMappingAdjunctionData
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-! # FiniteMappingEtaleDescent

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

/-- The ordinary etale adjunction descends to a natural transformation on the intrinsic
finite-Tor constructible category, with its prescribed agreement on every etale input.
Source: integral-dualizing proof, paragraph 2, and finite mapping node, steps 2, 4 and 6.
(blueprint: lem-sf-finite-mapping-etale-descent).

Proof: Finite duality site comparison gives the equivalence from the etale finite-Tor
constructible category to the intrinsic pro-etale category. Its specified comparison
identifies internal Hom into the dualizing object. Transport its Nagata presentation
to c using compactification independence and uniqueness of the ordinary etale right
adjoint. On an etale input J, take the ordinary internal exceptional adjunction with
second argument the unit, then Leray and the evaluation-defined etale point duality.
Precompose with the inverse global Hom comparison and postcompose with the inverse
dual compact-support/global comparison. Bounded constructibility supplies J's lower
bound; Tor comparison shows its pullback is in the intrinsic finite-Tor domain.
All factors are natural, including compactification independence. Full faithfulness
of the origin equivalence descends this natural transformation. Changing an origin
uses its unique lifted isomorphism and naturality, so the component is independent
of that choice. Evaluating the descended transformation on any J gives the displayed
square, with exactly the listed comparison factors and no scalar choice. -/
theorem finiteMappingEtaleDescent (hl : l ≠ D.p)
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∃ τ : finiteMappingGlobalHom D l E n X c ⟶
      (finiteMappingCompactSections D l E n X c).op ⋙
        coefficientDerivedDual
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))),
      (∀ (J : Etale.DerivedCategoryModule
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
              (Padic.coefficientExtensionRing l E (n + 1)) D.k c J)) := by sorry

end WeilConjectures
