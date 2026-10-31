/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteMappingAdjunctionData
import WeilConjectures.SmoothPurity.InternalAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.BoundedSiteAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
import WeilConjectures.SixFunctors.CtfStabilityDirectImages

/-! # FiniteMappingEtaleDescentTranspose

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

/-- The etale comparison square fixes the normalized transpose of the descended map.
This assertion concerns a natural transformation and does not assume it invertible.
Source: integral-dualizing proof, paragraph 2, and finite mapping node, step 5.
(blueprint: lem-sf-finite-mapping-etale-descent-transpose).

Proof: The ordinary etale exceptional right adjoint takes the comparison direct image
of the point unit to a bounded-below object, by the bounded-site adjunction theorem.
This supplies homega for the fixed compactification c. At the separably closed point,
etale sections are the inverse of constant sheaf, and the comparison derived unit is
invertible. Their canonical Leray identification shows that the derived constant/Gamma
unit on the coefficient unit is invertible. Compose it with the five displayed
constant-unit identifications to obtain scalar, with the required composite equation.
For an etale finite-Tor origin J, uncurry its comparison square. The internal adjunction
evaluation theorem identifies the etale transpose with projection, evaluation and
the etale exceptional counit. Projection comparison on etale origins and bounded-site
adjunction transpose transport this to c's pro-etale projection and exceptional counit.
The finite duality comparison preserves evaluation. The point internal-Hom comparison
is evaluation-defined, so global tensor and Leray comparisons yield precisely the
listed pairing, ending in scalar inverse; the unit normalization cancels the scalar
with no remaining automorphism. Every constituent is natural. Choose an etale origin
of an arbitrary intrinsic object, use naturality of the transformation and pairing,
and conjugate by the origin isomorphism. Thus the equation holds for every object,
independently of its chosen etale representative, including zero and empty cases. -/
theorem finiteMappingEtaleDescent_transpose (hl : l ≠ D.p)
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
      ∃ (homega : DerivedCategory.TStructure.t.plus
          (finiteMappingCounitInput (Padic.coefficientExtensionRing l E (n + 1)) c))
        (scalar :
          𝟙_ (DerivedCategory (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ≅
          (ProEtale.rightDerivedGlobalSections
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
            (Spec (.of D.k))).obj (𝟙_ _)),
        FiniteMappingComposite
          (finiteMappingScalarUnitArrows
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
            (Spec (.of D.k))) (Arrow.mk scalar.hom) ∧
        ∀ M : (finiteTorConstructibleProEtaleModule
            l E (n + 1) (Nat.succ_pos n) X).FullSubcategory,
          FiniteMappingSameComposite
            (finiteMappingTransposeArrows
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
              (τ.app (op M)))
            (finiteMappingPairing (Padic.coefficientExtensionRing l E (n + 1))
              c homega scalar M.obj) := by sorry

end WeilConjectures
