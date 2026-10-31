/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientAction
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.ZetaSeries

/-! # Finite data for smooth purity over algebraically closed coefficients

This module isolates the finite-stage adjunction package needed by the common-stage
smooth-purity theorem.  It deliberately stops before descending the package to the
common-stage category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The coefficient prime is invertible on every residue field by transport from D.k.
Source: the global coefficient hypotheses of smooth purity
(blueprint: d4-sp-qbar-finite-package). -/
@[instance_reducible] def qbarResidueInvertible (T : Scheme.{u})
    [T.Over (Spec (.of D.k))] :
    ∀ x : T, Invertible (l : T.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D l hl).map
      ((T ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
      IsUnit (l : T.residueField x)).invertible

/-- Intrinsic pullback followed by the signed Tate twist and cohomological shift.
Source: the displayed right functor of smooth purity
(blueprint: d4-sp-qbar-finite-package). -/
def qbarPurityRightFunctor
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    (f : X ⟶ Y) (d : ℕ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  letI := qbarResidueInvertible D l hl X
  letI := qbarResidueInvertible D l hl Y
  commonStageDerivedPullback l Ω f ⋙ intrinsicQbarComplexTwistFunctor D l hl X Ω
    (d : ℤ) ⋙ shiftFunctor (generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (2 * (d : ℤ))

/-- Finite adjunctions and their coefficient-compatibility equations, before descent.
Source: finite adjunction and coefficient-compatibility steps of smooth purity
(blueprint: d4-sp-qbar-finite-package). -/
structure SmoothPurityQbarFinitePackage
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) where
  action : SfCompactSupportCoefficientAction l D.k
    (finiteFieldDatumPrimeUnit D l hl) Ω c
  right : (stageSystem l Ω Y).Morphism (stageSystem l Ω X)
  stageAdjunction : ∀ E, action.system.Φ E ⊣ right.Φ E
  counit_compatible : ∀ (E L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : E ≤ L) (K : Stage l Ω Y E),
    (action.system.β h).hom.app ((right.Φ E).obj K) ≫
      (action.system.Φ L).map ((right.β h).hom.app K) ≫
      (stageAdjunction L).counit.app (((stageSystem l Ω Y).T h).obj K) =
        ((stageSystem l Ω Y).T h).map ((stageAdjunction E).counit.app K)

/-- Finite smooth-purity data with the normalized compact-support action.
Source: `sk-thm-sp-qbar`, finite adjunction and coefficient extension paragraphs;
`det-sp-integral-adjunction-bijection`, `det-sp-rational-localized-hom`, and
`det-sp-field-extension-towers` (blueprint: d4-sp-qbar-finite-package).

Proof: first obtain the normalized action S from finite-field independence. Its
finite_eq identifies each left functor with the specified finite compact-support
functor. For every coefficient field, form the integral right adjoint by the derived
limit of the finite exceptional tower. The integral adjunction restricts to bounded
constructible objects. Localize its linear Hom bijection at the uniformizer to obtain
the finite rational adjunction via the actual native condensed Hom comparisons of
prop-pur-condensed-rational-adjunction. Transport this adjunction through the
coefficient-presentation comparisons, including their specified left functor maps.
Use only the integral clauses (1)--(2) of det-sp-field-extension-towers, localized
through those same native comparisons; its raw rational clause is not used.
Use the coefficient-extension comparisons for these
right adjoints as the beta maps of the right stage morphism. The coefficient tower
cocycle is exactly its coherence field. The normalized left coefficient comparisons
are the tensor-unit mates, so the unit and counit equations of field extension give
the displayed finite coefficient equation for the counits. These data
form the package; deriving unit compatibility and constructing the corresponding
stage-system Hom families is left to its consumer. This proves finite data only and makes
no assertion about which explicit common-stage functor the right morphism induces.
-/
theorem smoothPurityQbarFinitePackage_exists
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f) :
    Nonempty (SmoothPurityQbarFinitePackage D l hl Ω f c) := by
  sorry

end WeilConjectures
