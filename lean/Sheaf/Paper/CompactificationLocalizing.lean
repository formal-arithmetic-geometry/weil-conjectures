/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Sheaf.Paper.OpenImmersionLocalizing
import Sheaf.SixFunctors.ProperImageLocalizingProper

/-!
# Compact support along a single compactification on the localizing category

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-single and its three-paragraph proof
(blueprint: det-sf-comp-coherence-single).

Restriction to the full localizing subcategories is expressed using their object predicates.
Exactness means preservation of their ambient distinguished triangles, with the canonical
composite shift comparison. Coproduct preservation means preservation of each ambient discrete
colimit whose vertices belong to the source closure, using the same indexing universe as
`localizingClosureProEtale`. These are precisely the triangles and sums of the full closures.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For each specified compactification, `Rp_*` after exact extension by zero restricts
exactly to the localizing closures, preserves their direct sums, and preserves Dctf.
The four conjuncts express restriction, exactness, sums, and preservation of Dctf.
All categories are the ordinary unbounded derived categories of internal module objects.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-single, statement and proof
(blueprint: det-sf-comp-coherence-single).

Proof plan:
1. Apply det-proper-image-localizing-open to the quasi-compact open immersion c.i.
Extension by zero preserves Dctf, all direct sums, and distinguished triangles; its
restriction maps the source localizing closure into the middle localizing closure.
2. Apply det-proper-image-localizing-proper to the proper map c.g. Its coefficient
clauses supply preservation of Dctf and direct sums on the middle localizing closure
for finite rings, integral coefficients, finite extension fields, and the condensed
algebraic closure. The Z_ell and Q_ell cases are the integral and field cases with
E = Q_ell. Thus its restriction is exact and preserves these sums.
3. Compose the two restricted functors. The middle closure is the same in both steps.
Each distinguished triangle is sent to a distinguished triangle twice, with the
composite shift comparison. The two coproduct comparisons compose to the comparison
for Rp_* j_!. A Dctf object first stays Dctf under j_! and then under Rp_*.
These arguments include the empty family and the zero complex. -/
theorem compactification_localizing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    (∀ K : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      localizingClosureProEtale Λ X K →
        localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) ∧
    (∀ T : Pretriangulated.Triangle (DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      T ∈ distTriang _ → localizingClosureProEtale Λ X T.obj₁ →
        localizingClosureProEtale Λ X T.obj₂ → localizingClosureProEtale Λ X T.obj₃ →
        (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).mapTriangle.obj T ∈
          distTriang _) ∧
    (∀ (I : Type (u + 2)) (K : Discrete I ⥤ DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      (∀ i : I, localizingClosureProEtale Λ X (K.obj (Discrete.mk i))) →
        PreservesColimit K (rightDerivedLowerShriekOfCompactification Λ c.obj.obj)) ∧
    (∀ K : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (constantModelBoundedConstructible Λ X K ∧ DerivedCategory.finiteTorAmplitude _ K) →
        constantModelBoundedConstructible Λ Y
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K) ∧
          DerivedCategory.finiteTorAmplitude _
            ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
