/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y7
-/
module

public import Sheaf.Paper.DifferenceFirstInputRestriction

/-! # Composition of the normalized etale dualizing comparison

Source: composition coherence Step 1, output comparison
(blueprint: lem-pur-normalized-etale-comparison-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
open FiniteEtaleNormalization

/-- The normalized comparison composes with both canonical congruences retained.
Source: composition coherence Step 1, output calculation, refinement Step 6
(blueprint: lem-pur-normalized-etale-comparison-composition).

Proof: first eliminate the equalities F=vw and b=Fh. Expand normalizedE as the
exceptional congruence followed by E. The reflexive congruence is identity, since
the compact-support congruence is identity and conjugacy preserves identities.
Expand E as the exceptional compositor at the unit followed by rho. Associativity
of compact-support composition, transferred by adjunction conjugacy, identifies
the two exceptional compositors. The composition law for rho identifies rho_vw
with rho_v followed by v-pullback of rho_w and the inverse pullback compositor.
Naturality of rho_v moves the w-exceptional compositor past it. These equalities
yield the displayed formula with precisely the specified congruence. Equivalently,
specialize the CompositeEEquation clause of the Cartesian-tower comparison to
q=id, q_Q=id, G=J=w, H=v and p=h, then transport the identity composites using
their canonical congruences. All comparisons preserve counits; no orientation or
choice of trivialization enters. This calculation does not require affine charts,
diagonals, sections, or the two input equations. -/
theorem normalizedE_comp_congr (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z B : Scheme.{u}} (v : X ⟶ Y) (w : Y ⟶ Z) (h : Z ⟶ B)
    (F : X ⟶ Z) (b : X ⟶ B)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [Etale w] [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    [Etale F] [IsSeparated F] [LocallyOfFiniteType F] [QuasiCompact F]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [HasCompactification h] [HasCompactification (w ≫ h)] [HasCompactification b]
    (r : ℕ) [SmoothOfRelativeDimension r h]
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (hF : v ≫ w = F) (hb : F ≫ h = b) :
    (normalizedE P F h b hb.symm aB).hom =
      (normalizedE P v (w ≫ h) b
        (hb.symm.trans ((congrArg (fun z ↦ z ≫ h) hF.symm).trans
          (Category.assoc v w h))) aB).hom ≫
      (pull P v).map (normalizedE P w h (w ≫ h) rfl aB).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        v w F hF.symm).inv.app _ := by sorry

end AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
