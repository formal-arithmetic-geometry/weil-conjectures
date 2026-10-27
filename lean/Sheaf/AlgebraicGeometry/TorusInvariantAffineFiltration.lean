/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-! # Invariant affine filtrations for split torus actions

Source: agent-formulated concentration prerequisite to Milne, Algebraic Groups (2017),
Section 22d, Theorem 22.50, p.480; the geometric input is Sumihiro (1974), Corollary 2,
followed by reduction and Noetherian induction. The latter source is marked WANTED
in the DAG; this result is not asserted to be stated in Milne.
(blueprint: lem-sfb-torus-invariant-affine-filtration).

Actions and equivariant arrows are Mathlib's internal module objects in schemes over
Spec F. The reduction is characterized by its reduced closed immersion and its ideal,
the vanishing ideal of the entire space, which is the sheaf of nilpotent sections.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An invariant open in a separated finite-type scheme with a split torus action
has a finite invariant reduced closed filtration of its reduction with affine strata.

Source: the agent-formulated concentration prerequisite to Milne (2017), Section 22d,
Theorem 22.50, p.480; Sumihiro (1974), Corollary 2 (WANTED), and Noetherian induction
(blueprint: lem-sfb-torus-invariant-affine-filtration).

Proof, following the accepted eight-step DAG split:
1. Finite type over a field makes Y Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Its open V is quasi-compact
   (lem-sfb-noetherian-open-immersion-qc), hence finite type
   (lem-weil-pbc-qc-open-immersion-finite-type, lem-sfb-finite-type-composition-base-change).
   Its diagonal is closed by lem-weil-pbc-closed-immersion-base-change. Reduction and
   locally closed permanence use lem-weil-pbc-reduced-induced-closed-subscheme and
   lem-dl-a1-locally-closed-stratum-separated-finite-type.
2. T times a reduced scheme is reduced (lem-trf-split-lattice-torus-projection).
   Factor the action through the reduction using
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme. Cancel its closed
   immersion to obtain the action identities and equivariance.
3. Induct on closed supports by lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.
   The empty scheme has a length-zero chain. Each reduced closed term remains separated
   and finite type by lem-dl-a1-locally-closed-stratum-separated-finite-type.
4. The algebraically closed field is perfect. Apply lem-kun-geometric-reduced-perfect
   and lem-pur-geometrically-reduced-dense-smooth-open to obtain a dense smooth open W.
   Source locality (lem-weil-pbc-smooth-local-on-source),
   lem-weil-pbc-smooth-scheme-over-field-regular and rem-pc-regular-normal make W normal.
5. The shear (t,c) maps to (t,t.c), with inverse (t,c) maps to (t,t.inverse.c).
   Torus smoothness and lem-pc-smooth-flat, together with
   lem-sfb-scheme-lfp-smooth-flat-base-change and
   lem-weil-pbc-smooth-restrict-open-subschemes, identify the inverse images of W under
   action and projection. Restrict via lem-weil-pbc-morphism-factors-through-open-subscheme;
   cancel by lem-weil-pbc-open-immersion-monomorphism. Thus W is invariant.
6. For nonempty W, lem-sfb-sumihiro-normal-torus-affine-neighbourhood gives a nonempty
   invariant affine open A. The shear shows equality of its two inverse images.
7. Give the complement D its reduced induced structure
   (lem-weil-pbc-reduced-induced-closed-subscheme). The torus product is reduced;
   lem-weil-pbc-closed-immersion-base-change and lem-weil-pbc-fibre-product-points
   identify its support. Factor the action using
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme and cancel to check laws.
   Compose closed inclusions by lem-weil-pbc-closed-immersion-products.
8. Apply induction to D and prepend the current scheme, with first stratum A.
   All strata and closed terms are separated and finite type by
   lem-dl-a1-locally-closed-stratum-separated-finite-type; all arrows are equivariant.
   The empty case permits N = 0. No normality or characteristic restriction is needed. -/
theorem exists_torus_invariant_affine_filtration
    (F : Type u) [Field F] [IsAlgClosed F] (r : ℕ)
    (T : Grp (Over (Spec (.of F))))
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Y V : CategoryTheory.Mod (Over (Spec (.of F))) T.X)
    [IsSeparated Y.X.hom] [LocallyOfFiniteType Y.X.hom] [QuasiCompact Y.X.hom]
    (j : V ⟶ Y) [IsOpenImmersion j.hom.left] :
    IsSeparated V.X.hom ∧ LocallyOfFiniteType V.X.hom ∧ QuasiCompact V.X.hom ∧
    ∃ (R : CategoryTheory.Mod (Over (Spec (.of F))) T.X) (i : R ⟶ V),
      IsReduced R.X.left ∧ IsClosedImmersion i.hom.left ∧
      i.hom.left.ker = Scheme.IdealSheafData.vanishingIdeal ⊤ ∧
      Set.range i.hom.left = Set.univ ∧
      ∃ (N : ℕ) (Z : Fin (N + 1) → CategoryTheory.Mod (Over (Spec (.of F))) T.X)
        (inclusion : ∀ a : Fin N, Z a.succ ⟶ Z a.castSucc)
        (S : Fin N → CategoryTheory.Mod (Over (Spec (.of F))) T.X)
        (stratum : ∀ a : Fin N, S a ⟶ Z a.castSucc),
        Z 0 = R ∧ IsEmpty (Z (Fin.last N)).X.left ∧
        (∀ a, IsReduced (Z a).X.left ∧ IsSeparated (Z a).X.hom ∧
          LocallyOfFiniteType (Z a).X.hom ∧ QuasiCompact (Z a).X.hom) ∧
        (∀ a, IsClosedImmersion (inclusion a).hom.left) ∧
        (∀ a, IsOpenImmersion (stratum a).hom.left ∧
          Set.range (stratum a).hom.left = (Set.range (inclusion a).hom.left)ᶜ ∧
          IsAffine (S a).X.left ∧ IsSeparated (S a).X.hom ∧
          LocallyOfFiniteType (S a).X.hom ∧ QuasiCompact (S a).X.hom) := by
  sorry

end AlgebraicGeometry
