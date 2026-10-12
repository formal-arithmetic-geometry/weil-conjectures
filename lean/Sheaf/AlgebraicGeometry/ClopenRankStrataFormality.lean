/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex
import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Formality of modules on disjoint clopen rank strata

Source: Stacks Tag 0BQZ, single-degree truncation, and Tag 0AVW,
modules over the direct-image algebra.
-/

@[expose] public section

universe u wA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- Arbitrary module sheaves on finitely many clopen rank strata can be
reconstructed from their cohomology in the assigned degrees. The family E
is arbitrary; no exterior-power or derived-direct-image computation occurs
in this assertion.

Source: Stacks Tags 0BQZ and 0AVW; reconstruction proof steps 2--4.
(blueprint: lem-sc-clopen-rank-strata-formality)

Proof: The clopen fibers of r partition Z. Glue 1 on each fiber and 0 on
its complement to obtain global sections e_n of O_Z. Their images in
 i_*O_Z are orthogonal idempotents with sum 1; only finitely many fibers
are nonempty. Multiplication by e_n splits each complex of algebra-module
sheaves into image subcomplexes. Differentials commute with scalar
multiplication, and the inclusions and projections exhibit the original
complex as their finite direct sum. The splitting preserves homology and
quasi-isomorphisms. The direct image of E_n from the clopen rank-n stratum
lies entirely in the e_n summand. The hypothesized cohomology isomorphisms
are algebra-linear, hence commute with these idempotents. Consequently
that summand of K has cohomology only in degree n, equal to the direct
image of E_n. Truncation above and below n identifies it with this module
in degree n. Apply the same truncations to the zero-differential comparison
complex. Sum these finitely many isomorphisms and compose with the splitting
isomorphisms. Off the closed image the algebra and all its modules are zero.
If Z is empty every summand is zero. Rank zero is the degree-zero case.
No stratum is required to be open in Y. -/
theorem clopenRankStrata_formality
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (r : LocallyConstant Z ℕ) (hfinite : (Set.range r).Finite)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (hK : ∀ n : ℤ, Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n))) :
    Nonempty (DerivedCategory.Q.obj
      (((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (CochainComplex.of T (fun _ => 0) (fun _ => zero_comp))) ≅ K) := by sorry

end AlgebraicGeometry
