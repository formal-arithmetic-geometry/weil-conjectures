/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts
import Sheaf.AlgebraicGeometry.LocalClosedLocusGluing
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The lowest matrix-zero closed locus

Source: Stacks Project, Tag 0BDL.
(blueprint: lem-sc-perfect-lowest-matrix-closed-locus).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

private theorem pullbackHomology_restrict_iso
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {S T : Scheme.{u}} (E : schemeDerivedCategory S) (a : ℤ)
    (h : T ⟶ S) (V : T.Opens) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) a).obj
        ((derivedPullback (V.ι ≫ h)).obj E) ≅
      (Modules.restrictFunctor V.ι).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
            ((derivedPullback h).obj E))) := by
  obtain ⟨_, _, _, c, _⟩ := exists_derivedPullbackComposition.{u, w}
  obtain ⟨e⟩ := Modules.nonempty_homology_derivedOpenPullback_iso_restrict
    V ((derivedPullback h).obj E) a
  exact ⟨(DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) a).mapIso
      ((c V.ι h).app E).symm ≪≫ e⟩

private theorem pullbackHomology_rank_restrict
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {S T : Scheme.{u}} (E : schemeDerivedCategory S) (a : ℤ) (r : ℕ)
    (h : T ⟶ S) (V : T.Opens)
    (hfree : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
          ((derivedPullback h).obj E)) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) a).obj
          ((derivedPullback (V.ι ≫ h)).obj E)) r := by
  obtain ⟨e⟩ := pullbackHomology_restrict_iso E a h V
  let := hfree
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm

private theorem pullbackHomology_rank_of_locally
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {S T : Scheme.{u}} (E : schemeDerivedCategory S) (a : ℤ) (r : ℕ)
    (h : T ⟶ S)
    (hlocal : ∀ x : T, ∃ V : T.Opens, x ∈ V ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) a).obj
            ((derivedPullback (V.ι ≫ h)).obj E)) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
          ((derivedPullback h).obj E)) r := by
  classical
  choose V hx hfree using hlocal
  apply Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top _ V
  · apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    obtain ⟨e⟩ := pullbackHomology_restrict_iso E a h (V x)
    let := hfree x
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e


/-- On an open where the lowest fibre rank is at most `r`, the matrix-zero locus
is a finitely presented closed immersion representing rank-`r` lowest cohomology.
Only a single pullback is tested here; no universal condition or comparison iso is asserted.
Source: Stacks Project, Tag 0BDL, proof after replacing the base by its rank-bound open.
(blueprint: lem-sc-perfect-lowest-matrix-closed-locus).

Proof:
1. At points of fibre rank `r`, take the affine finite-free residue model of Tag 0BCD.
   Tor amplitude makes the terms below `a` zero, and the degree-`a` term has rank `r`.
   Cut out the finitely many entries of its outgoing matrix. At points of smaller
   rank, upper semicontinuity gives open neighbourhoods of smaller rank; use the
   empty closed subscheme on those neighbourhoods.
2. After any map into a matrix chart, the kernel of the outgoing matrix is the
   degree-`a` cohomology. If the matrix vanishes, this kernel is free of rank `r`.
   Conversely, locally trivialize a rank-`r` kernel. Its inclusion into the free
   degree-`a` term is a square injective map. Its cokernel has zero dual by Tag 0EWY.
   The outgoing matrix factors through that cokernel; each target coordinate is
   therefore zero. Thus the matrix is zero and the map factors through the equations.
3. On a smaller-rank neighbourhood the same converse is impossible: a free
   rank-`r` kernel inside a term of smaller rank would violate the square-minor
   injectivity criterion after adjoining zero columns. Equivalently the above
   matrix-kernel argument forces the lowest fibre rank to be `r`.
4. The chartwise closed subschemes represent exactly the same single-pullback
   condition. On overlaps their unique identifications over the base obey the
   cocycle law, so their quasi-coherent ideals and closed subschemes glue.
   Each ideal is generated by finitely many matrix entries. The resulting closed
   immersion is locally of finite presentation and is quasi-compact. -/
theorem exists_perfectLowestMatrixClosedLocus
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes S E F i)
    (r : ℕ)
    (U : S.Opens) (hU : ∀ x : S, x ∈ U → derivedFiberBetti S E a x ≤ r) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ U.toScheme),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation i ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ U.toScheme),
        (∃ g : T ⟶ Z, g ≫ i = h) ↔
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
                ((derivedPullback (h ≫ U.ι)).obj E)) r) := by
  let P : ∀ T : Scheme.{u}, (T ⟶ U.toScheme) → Prop := fun T h ↦
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
          ((derivedPullback (h ≫ U.ι)).obj E)) r
  have hrestrict : ∀ (T : Scheme.{u}) (h : T ⟶ U.toScheme) (V : T.Opens),
      P T h → P V.toScheme (V.ι ≫ h) := by
    intro T h V hfree
    simpa only [P, Category.assoc] using
      pullbackHomology_rank_restrict E a r (h ≫ U.ι) V hfree
  have hlocal : ∀ (T : Scheme.{u}) (h : T ⟶ U.toScheme),
      (∀ x : T, ∃ V : T.Opens, x ∈ V ∧ P V.toScheme (V.ι ≫ h)) → P T h := by
    intro T h hfree
    apply pullbackHomology_rank_of_locally E a r (h ≫ U.ι)
    simpa only [P, Category.assoc] using hfree
  have hcharts := exists_perfectLowestMatrixCharts S E hE a b hamp r U hU
  obtain ⟨Z, i, hi, hfp, hfactor⟩ :=
    exists_closedLocus_of_local_charts U.toScheme P hrestrict hlocal hcharts
  exact ⟨Z, i, hi, hfp, hfactor⟩

end AlgebraicGeometry.Scheme
