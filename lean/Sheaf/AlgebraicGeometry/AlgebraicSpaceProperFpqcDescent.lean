/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcQCSeparatedDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Mathlib.CategoryTheory.Sites.Precoverage

/-! # Fpqc descent of properness for algebraic spaces over schemes

Source: Stacks Project, Spaces Descent, Tags 0422 and 03YH
(blueprint: lem-sfb-space-proper-fpqc-descent).

Properness uses the existing separated, finite type and universally closed predicates.
The pullbacks are actual sheaf fibre products, with the scheme member placed first
so that their first projection is the base-changed morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Properness of a morphism from an algebraic space to a scheme is fpqc local on
its target. No flatness, finite presentation, Noetherian, connectedness or nonemptiness
hypothesis is imposed on the morphism.
Source: Stacks Project, Spaces Descent, Tags 0422 and 03YH, restricted to scheme targets
and scheme covering families (blueprint: lem-sfb-space-proper-fpqc-descent).

Proof:
1. If f is proper, lem-sfb-space-proper-base-change gives properness of each pullback.
   Its separatedness, chartwise local finite type and universal closedness conventions
   are those of def-sfb-space-morphism-properties. Its atlas-based quasi-compactness
   agrees with compactness of the point space by lem-a1-space-finite-affine-subatlas:
   a quasi-compact atlas has compact target, and affine refinement of any atlas followed
   by extraction of a finite subatlas proves the converse on every affine scheme test.
2. Conversely each proper pullback is separated, quasi-compact, chartwise locally of
   finite type and universally closed by def-sfb-space-morphism-properties.
3. Apply lem-sfb-space-fpqc-qc-separated-descent separately to quasi-compactness and
   separatedness. Compare its atlas quasi-compactness with compact point spaces using
   lem-a1-space-finite-affine-subatlas in both directions as in step 1.
4. The fpqc-target clause of lem-sfb-space-lft-smooth-fpqc-locality descends local finite
   type. The given scheme family has fpqc scheme pullbacks by
   lem-galois-fpqc-covering-base-change, meeting that clause's covering convention.
   Combine local finite type with quasi-compactness to obtain finite type.
5. Apply lem-sfb-space-fpqc-descend-universally-closed to the same family. Its only
   property assumption is universal closedness of each pullback, supplied by step 2.
   Separatedness, finite type and universal closedness give MapIsProper f. -/
theorem proper_iff_fpqc_scheme_cover {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Over S) (f : X ⟶ schemeSpace T)
    {I : Type v} (Tᵢ : I → Over S) (g : ∀ i : I, Tᵢ i ⟶ T)
    (hg : Presieve.ofArrows (fun i : I ↦ (Tᵢ i).left) (fun i : I ↦ (g i).left) ∈
      Scheme.fpqcPrecoverage T.left) :
    MapIsProper f ↔ ∀ i : I,
      MapIsProper (enlargedFibreProductFst
        (ObjectProperty.homMk ⟨yoneda.map (g i)⟩ : schemeSpace (Tᵢ i) ⟶ schemeSpace T)
        f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
