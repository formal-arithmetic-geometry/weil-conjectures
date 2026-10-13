/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectDescentOnOpen
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation


import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

/-! # Two local perfect models at a common stage

Source: Stacks Project, Tag 09RF, the choice of E_{U,i} and E_{V,i}.
(blueprint: lem-pc-perfect-descent-common-local-models).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Descend the two restrictions separately and move them to a common stage.
This supplies no overlap isomorphism and no map into a derived direct image.
Source: Stacks Project, Tag 09RF, first sentence of the two-open induction.
(blueprint: lem-pc-perfect-descent-common-local-models).

Proof: Pull W and V back along f, and then along the projection of the limit
base change. Restriction of E is perfect by Tag 09UA and the derived open
restriction comparison. The presentations (f inverse W).toScheme → Xi and
(f inverse V).toScheme → Xi have images W and V because hf says their union
is the image of f. Apply dW and dV to these presentations and restricted objects.
Choose a common upper bound of the resulting indices. Pull the stage models
back to this stage; they remain perfect by Tag 09UA. The cartesian identifications
of each restricted base change with the corresponding stage open, and coherent
composition of derived pullbacks, give the two displayed comparison isomorphisms.
The opens cover since inverse image preserves joins and top. They are compact:
f has compact image W union V, hence has compact source; Xi is quasi-separated
since s is quasi-separated and its base is affine. Thus f is quasi-compact, and
its inverse images of W and V are compact. The stage projection to Z is affine
as a base change of a morphism of affine schemes, so these opens remain compact.
Empty or coincident opens cause no exception, and i ensures a nonempty index set.
-/
theorem perfect_descent_common_local_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (W V : Xi.Opens) (hW : IsCompact (W : Set Xi)) (hV : IsAffineOpen V)
    (dW : PerfectDescentOnOpen R c i Xi s W)
    (dV : PerfectDescentOnOpen R c i Xi s V)
    (Z : Scheme.{u}) (f : Z ⟶ Xi) [IsOpenImmersion f] (hf : f.opensRange = W ⊔ V)
    (E : schemeDerivedCategory (pullback (f ≫ s) (Spec.map (c.ι.app i))))
    (hE : (pullback (f ≫ s) (Spec.map (c.ι.app i))).IsPerfect E) :
    ∃ (j : I) (hij : i ≤ j),
      let Y := pullback (f ≫ s) (Spec.map (R.map (homOfLE hij)))
      let X := pullback (f ≫ s) (Spec.map (c.ι.app i))
      let g := baseChangeMap (f ≫ s)
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
      ∃ (U V : Y.Opens), U ⊔ V = ⊤ ∧
        IsCompact (U : Set Y) ∧ IsCompact (V : Set Y) ∧
      ∃ (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme),
        U.toScheme.IsPerfect A ∧ V.toScheme.IsPerfect B ∧
        Nonempty ((derivedPullback (g ∣_ U)).obj A ≅
          (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E) ∧
        Nonempty ((derivedPullback (g ∣_ V)).obj B ≅
          (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) := by sorry

end AlgebraicGeometry
