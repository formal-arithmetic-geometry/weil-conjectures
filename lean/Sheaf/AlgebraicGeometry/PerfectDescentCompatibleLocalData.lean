/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectDescentOnOpen
public import Sheaf.AlgebraicGeometry.PerfectOpenGluingData
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.PerfectDescendMorphisms
import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

/-! # Compatible local descent data at a common finite stage

Source: Stacks Project, Tag 09RF, the construction of a, b and c before gluing.
(blueprint: lem-pc-perfect-descent-compatible-local-data).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Descend the two local perfect objects and their overlap identification, and form
compatible adjoint maps into the restrictions of the common derived direct image.
The conclusion contains no object or comparison map on the whole stage scheme.
Source: Stacks Project, Tag 09RF, two-open induction, up to the invocation of Tag 08DG.
(blueprint: lem-pc-perfect-descent-compatible-local-data).

Proof: In the presentation Z of W union V take the inverse-image cover. Base change
its members to the limit and restrict E. Open restriction preserves perfectness
(Tag 09UA). Apply dW and dV to their presentations into Xi. Directedness gives a
common later stage; the base-change composition isomorphisms transport the two
comparison isomorphisms there, and pullback preserves perfectness. The stage opens
U and V are the inverse images of the original opens and cover the stage scheme.
Their intersection is quasi-compact because the finitely presented stage scheme
is quasi-separated and both opens are quasi-compact. Its structural map is
finitely presented. On the overlap apply perfect_descend_morphisms on a tail of
the directed system to the limit identification between the two local objects.
Lift the identification and its inverse and stabilize their two inverse equations;
the isomorphism clause gives c at one later common stage. Pullback composition
coherence identifies its limit pullback with the prescribed identification.
Choose the derived pullback/direct image adjunction on that stage. The canonical
restriction comparisons γU and γV and Tag 08FE identify the local adjoints of the
comparison isomorphisms with maps a and b into restrictions of Rg_*E. Naturality
of adjunction and its counit makes their overlap equation exactly hab below.
The local adjoints, expressed using γ inverse and the restricted global counit,
are the original comparison isomorphisms, giving the final two IsIso clauses.
Empty, equal, and disjoint opens need no extra condition: the same restrictions
and equations exist on an empty overlap, and the initial index supplies a stage.
-/
theorem perfect_descent_compatible_local_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
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
      let g := baseChangeMap (f ≫ s)
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
      PerfectOpenGluingData g E := by sorry

end AlgebraicGeometry
