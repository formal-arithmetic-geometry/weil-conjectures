module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Reduced finite-type closure model of a closed fibre subset

Source: Stacks Project, More on Morphisms, discussion preceding Tag 054Y and the proof
of Tag 0554 (blueprint: lem-trf-closed-generic-subset-finite-type-model).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed subset of one fibre has a reduced closed closure model of finite type.
All fibre identifications here concern underlying spaces, without any assertion that
these scheme-theoretic fibres are reduced.

Source: Stacks Project, More on Morphisms, discussion preceding Tag 054Y and proof of
Tag 0554 (blueprint: lem-trf-closed-generic-subset-finite-type-model).

Proof plan:
1. Let B be the image of A under the fibre projection, and F the set-theoretic fibre.
   The homeomorphism of def-pc-scheme-fibre makes B closed in F, hence B = C ∩ F for
   an ambient closed C. Its closure D is contained in C, so D ∩ F = B. Injectivity
   of the fibre projection then gives the stated inverse-image equality over y.
2. Apply clause (2) of lem-weil-pbc-reduced-induced-closed-subscheme to D. This gives
   a reduced scheme Z and a closed immersion j with image D (Stacks 01J3/01J4).
3. By lem-weil-pbc-closed-immersion-proper, j is of finite type. Composition with f
   is of finite type by lem-sfb-finite-type-composition-base-change (01W5/01T3).
4. For each t, the canonical fibre map is fiberMap j rfl along Spec κ(t) → Y.
   Its square commutes with both projections by the fibre-product definition.
   The two fibre homeomorphisms of def-pc-scheme-fibre identify this map with the
   restriction of the homeomorphism j onto D to the set-theoretic fibres over t.
   It is therefore a homeomorphism onto the inverse image of D under f.fiberι t.
   This subset is closed, since D is closed and the projection is continuous, so
   the canonical map is a closed embedding with precisely the stated range.
   At t = y, step 1 identifies this range with A.
-/
theorem exists_reduced_closed_fiber_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) (A : Set (f.fiber y))
    (hA : IsClosed A) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X),
      IsReduced Z ∧ IsClosedImmersion j ∧
      Set.range j = closure ((f.fiberι y) '' A) ∧
      LocallyOfFiniteType (j ≫ f) ∧ QuasiCompact (j ≫ f) ∧
      (∀ t : Y,
        Topology.IsClosedEmbedding
          (fiberMap (a := j ≫ f) (b := f) j rfl (Y.fromSpecResidueField t)) ∧
        Set.range (fiberMap (a := j ≫ f) (b := f) j rfl (Y.fromSpecResidueField t)) =
          (f.fiberι t) ⁻¹' closure ((f.fiberι y) '' A)) ∧
      (f.fiberι y) ⁻¹' closure ((f.fiberι y) '' A) = A := by
  sorry

end AlgebraicGeometry.Scheme.Hom
