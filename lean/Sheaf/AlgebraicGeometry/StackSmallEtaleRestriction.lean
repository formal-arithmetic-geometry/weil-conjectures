/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q69 and Q10
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Cartesian small étale restriction of big-fppf module sheaves

Source: Stacks Project, stacks-cohomology.tex, section-locally-quasi-coherent
and definition-flat-base-change; stacks-sheaves.tex, definition-pullback
(blueprint: def-sfb-stack-small-etale-restriction).

## Main definitions

* `moduliTestSlice`: the scheme-slice comparison for a test object.
* `moduliEtaleLiftOver`, `moduliEtaleLift`, `moduliEtaleLiftSchemeIso`:
  cartesian lifts of small étale tests and their canonical base identifications.
* `moduliEtaleModuleRings`, `moduliEtaleRestriction`: the regular-function rings
  and actual module restriction by precomposition along these lifts.
* `moduliEtaleLiftArrow`, `moduliEtaleLiftTransformation`: the unique lifted
  base-change projections, natural in the small étale test.

The declarations are extracted unchanged from `StackLqcCoherator`, which now
publicly imports this module. The slice equivalence, continuity, base triangle
and naturality are the named proof obligations of these constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- The scheme over a test object underlying an arrow of the total category.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: def-sfb-stack-small-etale-restriction). -/
def moduliTestSlice {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) (x : F.obj) :
    Over x ⥤ Over ((moduliSchemeForget F).obj x) :=
  Over.post F.p ⋙ Over.iteratedSliceForward (F.p.obj x)

/-- A fibred groupoid has the usual scheme slice over each object.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: def-sfb-stack-small-etale-restriction).
Proof: every scheme arrow to the base of x has a cartesian lift to x. Every arrow
of F is strongly cartesian, so each base triangle has exactly one lift. This gives
essential surjectivity and bijections on Hom sets, hence an equivalence. -/
theorem moduliTestSlice_isEquivalence {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj) :
    (moduliTestSlice F x).IsEquivalence := by
  sorry

/-- Lift étale tests to the slice of the total category. The inverse of an equivalence
is fixed up to its unique compatible isomorphism; no unrelated object is selected.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: def-sfb-stack-small-etale-restriction). -/
noncomputable def moduliEtaleLiftOver {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj) :
    ((moduliSchemeForget F).obj x).Etale ⥤ Over x :=
  letI := moduliTestSlice_isEquivalence F hF x
  Scheme.Etale.forget _ ⋙ (moduliTestSlice F x).asEquivalence.inverse

/-- The total-category objects on which small étale restriction is evaluated.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: def-sfb-stack-small-etale-restriction). -/
noncomputable def moduliEtaleLift {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj) :
    ((moduliSchemeForget F).obj x).Etale ⥤ F.obj :=
  moduliEtaleLiftOver F hF x ⋙ Over.forget x

/-- The lifted test scheme is canonically the original étale scheme.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: def-sfb-stack-small-etale-restriction). -/
noncomputable def moduliEtaleLiftSchemeIso {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj)
    (V : ((moduliSchemeForget F).obj x).Etale) :
    (moduliSchemeForget F).obj ((moduliEtaleLift F hF x).obj V) ≅ V.left :=
  letI := moduliTestSlice_isEquivalence F hF x
  (Over.forget _).mapIso
    ((moduliTestSlice F x).asEquivalence.counitIso.app ((Scheme.Etale.forget _).obj V))

/-- Étale restriction preserves the sheaf condition on the total fppf site.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: def-sfb-stack-small-etale-restriction).
Proof: a jointly surjective étale family lifts to a family of arrows over its
scheme maps. It is an fppf cover. Cartesian uniqueness identifies its overlaps,
so matching families and their unique gluings are the same on both sites. -/
@[instance] theorem moduliEtaleLift_isContinuous {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj) :
    (moduliEtaleLift F hF x).IsContinuous
      ((moduliSchemeForget F).obj x).smallEtaleTopology (moduliFppfTopology F) := by
  sorry

/-- The small étale structure sheaf, in the total site's regular-function coordinates.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: def-sfb-stack-small-etale-restriction). -/
noncomputable def moduliEtaleModuleRings {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj) :
    Sheaf ((moduliSchemeForget F).obj x).smallEtaleTopology RingCat.{max (u + 1) v w} :=
  letI := moduliEtaleLift_isContinuous F hF x
  ((moduliEtaleLift F hF x).sheafPushforwardContinuous _ _ _).obj (moduliModuleRings F hF)

/-- Restriction H_z of a big-fppf module to a test scheme's small étale site.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: def-sfb-stack-small-etale-restriction). -/
noncomputable def moduliEtaleRestriction {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) (x : F.obj) :
    ringedSiteModules.{max (u + 1) v w} (moduliModuleRings F hF) ⥤
      ringedSiteModules.{max (u + 1) v w} (moduliEtaleModuleRings F hF x) :=
  letI := moduliEtaleLift_isContinuous F hF x
  SheafOfModules.pushforward (F := moduliEtaleLift F hF x) (𝟙 _)

/-- The base arrow between lifted tests satisfies the required slice triangle.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: def-sfb-stack-small-etale-restriction).
Proof: the counit of each slice equivalence identifies its lifted projection with
the original étale map. Substitute these identities. The two middle maps cancel,
and the remaining equality is the defining equation of the scheme fibre product. -/
theorem moduliEtaleLiftArrow_w {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x) (V : ((moduliSchemeForget F).obj x).Etale) :
    (moduliEtaleLiftSchemeIso F hF y (((moduliSchemeForget F).map a).Etale.obj V)).hom ≫
        pullback.fst V.hom ((moduliSchemeForget F).map a) ≫
        (moduliEtaleLiftSchemeIso F hF x V).inv ≫
        (moduliSchemeForget F).map ((moduliEtaleLiftOver F hF x).obj V).hom =
      (moduliSchemeForget F).map
        (((moduliEtaleLiftOver F hF y).obj
          (((moduliSchemeForget F).map a).Etale.obj V)).hom ≫ a) := by
  sorry

/-- The unique arrow between lifted tests over the fibre-product projection.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: def-sfb-stack-small-etale-restriction). -/
noncomputable def moduliEtaleLiftArrow {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x) (V : ((moduliSchemeForget F).obj x).Etale) :
    (moduliEtaleLift F hF y).obj (((moduliSchemeForget F).map a).Etale.obj V) ⟶
      (moduliEtaleLift F hF x).obj V :=
  letI := moduliTestSlice_isEquivalence F hF x
  ((moduliTestSlice F x).preimage
    (X := Over.mk (((moduliEtaleLiftOver F hF y).obj
      (((moduliSchemeForget F).map a).Etale.obj V)).hom ≫ a))
    (Y := (moduliEtaleLiftOver F hF x).obj V)
    (Over.homMk
      ((moduliEtaleLiftSchemeIso F hF y
        (((moduliSchemeForget F).map a).Etale.obj V)).hom ≫
        pullback.fst V.hom ((moduliSchemeForget F).map a) ≫
          (moduliEtaleLiftSchemeIso F hF x V).inv)
      (moduliEtaleLiftArrow_w F hF a V))).left

/-- Cartesian uniqueness makes the lifted restriction arrow natural in the étale test.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: def-sfb-stack-small-etale-restriction).
Proof: both composites have the same image in the scheme slice, by naturality of
the counits and of the fibre-product projections. Faithfulness of the slice
comparison makes the composites equal. -/
theorem moduliEtaleLiftArrow_naturality {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x) {V W : ((moduliSchemeForget F).obj x).Etale} (f : V ⟶ W) :
    (moduliEtaleLift F hF y).map (((moduliSchemeForget F).map a).Etale.map f) ≫
        moduliEtaleLiftArrow F hF a W =
      moduliEtaleLiftArrow F hF a V ≫ (moduliEtaleLift F hF x).map f := by
  sorry

/-- The canonical restriction transformation on lifted étale tests.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: def-sfb-stack-small-etale-restriction). -/
noncomputable def moduliEtaleLiftTransformation {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x) :
    ((moduliSchemeForget F).map a).Etale ⋙ moduliEtaleLift F hF y ⟶
      moduliEtaleLift F hF x where
  app V := moduliEtaleLiftArrow F hF a V
  naturality {_V _W} f := moduliEtaleLiftArrow_naturality F hF a f

end CategoryTheory
