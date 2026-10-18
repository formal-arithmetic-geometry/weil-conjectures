/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.CategoryTheory.SiteCoveringAxioms

import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Geometric stalks as inverse images of topos points

Source: Stacks Project, Tags 0991, 04FM, and 00Y8
(blueprint: lem-fix-geometric-stalk-topos-point).

The two clauses cover the small etale and small pro-etale sites. The right adjoint's
underlying presheaf is specified as functions on lifts, including all its restriction maps.
The pro-etale stalk functor uses the already defined pointed-neighbourhood colimit.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The function presheaves attached to a lift functor `L`: the value at `U` is
`L(U) → T`, restriction is precomposition with `L.map`, and a map of sets acts by
postcomposition. This is the presheaf `p_*T` of the statement.
Source: Stacks Project, Tag 00Y8 (blueprint: lem-fix-geometric-stalk-topos-point). -/
def geometricLiftFunctionPresheaf {C : Type v} [Category.{w} C] (L : C ⥤ Type u) :
    Type (u + 1) ⥤ (Cᵒᵖ ⥤ Type (u + 1)) where
  obj T :=
    { obj U := L.obj U.unop → T
      map f := ↾fun a x ↦ a (L.map f.unop x)
    }
  map t := { app U := ↾fun a x ↦ t (a x) }

/-- The set-valued pro-etale geometric stalk as a functor. Its object at `F` is
`proEtaleGeometricSetStalk y F`; maps are the colimit maps induced by sectionwise maps.
Source: Stacks Project, Tag 0991 (blueprint: lem-fix-geometric-stalk-topos-point). -/
noncomputable def proEtaleGeometricSetStalkFunctor
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    Sheaf (ProEt.topology Y) (Type (u + 1)) ⥤ Type (u + 1) :=
  sheafToPresheaf (ProEt.topology Y) (Type (u + 1)) ⋙
    (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
      (proEtaleGeometricNeighbourhoodForget y).op ⋙ colim

/-- On either small site the prescribed function presheaves form a sheaf-valued functor
right adjoint to the geometric stalk, and that stalk preserves finite limits. Existence
of the sheaf-valued functor with the displayed underlying presheaf equality states that
`p_*T` is a sheaf for every `T`. The adjunction with its left exact left adjoint is the
specified morphism of topoi from sets.
Source: Stacks Project, Tags 0991, 04FM, and 00Y8
(blueprint: lem-fix-geometric-stalk-topos-point).

Proof:
1. The index is the opposite pointed-neighbourhood category. It is filtered by
   lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered or
   def-weil-proetale-geometric-stalk. The chosen size bound makes the index small in
   the larger universe. Colimit maps of sectionwise natural transformations give the
   stalk functor, with identity and composition from colimit uniqueness.
2. Etale covers lift the geometric point with the same field by
   lem-weil-pbc-etale-cover-geometric-point-lift.
3. Pro-etale covers lift it as well: base change the fpqc cover along the point
   (lem-galois-fpqc-covering-base-change), choose a point on a nonempty member and an
   affine neighbourhood. Weak etaleness is stable under base change, composition and
   source locality. By lem-weil-pbc-weak-etale-field its residue field is separable
   algebraic over Omega; lem-weil-pbc-separable-extension-embeds-separably-closed gives
   an Omega-map back to Omega. The affine spectrum construction gives the desired lift.
   Transport through skeleton isomorphisms preserves the lift equation.
4. Two lifts with the same image pair uniquely in the fibre-product overlap. Thus a
   matching family of functions on lifts glues to a unique function, proving that the
   prescribed presheaves are sheaves. Postcomposition defines the sheaf-valued functor.
5. A map a from the stalk to T gives the sheaf map s ↦ (u ↦ a(ι_(U,u)(s))). The
   pointed-arrow cocone identity proves naturality under restriction.
6. Conversely a sheaf map b gives the cocone s ↦ b_U(s)(u). The colimit universal
   property gives its unique map to T. These constructions are inverse and natural in
   the sheaf and in T, hence define the adjunction.
7. Sheaf limits are sectionwise by lem-weil-pbc-site-sheaf-sets-limits-sectionwise.
   The canonical comparison between the stalk of a finite limit and the limit of the
   stalks is invertible by lem-weil-pbc-filtered-colimits-commute-finite-limits, with
   the same filtered index for every sheaf. This includes the empty finite diagram.
   The adjunction is therefore a morphism of topoi with the specified inverse image. -/
theorem geometricStalkToposPoint
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    (∃ R : Type (u + 1) ⥤ Sheaf Y.smallEtaleTopology (Type (u + 1)),
      R ⋙ sheafToPresheaf Y.smallEtaleTopology (Type (u + 1)) =
        geometricLiftFunctionPresheaf (pointSmallEtale y).fiber ∧
      Nonempty ((pointSmallEtale y).sheafFiber (A := Type (u + 1)) ⊣ R) ∧
      PreservesFiniteLimits ((pointSmallEtale y).sheafFiber (A := Type (u + 1)))) ∧
    (∃ R : Type (u + 1) ⥤ Sheaf (ProEt.topology Y) (Type (u + 1)),
      R ⋙ sheafToPresheaf (ProEt.topology Y) (Type (u + 1)) =
        geometricLiftFunctionPresheaf
          (ProEt.forget Y ⋙ coyoneda.obj (op (Over.mk y))) ∧
      Nonempty (proEtaleGeometricSetStalkFunctor y ⊣ R) ∧
      PreservesFiniteLimits (proEtaleGeometricSetStalkFunctor y)) := by
  sorry

end AlgebraicGeometry.Scheme
