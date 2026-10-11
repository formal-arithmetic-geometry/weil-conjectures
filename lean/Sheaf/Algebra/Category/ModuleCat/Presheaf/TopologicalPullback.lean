/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Presheaf

/-!
# Pullback of presheaves of modules along a continuous map

Source: Stacks Project, Sheaves, Tags 008T, 008S and 008U
(blueprint: lem-pc-presheaf-module-inverse-image-adjunction).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace PresheafOfModules

/-- The section map from an open neighbourhood of `f(U)` into the presheaf pullback.
Source: Stacks Project, Sheaves, Tag 008T
(blueprint: lem-pc-presheaf-module-inverse-image-adjunction). -/
noncomputable def topologicalPullbackSectionMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (C : Type (u + 1)) [Category.{u} C] [HasColimits C] (G : Y.Presheaf C)
    (U : Opens X) (V : Opens Y) (h : U ≤ (Opens.map f).obj V) :
    G.obj (op V) ⟶ ((TopCat.Presheaf.pullback C f).obj G).obj (op U) :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G).app (op V) ≫
    ((TopCat.Presheaf.pullback C f).obj G).map (homOfLE h).op

/-- For a continuous map `f`, an `O`-module presheaf `G` pulls back sectionwise to a
module over the colimit ring presheaf. The action on sections is uniquely specified by
the coprojection formula. Direct image restricts scalars through the ring-presheaf unit.
The abelian-presheaf adjunction then restricts to an adjunction of module presheaves,
natural in both variables.

Proof (Stacks, Tags 008T, 008S, 008U): the neighbourhoods of `f(U)` form a filtered
category. Filtered-colimit representatives give a common neighbourhood for finitely
many ring and module sections, so the sectionwise multiplication is uniquely determined
and independent of representatives. The module laws, semilinear restrictions, and
linearity of pulled-back maps follow at that common neighbourhood. Direct image uses
restriction of scalars along the ring-presheaf unit. The abelian adjunction sends a
map `ψ` to `f_*ψ ∘ i_G`; the unit is linear, and the converse follows by checking
linearity on colimit representatives. These checks are compatible with both variables.
(blueprint: lem-pc-presheaf-module-inverse-image-adjunction) -/
def topologicalPullbackAdjunctionSpec {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : Y.Presheaf CommRingCat.{u}) : Prop :=
    let R := O ⋙ forget₂ CommRingCat RingCat
    let O' := (TopCat.Presheaf.pullback CommRingCat.{u} f).obj O
    let R' := O' ⋙ forget₂ CommRingCat RingCat
    let iO := Functor.whiskerRight
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app O)
      (forget₂ CommRingCat RingCat)
    ∃ P : PresheafOfModules.{u} R ⥤ PresheafOfModules.{u} R',
    ∃ e : P ⋙ toPresheaf R' ≅
        toPresheaf R ⋙ TopCat.Presheaf.pullback Ab.{u} f,
    ∃ adj : P ⊣ pushforward iO,
      (∀ (G : PresheafOfModules.{u} R) (U : Opens X) (V : Opens Y)
          (h : U ≤ (Opens.map f).obj V) (a : O.obj (op V)) (g : G.obj (op V)),
        let ringι := topologicalPullbackSectionMap f CommRingCat.{u} O U V h
        let groupι := topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h
        letI : Module (R'.obj (op U)) ((P.obj G).obj (op U)) :=
          ((P.obj G).obj (op U)).isModule
        @SMul.smul (R'.obj (op U)) ((P.obj G).obj (op U))
            ((P.obj G).obj (op U)).isModule.toSMul (ringι.hom a)
            (((e.app G).inv.app (op U)).hom (groupι.hom g)) =
          ((e.app G).inv.app (op U)).hom (groupι.hom (a • g))) ∧
      (∀ (G : PresheafOfModules.{u} R) (U : Opens X),
        ∃! μ : O'.obj (op U) →
            ((TopCat.Presheaf.pullback Ab.{u} f).obj G.presheaf).obj (op U) →
            ((TopCat.Presheaf.pullback Ab.{u} f).obj G.presheaf).obj (op U),
          ∀ (V : Opens Y) (h : U ≤ (Opens.map f).obj V)
              (a : O.obj (op V)) (g : G.obj (op V)),
            μ ((topologicalPullbackSectionMap f CommRingCat.{u} O U V h).hom a)
                ((topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom g) =
              (topologicalPullbackSectionMap f Ab.{u} G.presheaf U V h).hom (a • g)) ∧
      (∀ (G : PresheafOfModules.{u} R) (F : PresheafOfModules.{u} R')
          (ψ : P.obj G ⟶ F),
        (toPresheaf R).map ((adj.homEquiv G F) ψ) =
          (TopCat.Presheaf.pullbackPushforwardAdjunction Ab.{u} f).homEquiv
            G.presheaf F.presheaf
            ((e.app G).inv ≫ (toPresheaf R').map ψ))

/-- The concrete presheaf-module pullback and its adjunction, as specified by
`topologicalPullbackAdjunctionSpec`.

Source: Stacks Project, Sheaves, Tags 008T, 008S, 008U.
Proof, following the eight steps of the node:

1. The opens containing `f(U)`, ordered by reverse inclusion, form a nonempty
filtered category: the top open is an index and intersections give common later
indices (`def-weil-pbc-category-colimit`). The pointwise colimit description of
`def-weil-pbc-topological-inverse-image`, together with
`lem-pc-filtered-colimit-commrings-elementwise` and
`lem-weil-pbc-filtered-colimit-modules-elementwise` (over the integers), says every
ring or group section has a representative, and two representatives agree exactly
when their restrictions agree at a later index. Finite intersections therefore
give a common index for any finite collection of ring and group sections.
2. For representatives `a` and `g` at a common index define their product to be
the image of `a • g`. For a second choice of representatives, intersect the two
indices witnessing equality of the ring and group representatives. Semilinearity
of restrictions (`def-weil-presheaf-modules-sheafification`) identifies the two
products there. This proves well-definedness and the coprojection formula;
every pair has common representatives, so that formula also proves uniqueness.
3. Represent finitely many sections at one index. Each module law is the image
of that law at the index, since ring coprojections preserve ring operations and
group coprojections preserve addition. Restrictions preserve coprojections, so
are semilinear. The pullback of a module morphism preserves coprojections too,
and its linearity follows from linearity at the common index. This uses the two
definition nodes just cited and gives the module pullback functor.
4. Restrict scalars on `F(f⁻¹(V))` along the ring unit at `V`. Its naturality and
the semilinear restrictions of `F` give semilinear restrictions on direct image.
Direct image of a morphism is linear by restriction of scalars. This uses
`def-weil-pbc-topological-inverse-image` and
`def-weil-presheaf-modules-sheafification`.
5. The abelian adjunction (`def-weil-pbc-topological-inverse-image`) sends `ψ`
to `φ = f_*ψ ∘ i_G`. Naturality and restriction of coprojections give
`ψ_U ∘ ι_V = restriction ∘ φ_V` whenever `U ⊆ f⁻¹(V)`.
6. The coprojection formula at `f⁻¹(V)` makes `i_G` linear for the scalar
restriction in step 4. Thus a linear `ψ` gives a linear `φ` by composition.
7. Conversely, represent a ring section and a group section at a common `V`
using the two elementwise colimit lemmas of step 1. The formula of step 5,
linearity of `φ_V`, and semilinearity of restriction give
`ψ_U(ι(a • g)) = ι(a) • ψ_U(ι(g))`. Every pair is represented this way,
so `ψ` is linear. This is the direct unit computation replacing the source's
counit check, using only the two definition nodes and the elementwise lemmas.
8. Steps 6 and 7 identify exactly the linear subsets of the abelian Hom sets.
Restricting that bijection gives the module adjunction. Its naturality follows
from abelian naturality, since steps 3 and 4 preserve linear morphisms and the
forgetful functor on module morphisms is faithful.
(blueprint: lem-pc-presheaf-module-inverse-image-adjunction) -/
theorem topologicalPullbackAdjunction {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : Y.Presheaf CommRingCat.{u}) :
    topologicalPullbackAdjunctionSpec f O := by
  sorry

end PresheafOfModules
