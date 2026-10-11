/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures

/-! # Composition of inverse images of étale sheaves of sets, with units

Source: Stacks Project, Sites, Tags 03CB and 03CC, and Étale Cohomology, Tag 09ZF,
third paragraph of the proof
(blueprint: lem-weil-pbc-sets-etale-inverse-image-composition-units).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

local notation "L" => Scheme.etaleSetPullback
local notation "b" => MorphismProperty.Over.pullback @Etale ⊤
local notation "η[" S "," T "]" e =>
  Adjunction.unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b e) _
      (Scheme.smallGrothendieckTopology @Etale S)
      (Scheme.smallGrothendieckTopology @Etale T))

/-- Source: Stacks Project, Sites, Tags 03CB and 03CC; Étale Cohomology, Tag 09ZF,
third paragraph of the proof
(blueprint: lem-weil-pbc-sets-etale-inverse-image-composition-units).
The inverse image `L e` is left Kan extension followed by sheafification, and `η[S, T] e`
is the unit of its adjunction to restriction along base change. The isomorphisms
are natural in the sheaf, preserve pulled-back sections, are unique even for a
fixed sheaf, and satisfy associativity. The base-change comparison in the section
formula is the canonical fibre-product pasting isomorphism.

Proof:
1. By lem-weil-pbc-etale-inverse-image-algebraic-structures, the unit sends a
   section to its identity-indexed colimit representative followed by sheafification.
   Naturality in site objects and in sheaves gives the two equations in clause (0),
   using lem-weil-pbc-presheaf-pullback-sets-left-exact and def-weil-pbc-sheafification.
2. By lem-weil-pbc-cartesian-square-pasting and def-pc-fibre-product, iterated base
   change is canonically isomorphic to composite base change, naturally in objects.
   Both triple comparisons have the same projections, hence agree.
3. Apply def-weil-pbc-composite-adjunction to the two inverse-image adjunctions,
   and lem-weil-pbc-conjugate-iso-unit-equation to the direct-image comparison.
   This gives the natural composition isomorphism and its unit equation.
4. By lem-weil-pbc-site-sheafification-sections-local, applied twice, every section
   of an iterated inverse image is locally a restriction of an iterated pulled-back
   section. Pull back the intermediate covering using
   lem-weil-pbc-etale-base-change-continuous. A morphism satisfying the unit equation
   therefore agrees locally with the comparison, hence equals it by the sheaf axiom
   of def-weil-pbc-etale-sheaf-of-sets. This proves fixed-sheaf uniqueness.
5. On locally generating triple pulled-back sections, unit naturality and the
   composition equations identify both associative composites with the pullback
   along the composite morphism. The triple fibre-product comparisons agree by
   their projections. Local equality and the sheaf axiom give associativity. -/
theorem etaleSetInverseImageCompositionUnits :
    (∀ (S T : Scheme.{u}) (e : T ⟶ S)
      (G : Sheaf S.smallEtaleTopology (Type (u + 1)))
      (U U' : S.Etale) (a : U' ⟶ U) (s : G.obj.obj (op U)),
      ((η[S, T] e).app G).hom.app (op U') (G.obj.map a.op s) =
        ((L e).obj G).obj.map ((b e).map a).op (((η[S, T] e).app G).hom.app (op U) s)) ∧
    (∀ (S T : Scheme.{u}) (e : T ⟶ S)
      (G G' : Sheaf S.smallEtaleTopology (Type (u + 1))) (ψ : G ⟶ G')
      (U : S.Etale) (s : G.obj.obj (op U)),
      ((η[S, T] e).app G').hom.app (op U) (ψ.hom.app (op U) s) =
        ((L e).map ψ).hom.app (op ((b e).obj U))
          (((η[S, T] e).app G).hom.app (op U) s)) ∧
    ∃ c : ∀ (X Y W : Scheme.{u}) (f : Y ⟶ X) (g : W ⟶ Y),
      L f ⋙ L g ≅ L (g ≫ f),
      (∀ (X Y W : Scheme.{u}) (f : Y ⟶ X) (g : W ⟶ Y)
        (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (U : X.Etale) (s : F.obj.obj (op U)),
        ((c X Y W f g).hom.app F).hom.app (op ((b g).obj ((b f).obj U)))
          (((η[Y, W] g).app ((L f).obj F)).hom.app (op ((b f).obj U))
            (((η[X, Y] f).app F).hom.app (op U) s)) =
          ((L (g ≫ f)).obj F).obj.map
            ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app U).op
            (((η[X, W] (g ≫ f)).app F).hom.app (op U) s)) ∧
      (∀ (X Y W : Scheme.{u}) (f : Y ⟶ X) (g : W ⟶ Y)
        (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (q : (L g).obj ((L f).obj F) ⟶ (L (g ≫ f)).obj F),
        (∀ (U : X.Etale) (s : F.obj.obj (op U)),
          q.hom.app (op ((b g).obj ((b f).obj U)))
            (((η[Y, W] g).app ((L f).obj F)).hom.app (op ((b f).obj U))
              (((η[X, Y] f).app F).hom.app (op U) s)) =
            ((L (g ≫ f)).obj F).obj.map
              ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app U).op
              (((η[X, W] (g ≫ f)).app F).hom.app (op U) s)) →
          q = (c X Y W f g).hom.app F) ∧
      (∀ (X Y W V : Scheme.{u}) (f : Y ⟶ X) (g : W ⟶ Y) (h : V ⟶ W)
        (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
        (L h).map ((c X Y W f g).hom.app F) ≫
            (c X W V (g ≫ f) h).hom.app F =
          (c Y W V g h).hom.app ((L f).obj F) ≫
            (c X Y V f (h ≫ g)).hom.app F ≫
              eqToHom (congrArg (fun k : V ⟶ X ↦ (L k).obj F) (Category.assoc h g f))) := by
  sorry

end AlgebraicGeometry
