/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.EtaleGeometricFibreConstantSections

/-! # Cech compatibility over one connected geometric fibre

Source: Stacks Project, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-cech-sections-connected-geometric-fibre).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

local notation "L" => Scheme.etaleSetPullback
local notation "I[" X "]" => Scheme.Etale.mk (𝟙 X)
set_option quotPrecheck false in
local notation "η[" X "," Y "]" e =>
  Adjunction.unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ e) _
      (Scheme.smallGrothendieckTopology @Etale X)
      (Scheme.smallGrothendieckTopology @Etale Y))
set_option quotPrecheck false in
local notation "R[" X "," Y "," e "," G "]" =>
  (((η[X,Y] e).app G).hom.app (op I[X]) ≫
    ((L e).obj G).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift e (𝟙 Y)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
        I[Y] ⟶ (MorphismProperty.Over.pullback @Etale ⊤ e).obj I[X]).op)

set_option backward.isDefEq.respectTransparency false in
/-- The two Cech pullbacks agree after restriction to one connected geometric fibre.
Only that fibre is assumed connected; no assertion of equality on the whole Cech
scheme is made.

Source: Stacks Project, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-cech-sections-connected-geometric-fibre).

Proof:
1. Put U = T ×_S Spec Ω, with projections p and h. Apply the inverse-image unit
   along p to a and restrict to the identity object of U. Composition comparisons
   and p ≫ f = h ≫ q transport this to a section of (h ≫ q)⁻¹F.
   By etaleGeometricFibreConstantSections on connected U, it is the constant
   section associated to a unique e in F_q.
2. Put D = T ×_S T and E = D ×_S Spec Ω, with maps d : E → D and v : E → Spec Ω.
   The two maps E → U are the pullback lifts (d ≫ pr_i, v). Their composites with
   h are both v. Pullback uniqueness proves that E is canonically U ×_(Spec Ω) U.
   Naturality of the units and associativity of the chosen composition comparisons
   identify the restrictions of the two displayed Cech sections with the pullbacks
   of the section in step 1 along these maps E → U. Terminal-object maps agree
   because their composites with the two pullback projections agree.
3. The naturality clause of etaleGeometricFibreConstantSections makes both sections
   constant with value e on E. Its comparison with the constant sheaf is an
   isomorphism, so their equality transports back to the displayed equation.
   No connectedness or nonemptiness of E is used. If U were empty the connectedness
   hypothesis would be impossible, as ConnectedSpace includes nonemptiness. -/
theorem etaleSet_cech_sections_agree_on_connected_geometric_fibre
    {S T : Scheme.{u}} (f : T ⟶ S)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (q : Spec (.of Ω) ⟶ S)
    [ConnectedSpace (pullback f q : Scheme.{u})]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (a : ((L f).obj F).obj.obj (op I[T])) :
    let D := pullback f f
    let g := pullback.fst f f ≫ f
    let E := pullback g q
    let d := pullback.fst g q
    let G := (L g).obj F
    R[D,E,d,G]
      (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S T (pullback f f) f (pullback.fst f f)).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback f f))))
        (((Scheme.etaleSetPullback (pullback.fst f f)).obj
            ((Scheme.etaleSetPullback f).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst f f) (𝟙 (pullback f f))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback f f)) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst f f)).obj
                (Scheme.Etale.mk (𝟙 T))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst f f)) _
            (T.smallGrothendieckTopology @Etale)
            ((pullback f f).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback f).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 T))) a))) =
    R[D,E,d,G]
      (Eq.mp (congrArg (fun k : pullback f f ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback f f)))))
          (pullback.condition (f := f) (g := f)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S T (pullback f f) f (pullback.snd f f)).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback f f))))
          (((Scheme.etaleSetPullback (pullback.snd f f)).obj
              ((Scheme.etaleSetPullback f).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd f f) (𝟙 (pullback f f))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback f f)) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd f f)).obj
                  (Scheme.Etale.mk (𝟙 T))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd f f)) _
              (T.smallGrothendieckTopology @Etale)
              ((pullback f f).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback f).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 T))) a)))) := by sorry

end AlgebraicGeometry
