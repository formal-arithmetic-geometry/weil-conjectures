/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.GabberH0ZariskiConstructions
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # The canonical section comparison and the étale unit

Source: Stacks Project, Tag 09ZF, pullback-functoriality paragraph and fourth proof paragraph;
Sites, Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-gabber-h0-zariski-section-unit-equation).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Core section-isomorphism/unit identity used by the top-open comparison.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph.
(blueprint: lem-weil-pbc-gabber-h0-zariski-section-unit-equation).
Proof: Write f = pullback.snd i h, B for base change along f, K = f*h*F,
p = gabberPreimageEtaleIso f top, b = gabberTopPullbackIso h, and a for the
first étale-object isomorphism in gabberZariskiSectionIso. Then
 a.inv ≫ p.hom = B.map b.inv.
To prove this equality, forget to schemes and compare the two pullback projections.
The projection to X' is forced by the morphisms over the base. The projection to
the top-open subscheme is forced because its inclusion is an isomorphism. Thus
pullback uniqueness gives the equality, also when a scheme is empty.
Contravariant functoriality of K gives
 K.map a.inv.op (K.map p.hom.op q) = K.map (B.map b.inv).op q.
Apply this to q = the étale unit at the top-open object. Naturality of that unit
identifies the last expression with the unit at the identity-pullback object
applied to h*F.map b.inv.op s, which is gabberZariskiLift h F s. The remaining
factors of gabberZariskiSectionIso are the chosen composition-isomorphism
component, pullbackComp, and transport along pullback.condition.symm. These
are exactly the three factors in the right side after unfolding
etaleSetDescentComparison. Evaluate on every section and use function
extensionality. This argument needs no closedness or finiteness assumption. -/
theorem gabber_h0_zariski_section_unit_equation
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    gabberZariskiCompare i h F ∘
      (((Scheme.etaleSetPullback (pullback.snd i h)).obj
        ((Scheme.etaleSetPullback h).obj F)).obj.map
          (gabberPreimageEtaleIso (pullback.snd i h) ⊤).hom.op) ∘
      (etaleSetDescentUnit (pullback.snd i h)
        ((Scheme.etaleSetPullback h).obj F) (Scheme.Etale.mk (⊤ : X'.Opens).ι)) =
      fun s : (gabberZariskiG h F).obj.obj (op (⊤ : X'.Opens)) ↦
        eqToHom (congrArg
          (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd i h) F
            (Scheme.Etale.mk (𝟙 X)) (gabberZariskiLift h F s)) := by sorry

end AlgebraicGeometry
