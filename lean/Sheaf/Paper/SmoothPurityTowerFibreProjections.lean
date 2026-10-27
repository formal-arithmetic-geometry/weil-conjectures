/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.CategoryTheory.RingedToposBinaryDescentDefs

/-! # Local projections from a coefficient-tower fibre

Source: Stacks Project, Cohomology, Tag 08DG, restricted fibre calculation;
blueprint det-sp-tower-gluing, Gluing paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : Base l E) (o : Operations l E b)

/-- The counit projections from any distinguished binary direct-image fibre are
invertible on their respective opens. A covering hypothesis and finite-level
bounds are unnecessary for this restricted calculation.

Source: Stacks Project, Cohomology, Tag 08DG (lemma-glue), and the retained
proof of lem-sp-tower-binary-ctf-fibre, steps 1--2
(blueprint: lem-sp-tower-fibre-projections).

Proof: present the tower category by its ordinary ringed sequence site, as in
sequenceSiteOpenExtension. The constant representable open subterminal has
slice category the sequence site on the localized pro-etale site. The slice
site equivalence and the constant-section ring comparison preserve every
quotient transition, so transport the ordinary module restrictions and their
right adjoints to the displayed geometric operations. Termwise localization
transports these comparisons to the ordinary derived categories; the specified
adjunctions give their counits by uniqueness of right adjoints. The composition
comparison is the specified one, since comp_termwise and comp_evaluation identify
it on every complex and every coefficient level with ordinary nested restriction.
Apply ringedTopos_fibre_restriction in these coordinates. Explicitly, on U the
restricted middle map is (h,-1) after the direct-image base-change identifications;
on V it is (c,-r), with the first component invertible. Each map is split epic,
its fibre is the graph of the other component, and projection to P, respectively
Q, is invertible. This calculation is valid also for empty opens and zero inputs.
No assertion about constructibility, Tor amplitude or covering is used. -/
theorem tower_fibre_projections
    (Z : Scheme.{u}) (U V : Z.Opens)
    (P : D l E U.toScheme) (Q : D l E V.toScheme)
    (c : (pull l E b (o.geometry (Z.homOfLE (inf_le_left : U ⊓ V ≤ U)))).obj P ≅
      (pull l E b (o.geometry (Z.homOfLE (inf_le_right : U ⊓ V ≤ V)))).obj Q) :
    let compU := (o.comp (Z.homOfLE (inf_le_left : U ⊓ V ≤ U)) U.ι ≪≫
      eqToIso (congrArg (fun f ↦ pull l E b (o.geometry f))
        (Z.homOfLE_ι (inf_le_left : U ⊓ V ≤ U)))).symm
    let compV := (o.comp (Z.homOfLE (inf_le_right : U ⊓ V ≤ V)) V.ι ≪≫
      eqToIso (congrArg (fun f ↦ pull l E b (o.geometry f))
        (Z.homOfLE_ι (inf_le_right : U ⊓ V ≤ V)))).symm
    let d := biprod.desc
      (restrictionAdjunctionMap (adjunction l E b (o.geometry U.ι))
        (adjunction l E b (o.geometry (U ⊓ V).ι)) compU P ≫
          (push l E b (o.geometry (U ⊓ V).ι)).map c.hom)
      (-restrictionAdjunctionMap (adjunction l E b (o.geometry V.ι))
        (adjunction l E b (o.geometry (U ⊓ V).ι)) compV Q)
    ∀ (G : D l E Z)
      (f : G ⟶ (push l E b (o.geometry U.ι)).obj P ⊞
        (push l E b (o.geometry V.ι)).obj Q)
      (δ : (push l E b (o.geometry (U ⊓ V).ι)).obj
        ((pull l E b (o.geometry (Z.homOfLE (inf_le_right : U ⊓ V ≤ V)))).obj Q) ⟶
          (shiftFunctor _ (1 : ℤ)).obj G),
      Triangle.mk f d δ ∈ distTriang _ →
        IsIso ((pull l E b (o.geometry U.ι)).map f ≫
          (pull l E b (o.geometry U.ι)).map biprod.fst ≫
            (adjunction l E b (o.geometry U.ι)).counit.app P) ∧
        IsIso ((pull l E b (o.geometry V.ι)).map f ≫
          (pull l E b (o.geometry V.ι)).map biprod.snd ≫
            (adjunction l E b (o.geometry V.ι)).counit.app Q) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
