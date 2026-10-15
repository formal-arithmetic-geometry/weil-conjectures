/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Geometric stalks of étale sum extension

Source: Stacks Project, Tag 03S5, `proposition-describe-jshriek`, and Tag 0710,
`lemma-stalk-j-shriek` (blueprint: lem-amb-etale-sum-stalks).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace AlgebraicGeometry

open Classical in
/-- The natural linear stalk isomorphism for étale sum extension, including its formula
on the germ of each summand section. The index `Over.mk x ⟶ Over.mk u` is precisely
all lifts of the fixed geometric point, with the same algebraically closed field.
Source: Stacks Project, Tags 03S5 and 0710 (blueprint: lem-amb-etale-sum-stalks).

Proof: (1) Write P(V) as the direct sum of F(V,a). Its stalk L maps isomorphically to
that of its sheafification by `lem-weil-pbc-sheafification-geometric-stalk` and the
module sheafification construction `def-weil-presheaf-modules-sheafification`.
The unit and its inverse are linear. (2) Send the a-summand at (V,v) to the germ
in the lift a(v). Étale cancellation (`lem-weil-pbc-etale-composition-cancellation`)
and the stalk colimit relations (`def-weil-pbc-geometric-stalks`,
`def-weil-pbc-category-colimit`) make this a compatible cocone, hence a map from L.
(3) Conversely, a neighbourhood over U composes with u to a neighbourhood over X.
Place each section in its structure-map summand of P; these maps respect refinement,
so induce maps from every lift stalk to L, hence from their direct sum.
(4) Both composites are identities on every section germ, hence on stalks by the
colimit universal property and on sums by finite support.
(5) Compose with the inverse sheafification stalk map. This gives the displayed
section formula. Both sides of the naturality square send every section to the
same germ of its image, proving naturality by finite sums and the colimit property.
The sum presheaf throughout is `def-weil-pbc-etale-sum-extension`.
-/
theorem Etale.exists_etaleSumStalksIso
    {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    (A : Type (u + 1)) [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ e : ∀ F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
      (((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).obj F)) ≃ₗ[A]
      (⨁ (z : Over.mk x ⟶ Over.mk u),
        ((Scheme.pointSmallEtale z.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj F),
      (∀ (F G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (α : F ⟶ G)
        (s : ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).obj F)),
        e G (((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).map
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).map α) s) =
        DirectSum.lmap (fun z : Over.mk x ⟶ Over.mk u =>
          (((Scheme.pointSmallEtale z.left).sheafFiber
            (A := ModuleCat.{u + 1} A)).map α).hom) (e F s)) ∧
      (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
        (v : Over.mk x ⟶ (Scheme.Etale.forget X).obj
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).obj W))
        (s : F.obj.obj (op W)),
        e F
          ((Scheme.pointSmallEtale x).toPresheafFiber
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).obj W) v
            ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).obj F).obj
            ((toSheafify X.smallEtaleTopology
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).op.lan.obj F.obj)).app
                (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).obj W))
              (((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).op.lanUnit.app
                F.obj).app (op W) s))) =
        DirectSum.lof A
          (Over.mk x ⟶ Over.mk u)
          (fun z : Over.mk x ⟶ Over.mk u =>
            ((Scheme.pointSmallEtale z.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj F)
          (v ≫ Over.homMk W.hom)
          ((Scheme.pointSmallEtale (v.left ≫ W.hom)).toPresheafFiber W
            (Over.homMk v.left) F.obj s)) := by
  sorry

end AlgebraicGeometry
