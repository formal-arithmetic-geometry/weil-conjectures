/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Topology.ClosedImmersionPushforwardExact
public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Direct image of an extension and its fibre torsor

Source: Stacks Project, Cohomology of Sheaves, Tags 02UV and 02FQ, and Sheaves of Modules,
Tag 01AX (blueprint: lem-sc-torsor-h1-ext-pushforward).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

/-- Direct image of an extension, pulled back along restriction of constant integer
sections, has fibre torsor canonically equal to the direct image of the original fibre.
The isomorphism is specified on sections by the first projection of the pullback, and it
commutes with translation by the direct-image group sheaf.
Source: Stacks Project, Tags 02UV, 02FQ and 01AX
(blueprint: lem-sc-torsor-h1-ext-pushforward).

Proof:
1. Identify the closed immersion with its closed image. Apply
`lem-sc-closed-immersion-pushforward-exact` to the original short exact sequence, obtaining
short exactness of its direct image. Restriction sends a constant integer to the same
integer on the inverse-image open. Pull back the sequence along this restriction map:
the kernel embeds by the unique map whose projections are the original inclusion and zero,
and epimorphy of the second projection follows from local lifting along the original
projection. This gives the asserted short exact pullback sequence.
2. On an open U, a lift of 1 in the pullback is a pair (e,1), where e is a section over
its inverse image and p(e)=1. First projection therefore identifies these lifts with
sections of the original fibre over the inverse-image open. These bijections commute with
restriction. They commute with translation because the kernel inclusion has first
projection equal to the pushed-forward inclusion. Consequently they form the canonical
isomorphism of torsors asserted in the statement (`def-sc-gm-torsor`, `def-sc-zariski-site`
and `def-sc-topological-abelian-cohomology`). -/
theorem closedImmersion_extension_fibre_pushforward
    (Z X : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (F E : Z.carrier.Sheaf AddCommGrpCat.{u})
    (a : F ⟶ E)
    (p : E ⟶ (constantSheaf (Opens.grothendieckTopology Z.carrier)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (w : a ≫ p = 0) (hS : (ShortComplex.mk a p w).ShortExact) :
    (ShortComplex.map (ShortComplex.mk a p w)
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base)).ShortExact ∧
    ∃ r : (constantSheaf (Opens.grothendieckTopology X.carrier)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj
          ((constantSheaf (Opens.grothendieckTopology Z.carrier)
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))),
      (∀ (U : Opens X.carrier) (n : ℤ),
        r.hom.app (op U) ((toSheafify (Opens.grothendieckTopology X.carrier)
          ((Functor.const (Opens X.carrier)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op U) ⟨n⟩) =
          (toSheafify (Opens.grothendieckTopology Z.carrier)
            ((Functor.const (Opens Z.carrier)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
                (op ((Opens.map i.base).obj U)) ⟨n⟩) ∧
      ∃ k : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj F ⟶
          pullback ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map p) r,
        k ≫ pullback.fst _ _ =
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map a ∧
        ∃ hk : k ≫ pullback.snd _ _ = 0,
          ∃ hP : (ShortComplex.mk k (pullback.snd _ _) hk).ShortExact,
            ∃ e : (lifts (isTerminalTop : IsTerminal (⊤ : Opens X.carrier)) hP
                ((toSheafify (Opens.grothendieckTopology X.carrier)
                  ((Functor.const (Opens X.carrier)ᵒᵖ).obj
                    (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).sheaf ≅
                (TopCat.Sheaf.pushforward (Type u) i.base).obj
                  (lifts (isTerminalTop : IsTerminal (⊤ : Opens Z.carrier)) hS
                    ((toSheafify (Opens.grothendieckTopology Z.carrier)
                      ((Functor.const (Opens Z.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).sheaf,
              (∀ (U : Opens X.carrier)
                  (t : (lifts (isTerminalTop : IsTerminal (⊤ : Opens X.carrier)) hP
                    ((toSheafify (Opens.grothendieckTopology X.carrier)
                      ((Functor.const (Opens X.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).sheaf.obj.obj (op U)),
                (e.hom.hom.app (op U) t).val = (pullback.fst
                  ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map p) r).hom.app
                    (op U) t.val) ∧
              (∀ (U : Opens X.carrier)
                  (g : ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj F).obj.obj
                    (op U))
                  (t : (lifts (isTerminalTop : IsTerminal (⊤ : Opens X.carrier)) hP
                    ((toSheafify (Opens.grothendieckTopology X.carrier)
                      ((Functor.const (Opens X.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).sheaf.obj.obj (op U)),
                e.hom.hom.app (op U)
                  ((lifts (isTerminalTop : IsTerminal (⊤ : Opens X.carrier)) hP
                    ((toSheafify (Opens.grothendieckTopology X.carrier)
                      ((Functor.const (Opens X.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).vadd (op U) g t) =
                  (lifts (isTerminalTop : IsTerminal (⊤ : Opens Z.carrier)) hS
                    ((toSheafify (Opens.grothendieckTopology Z.carrier)
                      ((Functor.const (Opens Z.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).vadd
                          (op ((Opens.map i.base).obj U)) g (e.hom.hom.app (op U) t)) := by
  sorry

end CategoryTheory.Sheaf.Torsor
