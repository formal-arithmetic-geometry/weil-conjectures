/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Counit-normalized right adjoints on fixed pairs

Source: blueprint main-20261015, smooth purity, the smooth dualizing formula in
`cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md`; Stacks Project,
Tag 0037 (definition-adjoint); the categorical uniqueness proof in
`sk-prop-sp-unique-adjoint-categorical.proof.md`.
(blueprint: lem-pur-fixed-pair-right-adjoint-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- A carrier-normalized right adjoint has the mate-induced fixed structure, and any
other right adjoint admits a unique counit-compatible comparison with it.
The equality `hCarrier` expresses equality of carrier functors. Its `eqToIso`
components only transport morphisms between propositionally equal carriers.

Source: the smooth dualizing identification in blueprint main-20261015,
`cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md`; Stacks Tag 0037,
and `sk-prop-sp-unique-adjoint-categorical.proof.md`.
(blueprint: lem-pur-fixed-pair-right-adjoint-comparison)

Proof plan:
1. The fixed-pair morphism equation for the lifted counit, after identifying its
   carrier using hCarrier and hCounit, gives epsilon F(vartheta) beta = theta P(epsilon).
   Precompose with beta inverse. This uses def-weil-endofunctor-fixed-pair-category.
2. Naturality of epsilon at theta, followed by the counit equation for the mate
   e of beta inverse, gives the same composite for e followed by G(theta).
   This uses def-weil-pbc-adjunction-mate and mateEquiv_counit.
3. The inverse Hom equivalence of F adjoint G sends b to F(b) followed by epsilon.
   Its injectivity identifies the two structures. This is the transpose formula
   in lem-weil-pbc-adjunction-of-natural-bijection. Their inverse maps agree too,
   since both structure morphisms are isomorphisms.
4. Apply det-sp-unique-right-adjoint, with first right adjoint J and second
   right adjoint Gtilde. The counit equation uniquely characterizes the resulting
   natural isomorphism alpha, without any carrier identification on J.
5. Forget that equation and use hCounit to obtain the displayed carrier equation.
   The structure equality from step 3 makes the carrier identification an
   isomorphism of fixed pairs to (GK, G(theta) e). Compose it with alpha at B
   to obtain the final fixed-pair isomorphism. -/
theorem fixedPair_rightAdjoint_comparison
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {Q : C ⥤ C} {P : D ⥤ D} {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (β : F ⋙ P ≅ Q ⋙ F) (e : G ⋙ Q ≅ P ⋙ G)
    (hMate : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans = e.hom)
    (Gtilde : IsoAlgebra P ⥤ IsoAlgebra Q)
    (lifted : mapOfNatIso β ⊣ Gtilde)
    (hCarrier : Gtilde ⋙ forget Q = forget P ⋙ G)
    (hCounit : ∀ B : IsoAlgebra P,
      F.map ((eqToIso hCarrier).inv.app B) ≫ (lifted.counit.app B).hom.f =
        adj.counit.app B.carrier) :
    (∀ B : IsoAlgebra P,
      Q.map ((eqToIso hCarrier).inv.app B) ≫ (Gtilde.obj B).str.hom ≫
          (eqToIso hCarrier).hom.app B = e.hom.app B.carrier ≫ G.map B.str.hom) ∧
    (∀ (J : IsoAlgebra P ⥤ IsoAlgebra Q) (adjJ : mapOfNatIso β ⊣ J),
      ∃! α : J ≅ Gtilde,
        (∀ B : IsoAlgebra P,
          (mapOfNatIso β).map (α.hom.app B) ≫ lifted.counit.app B = adjJ.counit.app B) ∧
        (∀ B : IsoAlgebra P,
          F.map ((α.hom.app B).hom.f ≫ (eqToIso hCarrier).hom.app B) ≫
            adj.counit.app B.carrier = (adjJ.counit.app B).hom.f) ∧
        (∀ B : IsoAlgebra P,
          Nonempty (J.obj B ≅ mk (G.obj B.carrier) (e.app B.carrier ≪≫ G.mapIso B.str)))) := by
  let t (B : IsoAlgebra P) : (Gtilde.obj B).carrier ≅ G.obj B.carrier :=
    (eqToIso hCarrier).app B
  have hc (B : IsoAlgebra P) :
      F.map (t B).hom ≫ adj.counit.app B.carrier =
        (lifted.counit.app B).hom.f := by
    rw [← hCounit B, ← F.map_comp_assoc]
    simp [t]
  have hs (B : IsoAlgebra P) :
      Q.map (t B).inv ≫ (Gtilde.obj B).str.hom ≫ (t B).hom =
        e.hom.app B.carrier ≫ G.map B.str.hom := by
    apply (adj.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, F.map_comp, Category.assoc]
    change F.map (Q.map (t B).inv) ≫ F.map (Gtilde.obj B).str.hom ≫
      F.map (t B).hom ≫ adj.counit.app B.carrier =
        F.map (e.hom.app B.carrier) ≫ F.map (G.map B.str.hom) ≫
          adj.counit.app B.carrier
    rw [hc]
    have hw := (lifted.counit.app B).hom.h
    change P.map (lifted.counit.app B).hom.f ≫ B.str.hom =
      (β.hom.app (Gtilde.obj B).carrier ≫ F.map (Gtilde.obj B).str.hom) ≫
        (lifted.counit.app B).hom.f at hw
    have hn := β.inv.naturality (t B).inv
    change F.map (Q.map (t B).inv) ≫ β.inv.app (Gtilde.obj B).carrier =
      β.inv.app (G.obj B.carrier) ≫ P.map (F.map (t B).inv) at hn
    have hm := mateEquiv_counit adj adj (TwoSquare.mk _ _ _ _ β.inv) B.carrier
    change F.map ((mateEquiv adj adj (TwoSquare.mk _ _ _ _ β.inv)).natTrans.app _) ≫
      adj.counit.app (P.obj B.carrier) =
        β.inv.app (G.obj B.carrier) ≫ P.map (adj.counit.app B.carrier) at hm
    rw [hMate] at hm
    calc
      _ = β.inv.app (G.obj B.carrier) ≫ P.map (F.map (t B).inv) ≫
          β.hom.app (Gtilde.obj B).carrier ≫ F.map (Gtilde.obj B).str.hom ≫
            (lifted.counit.app B).hom.f := by
        rw [← reassoc_of% hn]
        simp
      _ = β.inv.app (G.obj B.carrier) ≫
          P.map (F.map (t B).inv ≫ (lifted.counit.app B).hom.f) ≫ B.str.hom := by
        rw [P.map_comp, Category.assoc, hw]
        simp only [Category.assoc]
      _ = β.inv.app (G.obj B.carrier) ≫ P.map (adj.counit.app B.carrier) ≫
          B.str.hom := by
        have hi : F.map (t B).inv ≫ (lifted.counit.app B).hom.f =
            adj.counit.app B.carrier := hCounit B
        rw [hi]
      _ = F.map (e.hom.app B.carrier) ≫ F.map (G.map B.str.hom) ≫
          adj.counit.app B.carrier := by
        rw [← reassoc_of% hm]
        congr 1
        exact (adj.counit.naturality B.str.hom).symm
  refine ⟨hs, ?_⟩
  intro J adjJ
  refine ⟨adjJ.rightAdjointUniq lifted, ?_, ?_⟩
  · refine ⟨fun B ↦ adjJ.rightAdjointUniq_hom_app_counit lifted B, ?_, ?_⟩
    · intro B
      change F.map (((adjJ.rightAdjointUniq lifted).hom.app B).hom.f ≫ (t B).hom) ≫
        adj.counit.app B.carrier = (adjJ.counit.app B).hom.f
      rw [F.map_comp, Category.assoc, hc]
      exact congrArg (fun f ↦ f.hom.f) (adjJ.rightAdjointUniq_hom_app_counit lifted B)
    · intro B
      refine ⟨(adjJ.rightAdjointUniq lifted).app B ≪≫
        ObjectProperty.isoMk _ (Algebra.isoMk (t B) ?_)⟩
      change Q.map (t B).hom ≫
        (e.hom.app B.carrier ≫ G.map B.str.hom) =
          (Gtilde.obj B).str.hom ≫ (t B).hom
      rw [← hs B, ← Q.map_comp_assoc]
      simp
  · intro α hα
    apply Iso.ext
    ext B
    apply (lifted.homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit] using
      (hα.1 B).trans (adjJ.rightAdjointUniq_hom_app_counit lifted B).symm

end CategoryTheory.Endofunctor.IsoAlgebra
