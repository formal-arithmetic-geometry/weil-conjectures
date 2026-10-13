/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Algebraization of the completed affine comparison as an adjunction

Source: Stacks Project, Tag 088B, completed-base algebraization argument.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The completed affine comparison is the section map of an algebraized adjunction.
This supplies an algebraized source, a proper morphism and an isomorphism on its
pullback, together with the limit comparison square. It asserts no invertibility
of the comparison itself, either globally or on an open.

Source: Stacks Project, Tag 088B, proof, from flat completion base change through
algebraization of the formal pullback isomorphism; Tags 087W, 087X and 0883.
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-adjunction-model)

Proof: Restrict the original data to U=Spec B, and form the base change of f along
Spec R -> Spec B -> Y, where R is the J(U)-adic completion. Completion is flat,
Noetherian, and has the same positive ideal-power quotients as B. Flat base change
identifies pushforward, quotient projections and adjunction units. Since the
quotient projections are epimorphisms, hκ specifies their comparison uniquely;
formal functions identifies its inverse limit with an isomorphism. The equation
hα therefore determines the completed comparison on inverse limits. Algebraize
G over R by the affine formal-module equivalence, obtaining A₀, and pull back F
to obtain F₀ on the proper base-changed scheme Z. Pullback commutes with formal
completion. Full faithfulness of completion on the proper scheme Z lifts β and
its inverse to inverse coherent maps, giving b. Proper coherent pushforward
supplies hD. The affine limit cones and formal functions give eA₀ and eD₀;
naturality and hα identify the limit map with the sections of the adjunction unit
followed by p_*b. For an arbitrary supplied adjunction, first absorb the natural
automorphism relating it to the standard adjunction into β; it remains invertible.
The complement of the extended ideal is the inverse image of the original
complement of K, so p is an isomorphism there by stability under base change.
If R is zero, the spectrum is empty and the same constructions apply. -/
theorem formalComparison_completed_affine_adjunction_model
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (hα : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward f).map (β.hom.app (op n))) :
    ∀ U : Y.affineOpens,
      let B := Γ(Y, U.1)
      let R := AdicCompletion (J.ideal U) B
      let L := (K.ideal U).map (algebraMap B R)
      let Q := Scheme.IdealSheafData.ofIdealTop
        (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      ∃ (Z : Scheme.{u}) (p : Z ⟶ Spec (CommRingCat.of R))
        (adjR : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
        (A₀ : CoherentModules (Spec (CommRingCat.of R))) (F₀ : CoherentModules Z)
        (b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F₀.obj)
        (hD : RingedSpace.IsCoherent (Spec (CommRingCat.of R)).toRingedSpace
          ((Scheme.Modules.pushforward p).obj F₀.obj)),
        IsProper p ∧ IsIso (pullback.snd p (Scheme.Opens.ι Q.support.compl)) ∧
        ∃ eA₀ : limit (G.obj ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A₀.obj),
        ∃ eD₀ : limit (((completion Y J).obj
            ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
              SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj
                ((Scheme.Modules.pushforward p).obj F₀.obj)),
          lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫ eD₀.hom =
          eA₀.hom ≫ (ModuleCat.restrictScalars (algebraMap B R)).map
            ((moduleSpecΓFunctor (R := CommRingCat.of R)).map
              (adjR.unit.app A₀.obj ≫ (Scheme.Modules.pushforward p).map b.hom)) := by
  sorry

end AlgebraicGeometry
