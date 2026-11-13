/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescent
import WeilConjectures.AlgebraicGeometry.GabberH0EtaleInjective
import WeilConjectures.AlgebraicGeometry.GabberH0FiniteLift
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Gabber's degree-zero criterion for etale sheaves of sets

## References

* Stacks Project, Lemma 59.82.2 (Tag 09ZF).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem comparison_unit {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : F.obj.obj (op U)) :
    etaleSetDescentComparison f g F U (etaleSetDescentUnit f F U s) =
      etaleSetDescentUnit (g ≫ f) F U s := by
  have h := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
    X Y W f g F U s
  unfold etaleSetDescentComparison
  erw [h]
  simp [etaleSetDescentUnit, ← Functor.map_comp_apply, ← op_comp]

private theorem unit_injective_terminal {Y W : Scheme.{u}}
    (g : W ⟶ Y) [IsFinite g] [Surjective g]
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (U : Y.Etale) (hU : IsTerminal U) :
    Function.Injective (etaleSetDescentUnit g G U) := by
  let e : U ≅ Scheme.Etale.mk (𝟙 Y) :=
    hU.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @Etale Y)
  intro s t h
  have he : G.obj.map e.inv.op s = G.obj.map e.inv.op t := by
    apply (finiteSurjectiveSetDescent g G).1
    have hn := etaleSetInverseImageCompositionUnits.1 Y W g G U
      (Scheme.Etale.mk (𝟙 Y)) e.inv
    change _ = _
    rw [show etaleSetDescentUnit g G (Scheme.Etale.mk (𝟙 Y))
      (G.obj.map e.inv.op s) = _ from hn s]
    rw [show etaleSetDescentUnit g G (Scheme.Etale.mk (𝟙 Y))
      (G.obj.map e.inv.op t) = _ from hn t]
    exact congrArg
      (((Scheme.etaleSetPullback g).obj G).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ g).map e.inv).op) h
  have he' := congrArg (G.obj.map e.hom.op) he
  simpa [← Functor.map_comp_apply, ← op_comp] using he'

private theorem comparison_injective {X Y W : Scheme.{u}}
    (f : Y ⟶ X) (g : W ⟶ Y) [IsFinite g] [Surjective g]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Function.Injective (etaleSetDescentComparison f g F (Scheme.Etale.mk (𝟙 X))) := by
  let U := (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 X))
  have hU : IsTerminal U :=
    (MorphismProperty.Over.mkIdTerminal @Etale X).isTerminalObj
      (MorphismProperty.Over.pullback @Etale ⊤ f) _
  have hi := unit_injective_terminal g ((Scheme.etaleSetPullback f).obj F) U hU
  intro s t h
  apply hi
  let c := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
    X Y W f g).app F
  let e := ((Scheme.etaleSetPullback (g ≫ f)).obj F).obj.mapIso
    (((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).app
      (Scheme.Etale.mk (𝟙 X))).op)
  have h₁ := congrArg e.inv h
  have h₂ :
      c.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj U))
        (etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj F) U s) =
      c.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj U))
        (etaleSetDescentUnit g ((Scheme.etaleSetPullback f).obj F) U t) := by
    simpa [c, U, e, etaleSetDescentComparison, ← Functor.map_comp_apply, ← op_comp] using h₁
  let d := (sheafToPresheaf _ _).mapIso c
  have h₃ := congrArg (d.inv.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj U))) h₂
  simpa [d, ← NatTrans.comp_app, ← types_comp_apply] using h₃


private theorem unit_transport {X W : Scheme.{u}} (a b : W ⟶ X) (e : a = b)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : F.obj.obj (op U)) :
    eqToHom (congrArg
      (fun k : W ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))) e)
      (etaleSetDescentUnit a F U s) = etaleSetDescentUnit b F U s := by
  subst b
  rfl

/-- If Zariski restriction to a closed subscheme is bijective on sections for every
set-valued sheaf, and remains so after every finite base change, then etale restriction
is bijective on sections for every set-valued sheaf. (Stacks, Tag 09ZF) -/
theorem gabber_h0_etale_criterion
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZar :
      letI : ∀ P : X.Opensᵒᵖ ⥤ Type (u + 1),
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)).op.HasPointwiseLeftKanExtension P :=
            fun P U ↦
              @Types.hasColimit.{u, u + 1, u}
                (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
                inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat,
      Function.Bijective
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)) (Type (u + 1))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom.app
            (op (⊤ : X.Opens))))
    (hFinite : ∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h],
      let b : CategoryTheory.Functor.{u, u, u, u} X'.Opens (pullback i h : Scheme.{u}).Opens :=
        Opens.map
        ((pullback.snd i h : (pullback i h : Scheme.{u}) ⟶ X').base)
      letI : ∀ P : X'.Opensᵒᵖ ⥤ Type (u + 1), b.op.HasPointwiseLeftKanExtension P :=
        fun P U ↦
          @Types.hasColimit.{u, u + 1, u} (CostructuredArrow.{u, u, u, u} b.op U)
            inferInstance (small_succ.{u} _) (CostructuredArrow.proj b.op U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X'.toTopCat,
        Function.Bijective
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            b (Type (u + 1)) (Opens.grothendieckTopology X')
            (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).unit.app G).hom.app
              (op (⊤ : X'.Opens))))
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    let adj : Scheme.etaleSetPullback i ⊣
        (MorphismProperty.Over.pullback @Etale ⊤ i).sheafPushforwardContinuous
          (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
          (Z.smallGrothendieckTopology @Etale) :=
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)
    Function.Bijective ((adj.unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 X)))) := by
  change Function.Bijective (etaleSetDescentUnit i F (Scheme.Etale.mk (𝟙 X)))
  refine ⟨gabber_h0_etale_injective i hZar F, ?_⟩
  intro t
  obtain ⟨X', h, hh, hsurj, s', heq, hres⟩ := gabber_h0_finite_lift i hZar hFinite F t
  let : IsFinite h := hh
  let : Surjective h := hsurj
  obtain ⟨s, hs⟩ := ((finiteSurjectiveSetDescent h F).2 s').mp heq
  refine ⟨s, ?_⟩
  apply comparison_injective i (pullback.fst i h) F
  have hc := (comparison_unit h (pullback.snd i h) F (Scheme.Etale.mk (𝟙 X)) s).symm
  have hr := hc.trans (congrArg
    (etaleSetDescentComparison h (pullback.snd i h) F (Scheme.Etale.mk (𝟙 X))) hs)
  have hr' := congrArg (eqToHom (congrArg
    (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj (Scheme.Etale.mk (𝟙 X)))))
    (pullback.condition (f := i) (g := h)).symm)) hr
  exact (comparison_unit i (pullback.fst i h) F _ s).trans
    ((unit_transport _ _ (pullback.condition (f := i) (g := h)).symm F _ s).symm.trans
      (hr'.trans hres.symm))

end AlgebraicGeometry
