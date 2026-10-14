/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent

/-!
# Blueprint statements

thm-galois-lc-etale.
-/

@[expose] public section

universe v w v₁ u₁

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D] (G : C ⥤ D)
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} [G.IsContinuous J K]
  [J.Subcanonical] [K.Subcanonical]

/-- A left adjoint `L` of the pushforward of sheaves along a continuous functor `G` sends the
sheaf represented by `U` to the sheaf represented by `G.obj U`: both corepresent `F ↦ F(G U)`. -/
noncomputable def uliftYonedaCompIsoOfAdjunction
    {L : Sheaf J (Type (max v₁ w)) ⥤ Sheaf K (Type (max v₁ w))}
    (adj : L ⊣ G.sheafPushforwardContinuous (Type (max v₁ w)) J K) :
    J.uliftYoneda.{w} ⋙ L ≅ G ⋙ K.uliftYoneda.{w} :=
  (NatIso.removeOp ((Coyoneda.fullyFaithful.whiskeringRight Cᵒᵖ).preimageIso
    (X := (J.uliftYoneda.{w} ⋙ L).op) (Y := (G ⋙ K.uliftYoneda.{w}).op)
    (isoWhiskerLeft (J.uliftYoneda.{w}).op adj.compCoyonedaIso ≪≫
      isoWhiskerRight J.uliftYonedaOpCompCoyoneda ((whiskeringLeft _ _ _).obj _) ≪≫
      NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)) ≪≫
      (isoWhiskerLeft G.op K.uliftYonedaOpCompCoyoneda).symm))).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- Base change of finite étale schemes along `f : X ⟶ Y` is base change on the small étale
sites, restricted to finite étale schemes. -/
noncomputable def FiniteEtale.pullbackCompιIso {X Y : Scheme.{v}} (f : X ⟶ Y) :
    FiniteEtale.pullback f ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ f.Etale :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun φ ↦ by
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext <;> simp [Hom.Etale]

/-- The étale sheaf of sets `Hom_Y(-, P)` represented by a finite étale `Y`-scheme `P` pulls back
along `f : X ⟶ Y` to the sheaf `Hom_X(-, P ×_Y X)` represented by the base change. -/
noncomputable def FiniteEtale.uliftYonedaCompEtaleSetPullbackIso {X Y : Scheme.{v}}
    (f : X ⟶ Y) :
    ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1} ⋙ etaleSetPullback f ≅
      FiniteEtale.pullback f ⋙ ObjectProperty.ι _ ⋙ X.smallEtaleTopology.uliftYoneda.{v + 1} :=
  Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (f.Etale.uliftYonedaCompIsoOfAdjunction
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)) ≪≫
    Functor.isoWhiskerRight (FiniteEtale.pullbackCompιIso f).symm
      X.smallEtaleTopology.uliftYoneda.{v + 1}

/-- Blueprint: thm-galois-lc-etale. Finite étale `Y`-schemes are equivalent to finite locally
constant étale sheaves of sets by `P ↦ Hom_Y(-, P)`, compatibly with geometric fibres and stalks
and with pullback along any morphism `f : X ⟶ Y`. -/
theorem exists_finiteEtale_flc_equivalence (Y : Scheme.{v}) :
    ∃ Φ : Y.FiniteEtale ≌ Y.FiniteLocallyConstant,
      Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
      (∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙
            (pointSmallEtale s).sheafFiber (A := Type (v + 1)) ≅
          FiniteEtale.fiber s ⋙ CategoryTheory.forget FintypeCat.{v} ⋙
            uliftFunctor.{v + 1, v})) ∧
      (∀ (X : Scheme.{v}) (f : X ⟶ Y), ∃ Ψ : X.FiniteEtale ≌ X.FiniteLocallyConstant,
        Nonempty (Ψ.functor ⋙ ObjectProperty.ι _ ≅
          ObjectProperty.ι _ ⋙ X.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙ etaleSetPullback f ≅
          FiniteEtale.pullback f ⋙ Ψ.functor ⋙ ObjectProperty.ι _)) := by
  refine ⟨FiniteEtale.equivalenceFiniteLocallyConstant Y, ⟨Iso.refl _⟩, fun Ω _ _ s ↦ ?_,
    fun X f ↦ ⟨FiniteEtale.equivalenceFiniteLocallyConstant X, ⟨Iso.refl _⟩, ?_⟩⟩
  · exact ⟨FiniteEtale.toFiniteLocallyConstantCompSheafFiberIso s⟩
  · exact ⟨FiniteEtale.uliftYonedaCompEtaleSetPullbackIso f⟩

/-- Blueprint: thm-galois-lc-etale. Under an equivalence `Φ` between finite étale `Y`-schemes
and finite locally constant sheaves identified with `P ↦ Hom_Y(-, P)` by `α`, the sheaf
attached to an `M`-torsor `P` is its sheaf torsor, with `m ∈ M` acting through `Φ` as
composition with the action of `m` on `P`. -/
theorem finiteEtale_flc_preserves_torsors {Y : Scheme.{v}}
    (Φ : Y.FiniteEtale ≌ Y.FiniteLocallyConstant)
    (α : Φ.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) :
    ∀ (M : Type (v + 1)) [AddCommGroup M] [Finite M] (t : EtaleTorsor M Y),
      ∃ ε : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj ≅ t.toSheafTorsor.sheaf,
        ε = α.app ⟨t.toEtale, t.isFinite⟩ ∧
        ∀ (U : Y.Etale) (m : M)
          (x : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj.obj.obj (op U)),
          ε.hom.hom.app (op U)
            ((Φ.functor.map (ObjectProperty.homMk
              (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)))).hom.hom.app (op U) x) =
            ⟨(ε.hom.hom.app (op U) x).down ≫
              MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)⟩ := by
  intro M _ _ t
  refine ⟨α.app _, rfl, fun U m x ↦ ?_⟩
  let g : (⟨t.toEtale, t.isFinite⟩ : Y.FiniteEtale) ⟶ ⟨t.toEtale, t.isFinite⟩ :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m))
  have h := congr_arg (fun φ ↦ φ.hom.app (op U)) (α.hom.naturality g)
  exact ConcreteCategory.congr_hom h x

end AlgebraicGeometry.Scheme
