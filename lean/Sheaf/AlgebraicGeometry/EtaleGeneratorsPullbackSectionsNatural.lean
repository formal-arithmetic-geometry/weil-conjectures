/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections
import WeilConjectures.AlgebraicGeometry.Modules.AffineDescent
import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSourceComparison
import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackTargetComparison

/-! # Naturality of pulled-back generator sections

Source: Stacks Project, Tags 040E and 0097.
(blueprint: lem-sc-etale-generators-pullback-sections-natural)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

private theorem compose_comparison_squares {C : Type*} [Category* C]
    {A B D E F G H I J : C} (c₀ : B ≅ A) (c₁ : I ≅ J) (k₀ : D ≅ E) (k₁ : G ≅ H)
    (a : B ⟶ D) (m : D ⟶ G) (b : G ⟶ I)
    (a₁ : A ⟶ F) (a₂ : F ⟶ E) (m' : E ⟶ H) (b' : H ⟶ J)
    (ha : c₀.inv ≫ a ≫ k₀.hom = a₁ ≫ a₂)
    (hm : m ≫ k₁.hom = k₀.hom ≫ m')
    (hb : k₁.inv ≫ b ≫ c₁.hom = b') :
    c₀.inv ≫ a ≫ m ≫ b ≫ c₁.hom = a₁ ≫ a₂ ≫ m' ≫ b' := by
  calc
    _ = (c₀.inv ≫ a ≫ k₀.hom) ≫ (k₀.inv ≫ m ≫ k₁.hom) ≫
        (k₁.inv ≫ b ≫ c₁.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = a₁ ≫ a₂ ≫ m' ≫ b' := by
      rw [ha, hb, hm]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem section_hom {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)]
    (U : X.Etale) (t : (etaleIsoTorsor L).sheaf.obj.obj (op U)) :
    (etaleGeneratorsPullbackSection f L U t).down.1 =
      (etaleGeneratorsPullbackSourceIso f U).hom ≫ (pullback (Limits.pullback.fst U.hom f)).map
        t.down.1 ≫
      (etaleGeneratorsPullbackTargetIso f U L).hom := by
  simp only [etaleGeneratorsPullbackSection, etaleGeneratorsPullbackSourceIso,
    etaleGeneratorsPullbackTargetIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]

private theorem naturality_hom {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    {V W : X.Etale} (i : V ⟶ W)
    (t : (pullback W.hom).obj (unit X) ⟶ (pullback W.hom).obj L) :
    (pullbackCompOfEq ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
          (Limits.pullback.snd W.hom f) (Limits.pullback.snd V.hom f)
          ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).w (unit Y)).inv ≫ (pullback
            ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).map
            (etaleGeneratorsPullbackSourceIso f W).hom ≫
        (pullback ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).map ((pullback
          (Limits.pullback.fst W.hom f)).map t) ≫
        (pullback ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).map
          (etaleGeneratorsPullbackTargetIso f W L).hom ≫ (pullbackCompOfEq
          ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
          (Limits.pullback.snd W.hom f) (Limits.pullback.snd V.hom f)
          ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).w ((tensorPullback f).obj L)).hom =
      (etaleGeneratorsPullbackSourceIso f V).hom ≫ (pullback (Limits.pullback.fst V.hom f)).map
        (pullbackCompOfEq i.left W.hom V.hom i.w (unit X)).inv ≫
        (pullback (Limits.pullback.fst V.hom f)).map ((pullback i.left).map t) ≫
        (pullback (Limits.pullback.fst V.hom f)).map (pullbackCompOfEq i.left W.hom V.hom i.w
          L).hom ≫ (etaleGeneratorsPullbackTargetIso f V L).hom := by
  have hn : (pullback ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).map ((pullback
    (Limits.pullback.fst W.hom f)).map t) ≫
      (etaleGeneratorsPullbackSquareIso f i ((pullback W.hom).obj L)).hom =
      (etaleGeneratorsPullbackSquareIso f i ((pullback W.hom).obj (unit X))).hom ≫
        (pullback (Limits.pullback.fst V.hom f)).map ((pullback i.left).map t) := by
    let hp : ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left ≫ Limits.pullback.fst
      W.hom f =
        Limits.pullback.fst V.hom f ≫ i.left := by
      simp [MorphismProperty.Over.pullback_map_left]
    let e : pullback (Limits.pullback.fst W.hom f) ⋙ pullback ((MorphismProperty.Over.pullback
      @Etale ⊤ f).map i).left ≅
        pullback i.left ⋙ pullback (Limits.pullback.fst V.hom f) :=
      (pullbackComp ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
        (Limits.pullback.fst W.hom f) ≪≫ pullbackCongr hp) ≪≫
        (pullbackComp (Limits.pullback.fst V.hom f) i.left).symm
    exact e.hom.naturality t
  have hs := etaleGeneratorsPullbackSource_naturality f i
  have ht := etaleGeneratorsPullbackTarget_naturality f L i
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      exact compose_comparison_squares _ _ _ _ _ _ _ _ _ _ _ hs hn ht

/-- Pulling back generator sections commutes with etale restrictions.
Source: Stacks Project, Tag 0097 (composition of pullbacks), Tag 040E (generators).
(blueprint: lem-sc-etale-generators-pullback-sections-natural)

Proof: Expand restriction in the presheaf of isomorphisms as conjugation by the
module pseudofunctor's composition constraints. Expand the section map as the
pullback of the trivialisation along the first projection, conjugated by the
structure-module and tensor-comparison isomorphisms. The pullback square for a
map of etale objects commutes. The associativity coherence for module pullback
then identifies the two composite comparison maps; naturality of the structure
module comparison and of the left-adjoint comparison identifies their outer
factors. The middle factors agree by functoriality of module pullback. Thus the
underlying homomorphisms agree, and subtype and ULift extensionality give equality
of generator sections. This argument includes empty objects and zero rings.
-/
theorem etaleGeneratorsPullbackSection_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)]
    {V W : X.Etale} (i : V ⟶ W)
    (s : (etaleIsoTorsor L).sheaf.obj.obj (op W)) :
    (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf.obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).op
      (etaleGeneratorsPullbackSection f L W s) =
    etaleGeneratorsPullbackSection f L V ((etaleIsoTorsor L).sheaf.obj.map i.op s) := by
  apply ULift.ext
  apply Subtype.ext
  dsimp only [etaleIsoTorsor, Functor.comp_map, uliftFunctor, Subfunctor.toFunctor,
    etaleIso, Pseudofunctor.presheafIso, Pseudofunctor.presheafHom]
  simp only [TypeCat.ofHom_apply, etaleHom, Functor.comp_map,
    Pseudofunctor.presheafHom_map]
  dsimp only [Functor.op_map, Functor.op_obj, Functor.comp_obj, Functor.comp_map]
  simp only [section_hom f L]
  conv_rhs =>
    enter [2, 1]
    rw [modulesPseudofunctor_pullHom_eq_pullbackCompOfEq]
  rw [modulesPseudofunctor_pullHom_eq_pullbackCompOfEq]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Quiver.Hom.unop_op, unitObj]
  set_option backward.isDefEq.respectTransparency true in
    exact naturality_hom f L i s.down.1

end AlgebraicGeometry.Scheme.Modules
