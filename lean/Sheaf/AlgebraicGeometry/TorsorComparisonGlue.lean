/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleComparisonTorsor
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence

/-! # Gluing the etale models of a torsor

Source: the current blueprint, sec-proetale-coefficients/sk-lem-pe-torsor-comparison,
`sk-lem-pe-torsor-comparison-glue.md`; Stacks Project, Tag 099X
(blueprint: det-pe-torsor-comparison-glue).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

private noncomputable def comparisonUnit {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) :
    F.obj.obj (Opposite.op U) →
      ((comparisonSets X).obj F).obj.obj (Opposite.op ((Scheme.toProEt X).obj U)) :=
  ((Scheme.proEtaleSiteComparison X).unit.app F).hom.app (Opposite.op U)

private theorem comparison_unit_product {X : Scheme.{u}}
    (F H : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (s : F.obj.obj (Opposite.op U)) (t : H.obj.obj (Opposite.op U)) :
    (comparisonProduct F H).hom.hom.app (Opposite.op ((Scheme.toProEt X).obj U))
        (comparisonUnit (F ⊗ H) U (s, t)) =
      (comparisonUnit F U s, comparisonUnit H U t) := by
  apply Prod.ext
  · have hn := congrArg (fun k ↦ k.hom.app (Opposite.op U) (s, t))
      ((Scheme.proEtaleSiteComparison X).unit.naturality
        (CartesianMonoidalCategory.fst F H))
    exact hn.symm
  · have hn := congrArg (fun k ↦ k.hom.app (Opposite.op U) (s, t))
      ((Scheme.proEtaleSiteComparison X).unit.naturality
        (CartesianMonoidalCategory.snd F H))
    exact hn.symm

private theorem comparison_unit_mul {X : Scheme.{u}}
    (G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (U : X.Etale)
    (g h : G₀.obj.obj (Opposite.op U)) :
    comparisonUnit (groupSets G₀) U (g * h) =
      (comparisonMultiplication G₀).hom.app (Opposite.op ((Scheme.toProEt X).obj U))
        (comparisonUnit (groupSets G₀) U g, comparisonUnit (groupSets G₀) U h) := by
  have hn := congrArg (fun k ↦ k.hom.app (Opposite.op U) (g, h))
    ((Scheme.proEtaleSiteComparison X).unit.naturality (groupMultiplication G₀))
  have hp := comparison_unit_product (groupSets G₀) (groupSets G₀) U g h
  have hi := congrArg (fun k ↦ k.hom.app
      (Opposite.op ((Scheme.toProEt X).obj U))
      (comparisonUnit (groupSets G₀ ⊗ groupSets G₀) U (g, h)))
    (comparisonProduct (groupSets G₀) (groupSets G₀)).hom_inv_id
  change (comparisonProduct (groupSets G₀) (groupSets G₀)).inv.hom.app
      (Opposite.op ((Scheme.toProEt X).obj U))
      ((comparisonProduct (groupSets G₀) (groupSets G₀)).hom.hom.app
        (Opposite.op ((Scheme.toProEt X).obj U))
        (comparisonUnit (groupSets G₀ ⊗ groupSets G₀) U (g, h))) =
    comparisonUnit (groupSets G₀ ⊗ groupSets G₀) U (g, h) at hi
  rw [hp] at hi
  exact hn.trans (congrArg
    (((comparisonSets X).map (groupMultiplication G₀)).hom.app
      (Opposite.op ((Scheme.toProEt X).obj U))) hi.symm)

private theorem comparison_unit_one {X : Scheme.{u}}
    (G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (U : X.Etale) :
    comparisonUnit (groupSets G₀) U (1 : G₀.obj.obj (Opposite.op U)) =
      (comparisonIdentity G₀).hom.app
        (Opposite.op ((Scheme.toProEt X).obj U)) PUnit.unit := by
  have := Scheme.preservesFiniteLimits_proEtaleSiteComparison X
  have hn := congrArg (fun k ↦ k.hom.app (Opposite.op U) PUnit.unit)
    ((Scheme.proEtaleSiteComparison X).unit.naturality (groupIdentity G₀))
  have ht : comparisonUnit (𝟙_ (Sheaf X.smallEtaleTopology (Type (u + 1)))) U PUnit.unit =
      (CartesianMonoidalCategory.preservesTerminalIso (comparisonSets X)).inv.hom.app
        (Opposite.op ((Scheme.toProEt X).obj U)) PUnit.unit := by
    apply (ConcreteCategory.bijective_of_isIso
      ((CartesianMonoidalCategory.preservesTerminalIso (comparisonSets X)).hom.hom.app
        (Opposite.op ((Scheme.toProEt X).obj U)))).injective
    exact @Subsingleton.elim PUnit _ _ _
  exact hn.trans (congrArg
    (((comparisonSets X).map (groupIdentity G₀)).hom.app
      (Opposite.op ((Scheme.toProEt X).obj U))) ht)

private theorem model_of_classical {X : Scheme.{u}}
    {G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}} (T : ComparisonTorsor G₀)
    (hc : IsClassical T.sheaf) :
    ∃ P : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀,
      Nonempty (ComparisonTorsor.ModelIso P T) := by
  classical
  let L := comparisonSets X
  let R := (Scheme.toProEt X).sheafPushforwardContinuous
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  let S := R.obj T.sheaf
  let a (U : X.Etaleᵒᵖ) (g : G₀.obj.obj U) (t : S.obj.obj U) :=
    T.action.hom.app ((Scheme.toProEt X).op.obj U)
      (comparisonUnit (groupSets G₀) U.unop g, t)
  have : IsIso ((Scheme.proEtaleSiteComparison X).counit.app T.sheaf) :=
    (Scheme.proEtaleClassicalSheavesImage X T.sheaf).2.mp hc
  let ε := asIso ((Scheme.proEtaleSiteComparison X).counit.app T.sheaf)
  have hfinite := Scheme.preservesFiniteLimits_proEtaleSiteComparison X
  have hbij := (Scheme.proEtaleClassicalSheavesUnit X).2
  have : L.Faithful := ⟨fun h ↦ (hbij _ _).1 h⟩
  have hnempty (U : X.Etale) : CategoryTheory.Sheaf.nonemptySieve S.obj U ∈
      X.smallEtaleTopology U := by
    let q := CartesianMonoidalCategory.toUnit S
    let qT := CartesianMonoidalCategory.toUnit T.sheaf
    have : CategoryTheory.Sheaf.IsLocallySurjective qT := by
      constructor
      intro V t
      apply (Scheme.ProEt.topology X).superset_covering _ (T.nonemptySieve_mem V)
      intro W f hf
      obtain ⟨s⟩ := hf
      exact ⟨s, @Subsingleton.elim PUnit _ _ _⟩
    have : Epi qT := inferInstance
    let c := CartesianMonoidalCategory.preservesTerminalIso L
    have hq : L.map q ≫ c.hom = ε.hom ≫ qT :=
      CartesianMonoidalCategory.toUnit_unique _ _
    have : Epi (L.map q ≫ c.hom) := hq.symm ▸ inferInstance
    have : Epi (L.map q) := (epi_comp_iff_of_isIso (L.map q) c.hom).1 inferInstance
    have : Epi q := ⟨fun f g h ↦ by
      apply L.map_injective
      apply (cancel_epi (L.map q)).1
      simpa only [← L.map_comp] using congrArg L.map h⟩
    have : CategoryTheory.Sheaf.IsLocallySurjective q :=
      (CategoryTheory.Sheaf.isLocallySurjective_iff_epi q).2 inferInstance
    apply X.smallEtaleTopology.superset_covering _
      (Presheaf.imageSieve_mem X.smallEtaleTopology q.hom
        (show (𝟙_ (Sheaf X.smallEtaleTopology (Type (u + 1)))).obj.obj
          (Opposite.op U) from PUnit.unit))
    intro V f hf
    obtain ⟨t, _⟩ := hf
    exact ⟨t⟩
  let P : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀ :=
    { sheaf := S
      act := a
      one_act := fun U t ↦ by
        dsimp [a]
        rw [comparison_unit_one]
        exact T.one_act _ t
      mul_act := fun U g h t ↦ by
        dsimp [a]
        rw [comparison_unit_mul]
        exact T.mul_act _ _ _ t
      map_act := fun {U V} f g t ↦ by
        have hη := ((Scheme.proEtaleSiteComparison X).unit.app
          (groupSets G₀)).hom.naturality_apply f g
        have hn := T.action.hom.naturality_apply ((Scheme.toProEt X).op.map f)
          (show (((comparisonSets X).obj (groupSets G₀)) ⊗ T.sheaf).obj.obj
            ((Scheme.toProEt X).op.obj U) from
            (comparisonUnit (groupSets G₀) U.unop g, t))
        change T.action.hom.app ((Scheme.toProEt X).op.obj V)
            (((comparisonSets X).obj (groupSets G₀)).obj.map
              ((Scheme.toProEt X).op.map f) (comparisonUnit (groupSets G₀) U.unop g),
                T.sheaf.obj.map ((Scheme.toProEt X).op.map f) t) = _ at hn
        change comparisonUnit (groupSets G₀) V.unop ((G₀.obj.map f).hom g) =
          ((comparisonSets X).obj (groupSets G₀)).obj.map
            ((Scheme.toProEt X).op.map f) (comparisonUnit (groupSets G₀) U.unop g) at hη
        exact hn.symm.trans (congrArg
          (fun z ↦ T.action.hom.app ((Scheme.toProEt X).op.obj V)
            (z, T.sheaf.obj.map ((Scheme.toProEt X).op.map f) t)) hη.symm)
      bijective_act := fun U t ↦ by
        have := (Scheme.proEtaleClassicalSheavesUnit X).1 (groupSets G₀)
        exact (T.bijective_act ((Scheme.toProEt X).op.obj U) t).comp
          (ConcreteCategory.bijective_of_isIso
            (((Scheme.proEtaleSiteComparison X).unit.app (groupSets G₀)).hom.app U))
      nonemptySieve_mem := hnempty }
  refine ⟨P, ⟨⟨ε, ?_⟩⟩⟩
  apply (cancel_epi (comparisonProduct (groupSets G₀) S).hom).1
  simp only [comparisonTorsorAction, ← Category.assoc]
  rw [show (comparisonProduct (groupSets G₀) S).hom ≫
      (comparisonProduct (groupSets G₀) P.sheaf).inv = 𝟙 _ from
    (comparisonProduct (groupSets G₀) S).hom_inv_id, Category.id_comp]
  apply ((Scheme.proEtaleSiteComparison X).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  ext U p
  obtain ⟨g, t⟩ := p
  have htri (s : S.obj.obj U) :
      ε.hom.hom.app ((Scheme.toProEt X).op.obj U)
        (comparisonUnit S U.unop s) = s := by
    have h := congrArg (fun k ↦ k.hom.app U s)
      ((Scheme.proEtaleSiteComparison X).right_triangle_components T.sheaf)
    exact h
  have hnat := congrArg (fun k ↦ k.hom.app U (g, t))
    ((Scheme.proEtaleSiteComparison X).unit.naturality (etaleTorsorAction P)).symm
  change ((L.map (etaleTorsorAction P)).hom.app ((Scheme.toProEt X).op.obj U)
      (comparisonUnit (groupSets G₀ ⊗ S) U.unop (g, t))) =
        comparisonUnit S U.unop (a U g t) at hnat
  have hp := comparison_unit_product (groupSets G₀) S U.unop g t
  change ε.hom.hom.app ((Scheme.toProEt X).op.obj U)
      ((L.map (etaleTorsorAction P)).hom.app ((Scheme.toProEt X).op.obj U)
        (comparisonUnit (groupSets G₀ ⊗ S) U.unop (g, t))) = _
  rw [hnat, htri]
  change a U g t = T.action.hom.app ((Scheme.toProEt X).op.obj U)
    ((𝟙 _ ⊗ₘ ε.hom).hom.app ((Scheme.toProEt X).op.obj U)
      ((comparisonProduct (groupSets G₀) S).hom.hom.app ((Scheme.toProEt X).op.obj U)
        (comparisonUnit (groupSets G₀ ⊗ S) U.unop (g, t))))
  erw [hp]
  change a U g t = T.action.hom.app ((Scheme.toProEt X).op.obj U)
    (comparisonUnit (groupSets G₀) U.unop g,
      ε.hom.hom.app ((Scheme.toProEt X).op.obj U) (comparisonUnit S U.unop t))
  rw [htri]


private theorem trivialization_of_section {X : Scheme.{u}}
    {G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}} (T : ComparisonTorsor G₀)
    (U : X.ProEt) (s : T.sheaf.obj.obj (Opposite.op U)) :
    Nonempty (ComparisonTorsor.Trivialization T U) := by
  classical
  let e (V : X.ProEt) (f : V ⟶ U) :=
    Equiv.ofBijective
      (fun a ↦ T.action.hom.app (Opposite.op V) (a, T.sheaf.obj.map f.op s))
      (T.bijective_act (Opposite.op V) (T.sheaf.obj.map f.op s))
  refine ⟨{ equiv := fun V f ↦ (e V f).symm, natural := ?_, equivariant := ?_ }⟩
  · intro V W f g t
    apply (e W (g ≫ f)).injective
    rw [Equiv.apply_symm_apply]
    let p : (((comparisonSets X).obj (groupSets G₀)) ⊗ T.sheaf).obj.obj
        (Opposite.op V) := ((e V f).symm t, T.sheaf.obj.map f.op s)
    have hn := ConcreteCategory.congr_hom (T.action.hom.naturality g.op) p
    change T.action.hom.app (Opposite.op W)
        (((comparisonSets X).obj (groupSets G₀)).obj.map g.op ((e V f).symm t),
          T.sheaf.obj.map g.op (T.sheaf.obj.map f.op s)) =
      T.sheaf.obj.map g.op (e V f ((e V f).symm t)) at hn
    change T.sheaf.obj.map g.op t = T.action.hom.app (Opposite.op W)
      (((comparisonSets X).obj (groupSets G₀)).obj.map g.op ((e V f).symm t),
        T.sheaf.obj.map (g ≫ f).op s)
    simpa only [Equiv.apply_symm_apply, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply] using hn.symm
  · intro V f a t
    apply (e V f).injective
    rw [Equiv.apply_symm_apply]
    change T.action.hom.app (Opposite.op V) (a, t) =
      T.action.hom.app (Opposite.op V)
        ((comparisonMultiplication G₀).hom.app (Opposite.op V) (a, (e V f).symm t),
          T.sheaf.obj.map f.op s)
    rw [T.mul_act]
    change _ = T.action.hom.app (Opposite.op V) (a, e V f ((e V f).symm t))
    rw [Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem model_etale_cover {X : Scheme.{u}}
    {G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}} (T : ComparisonTorsor G₀)
    (P : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀)
    (α : ComparisonTorsor.ModelIso P T) :
    ∃ (I : Type (u + 1)) (U : I → X.Etale),
      (∀ x : X, ∃ (i : I) (y : (U i).left), (U i).hom y = x) ∧
      ∀ i : I, Nonempty (ComparisonTorsor.Trivialization T ((Scheme.toProEt X).obj (U i))) := by
  classical
  let I := {V : X.Etale // Nonempty (P.sheaf.obj.obj (Opposite.op V))}
  refine ⟨I, Subtype.val, ?_, ?_⟩
  · let W := Scheme.Etale.mk (𝟙 X)
    have hs := P.nonemptySieve_mem W
    change _ ∈ X.smallGrothendieckTopology (P := @Etale) W at hs
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X le_rfl] at hs
    intro x
    obtain ⟨V, f, y, hf, _, hy⟩ :=
      (Scheme.mem_toGrothendieck_smallPretopology W _).1 hs x
    refine ⟨⟨V, hf⟩, y, ?_⟩
    have hw := f.w
    change f.left ≫ 𝟙 X = V.hom at hw
    have hw' : f.left = V.hom := (Category.comp_id _).symm.trans hw
    change V.hom y = x
    exact hw' ▸ hy
  · intro i
    obtain ⟨s⟩ := i.property
    apply trivialization_of_section T
    exact α.iso.hom.hom.app (Opposite.op ((Scheme.toProEt X).obj i.val))
      (((Scheme.proEtaleSiteComparison X).unit.app P.sheaf).hom.app (Opposite.op i.val) s)

private theorem modelIso_unique {X : Scheme.{u}}
    {G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}} (T : ComparisonTorsor G₀)
    (P Q : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀)
    (α : ComparisonTorsor.ModelIso P T) (β : ComparisonTorsor.ModelIso Q T) :
    ∃! e : P.sheaf ≅ Q.sheaf,
      etaleTorsorAction P ≫ e.hom =
        (𝟙 (groupSets G₀) ⊗ₘ e.hom) ≫ etaleTorsorAction Q ∧
      (comparisonSets X).map e.hom ≫ β.iso.hom = α.iso.hom := by
  classical
  let F := comparisonSets X
  have := Scheme.preservesFiniteLimits_proEtaleSiteComparison X
  have hbij := (Scheme.proEtaleClassicalSheavesUnit X).2
  have : F.Faithful := ⟨fun h ↦ (hbij _ _).1 h⟩
  have : F.Full := ⟨fun h ↦ (hbij _ _).2 h⟩
  let e := F.preimageIso (α.iso ≪≫ β.iso.symm)
  have he : F.map e.hom = α.iso.hom ≫ β.iso.inv := by
    simp [e]
  have heβ : F.map e.hom ≫ β.iso.hom = α.iso.hom := by
    simp [he]
  refine ⟨e, ⟨?_, heβ⟩, ?_⟩
  · apply F.map_injective
    apply (cancel_epi (comparisonProduct (groupSets G₀) P.sheaf).inv).1
    simp only [Functor.map_comp]
    change comparisonTorsorAction P ≫ F.map e.hom = _
    rw [he]
    have hb := β.equivariant
    have ha := α.equivariant
    have hn := CartesianMonoidalCategory.prodComparison_inv_natural
      F (𝟙 (groupSets G₀)) e.hom
    have hi (H : Sheaf X.smallEtaleTopology (Type (u + 1))) :
        inv (CartesianMonoidalCategory.prodComparison F (groupSets G₀) H) =
          (comparisonProduct (groupSets G₀) H).inv := by
      apply (cancel_mono (comparisonProduct (groupSets G₀) H).hom).1
      change inv (CartesianMonoidalCategory.prodComparison F (groupSets G₀) H) ≫
          CartesianMonoidalCategory.prodComparison F (groupSets G₀) H =
        (comparisonProduct (groupSets G₀) H).inv ≫
          (comparisonProduct (groupSets G₀) H).hom
      rw [IsIso.inv_hom_id, Iso.inv_hom_id]
    rw [hi P.sheaf, hi Q.sheaf] at hn
    change (comparisonProduct (groupSets G₀) P.sheaf).inv ≫
        F.map (𝟙 (groupSets G₀) ⊗ₘ e.hom) =
      (F.map (𝟙 (groupSets G₀)) ⊗ₘ F.map e.hom) ≫
        (comparisonProduct (groupSets G₀) Q.sheaf).inv at hn
    rw [← Category.assoc _ (F.map (𝟙 (groupSets G₀) ⊗ₘ e.hom)), hn]
    rw [F.map_id]
    simp only [Category.assoc]
    change comparisonTorsorAction P ≫ α.iso.hom ≫ β.iso.inv =
      (𝟙 _ ⊗ₘ F.map e.hom) ≫ comparisonTorsorAction Q
    apply (cancel_mono β.iso.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp, heβ]
  · intro e' he'
    apply Iso.ext
    apply F.map_injective
    apply (cancel_mono β.iso.hom).1
    exact he'.2.trans heβ.symm

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def restrictionPullbackIso (X : Scheme.{u}) (U : X.ProEt) :
    proEtaleComparisonPullback (Type (u + 1)) U.hom ≅
      Scheme.proEtaleSetRestriction X U := by
  letI hMap := Scheme.ProEt.isContinuous_overMap U.prop
  letI hPull := Scheme.ProEt.isContinuous_overPullback U.hom
  let adj : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop) ⊣
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom :=
    MorphismProperty.Over.mapPullbackAdj (@WeaklyEtale) ⊤ U.hom U.prop _root_.trivial
  exact (proEtaleComparisonAdjunction (Type (u + 1)) U.hom).leftAdjointUniq
    (@Adjunction.sheafPushforwardContinuous _ _ _ _ _ _ _ _ adj
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) hMap hPull)

private noncomputable def classicalRestrictionIso (X : Scheme.{u}) (U : X.ProEt) :
    comparisonSets X ⋙ Scheme.proEtaleSetRestriction X U ≅
      etaleComparisonPullback (Type (u + 1)) U.hom ⋙ comparisonSets U.left :=
  (Functor.isoWhiskerLeft _ (restrictionPullbackIso X U)).symm ≪≫
    (comparisonCoefficientPullbackIso (Type (u + 1)) U.hom).symm

private theorem classical_of_torsor {X : Scheme.{u}}
    {G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}} (T : ComparisonTorsor G₀) :
    IsClassical T.sheaf := by
  classical
  let I := {U : X.ProEt // Nonempty (T.sheaf.obj.obj (Opposite.op U))}
  let U : I → X.ProEt := Subtype.val
  have hcover : (Scheme.ProEt.topology X).CoversTop U := by
    intro V
    apply (Scheme.ProEt.topology X).superset_covering _ (T.nonemptySieve_mem V)
    intro W f hf
    exact ⟨⟨W, hf⟩, ⟨𝟙 W⟩⟩
  have hlocal : Scheme.IsProEtaleLocallyClassical X T.sheaf := by
    refine ⟨I, U, hcover, fun i ↦ ?_⟩
    obtain ⟨s⟩ := i.property
    let R := Scheme.proEtaleSetRestriction X (U i)
    let k := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (U i).prop
    let sec (V : (U i).left.ProEt) :=
      T.sheaf.obj.map
        (show k.obj V ⟶ U i from MorphismProperty.Over.homMk V.hom (by rfl)).op s
    let f : R.obj ((comparisonSets X).obj (groupSets G₀)) ⟶ R.obj T.sheaf :=
      ⟨{ app := fun V ↦ TypeCat.ofHom (fun g ↦
            T.action.hom.app (Opposite.op (k.obj V.unop)) (g, sec V.unop))
         naturality := by
           intro V W h
           ext g
           have hn := T.action.hom.naturality_apply (k.op.map h)
             (show (((comparisonSets X).obj (groupSets G₀)) ⊗ T.sheaf).obj.obj
               (k.op.obj V) from (g, sec V.unop))
           symm
           change T.sheaf.obj.map (k.op.map h)
               (T.action.hom.app (Opposite.op (k.obj V.unop)) (g, sec V.unop)) =
             T.action.hom.app (Opposite.op (k.obj W.unop))
               (((comparisonSets X).obj (groupSets G₀)).obj.map (k.op.map h) g,
                 sec W.unop)
           erw [← hn]
           congr 1
           apply Prod.ext
           · rfl
           · change T.sheaf.obj.map (k.op.map h) (sec V.unop) = sec W.unop
             dsimp only [sec]
             erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
             congr 2
             apply congrArg T.sheaf.obj.map
             apply Quiver.Hom.unop_inj
             apply MorphismProperty.Over.Hom.ext
             exact h.unop.w }⟩
    have hf (V : (U i).left.ProEtᵒᵖ) : IsIso (f.hom.app V) := by
      apply (isIso_iff_bijective _).2
      exact T.bijective_act _ _
    have : IsIso f.hom := NatIso.isIso_of_isIso_app _
    have : IsIso ((sheafToPresheaf (Scheme.ProEt.topology (U i).left)
        (Type (u + 1))).map f) := by
      change IsIso f.hom
      infer_instance
    have : IsIso f := isIso_of_reflects_iso f
      (sheafToPresheaf (Scheme.ProEt.topology (U i).left) (Type (u + 1)))
    refine ⟨(etaleComparisonPullback (Type (u + 1)) (U i).hom).obj (groupSets G₀), ?_⟩
    exact ⟨(asIso f).symm ≪≫ (classicalRestrictionIso X (U i)).app (groupSets G₀)⟩
  apply (Scheme.proEtaleClassicalSheavesImage X T.sheaf).1.mp
  exact (Scheme.proEtale_locallyClassical_etaleCover X T.sheaf).1 hlocal

/-- Every torsor under the inverse image of an etale group sheaf descends to an etale
torsor. The model together with its specified comparison is unique up to unique equivariant
isomorphism commuting with that comparison. The original torsor is classical and is trivial
on an etale covering of the scheme.

Source: current blueprint, `sk-lem-pe-torsor-comparison-glue.md`, proof paragraphs 1--3;
Stacks Project, Tag 099X (blueprint: det-pe-torsor-comparison-glue).

Proof:
1. First fix the restriction identifications used throughout. By
[lem-weil-pbc-etale-site-localization-open], for any etale morphism $W\to X$ (in particular any
open subscheme) the slice $X_{\Et}/W$ is $W_{\Et}$ as a site, not just at the level of abelian
sheaves. Part (1) of [lem-weil-proetale-weakly-etale-localization] identifies $X_{\Proet}/W$ with
$W_{\Proet}$ and their set sheaves. The inclusion in [def-weil-pbc-site-comparison-morphism] views
every etale object as weakly etale, so both site-identification hypotheses hold. Apply
[lem-weil-pbc-slice-site-localization] to the continuous inclusion defining $\nu_X$ in
[def-weil-pbc-site-comparison-morphism]. On the localized sites the inclusion is exactly the
inclusion defining $\nu_W$. Hence there is a natural isomorphism
$r_{W,F}:(\nu_X^*F)|_W\xrightarrow{\sim}\nu_W^*(F|_W)$. Use these canonical identifications on all
overlaps. For composable etale maps $Z\to W\to X$, denote this isomorphism by $r^X_{W,F}$. Under
the sectionwise relocalization identifications, $r^X_{Z,F}=r^W_{Z,F|_W}\circ(r^X_{W,F})|_Z$.
Indeed, the inclusion and forgetful slice functors commute on objects and arrows; the two
comparison maps are adjunction mates of that same commuting composite square, so the adjunction
bijection makes them equal. The isomorphisms preserve finite products since both routes are
finite-limit-preserving inverse images; thus they identify the restricted group actions.
Restricting a torsor gives a torsor: simple transitivity and a local section can be checked on the
same objects and covering families of these slice sites.

2. Choose a set-indexed affine open cover $X=\bigcup_aX_a$ (no quasi-compactness or
quasi-separatedness is required). An open cover is a cover in both sites by [sk-def-pe-site] and
[def-weil-pbc-etale-site]. By step 1 the restriction of $T$ is a $\nu_{X_a}^*(G_0|_{X_a})$-torsor.
Apply [det-pe-torsor-comparison-affine] to each affine scheme $X_a$: obtain a $G_0|_{X_a}$-torsor
$T_{0,a}$, an equivariant isomorphism $\alpha_a:\nu_{X_a}^*T_{0,a}\xrightarrow{\sim}T|_{X_a}$, and
an affine etale surjection $W_a\to X_a$ with $T_{0,a}(W_a)\ne\varnothing$. The same argument
includes $X=\varnothing$, using an empty affine cover.

3. Put $X_{ab}=X_a\cap X_b$. Under step 1 the map $\beta_{ab}=\alpha_b^{-1}\circ\alpha_a$ is an
isomorphism from $\nu_{X_{ab}}^*(T_{0,a}|_{X_{ab}})$ to $\nu_{X_{ab}}^*(T_{0,b}|_{X_{ab}})$. Full
faithfulness in [det-pe-classical-sheaves-unit], applied to the scheme $X_{ab}$, gives a unique
sheaf map $\phi_{ab}$ with $\nu^*\phi_{ab}=\beta_{ab}$. Lift $\beta_{ab}^{-1}$ as well;
faithfulness applied to their two composites proves that $\phi_{ab}$ is invertible. Write
$m_a,m_b$ for the restricted actions. Since $\beta_{ab}$ is equivariant, the pullbacks of
$\phi_{ab}\circ m_a$ and $m_b\circ(\mathrm{id}_{G_0}\times\phi_{ab})$ agree. The finite-product
preservation in [def-weil-pbc-site-comparison-morphism] identifies their domains, and faithfulness
makes the two maps equal. Thus $\phi_{ab}$ is equivariant. On $X_{abc}$, cancellation gives
$\beta_{bc}\beta_{ab}=\alpha_c^{-1}\alpha_a=\beta_{ac}$; faithfulness on this scheme gives
$\phi_{bc}\phi_{ab}=\phi_{ac}$. Likewise $\phi_{aa}=\mathrm{id}$. None of these overlaps is
assumed affine.

4. Apply [lem-pe-site-sheaf-gluing] to the covering $\{X_a\to X\}$ of $X_{\Et}$ and the sheaves
$T_{0,a}$ with the isomorphisms $\phi_{ab}$ from step 3. The small sites and the set-indexed cover
fit the universe convention in that lemma. Since $X$ is final in its small etale site, the slice
over $X$ is the original site. Using the site identifications fixed in step 1, the lemma gives a
sheaf of sets $T_0$ on $X_{\Et}$ and isomorphisms $e_a:T_0|_{X_a}\xrightarrow{\sim}T_{0,a}$
satisfying $\phi_{ab}e_a=e_b$ on every overlap.

5. Define the action on $T_0$ explicitly. For an etale $V\to X$, $g\in G_0(V)$ and $t\in T_0(V)$,
set $V_a=V\times_XX_a$. The sections $e_a^{-1}(g|_{V_a}\cdot e_a(t|_{V_a}))$ agree on
$V_a\times_VV_b$, by the equivariance of $\phi_{ab}$ and $\phi_{ab}e_a=e_b$. The sheaf axiom
[def-weil-pbc-etale-sheaf-of-sets] gives a unique section $g\cdot t$ on $V$. Restriction, the
identity law and associativity hold because they hold on every $V_a$ and the same uniqueness
applies. For $t,t'\in T_0(V)$, the local torsor structures give a unique $g_a\in G_0(V_a)$ sending
$t|_{V_a}$ to $t'|_{V_a}$. Freeness makes these agree on overlaps; the sheaf axiom for $G_0$ glues
them to a unique $g\in G_0(V)$. Finally the chosen sections over the etale surjections $W_a\to
X_a$ of step 2 give local sections of $T_0$ on a jointly surjective etale family over $X$, and on
every test object after base change. These are precisely simple transitivity and local
nonemptiness in [def-constructible-torsor], so $T_0$ is a $G_0$-torsor.

6. The local maps $A_a=\alpha_a\circ\nu_{X_a}^*(e_a)\circ r_{X_a,T_0}$ are equivariant
isomorphisms $(\nu_X^*T_0)|_{X_a}\to T|_{X_a}$. On $X_{ab}$ the equations
$\nu^*\phi_{ab}=\alpha_b^{-1}\alpha_a$ and $\phi_{ab}e_a=e_b$ give $A_b=A_a$; naturality of $r$
from step 1 makes these equations equations between the actual restricted maps. For a pro-etale
object $V\to X$ and $s\in(\nu_X^*T_0)(V)$, apply $A_a$ to $s|_{V\times_XX_a}$ and glue the
resulting compatible sections of $T$ over the open cover of $V$. The sheaf axiom
[def-weil-pbc-sites-and-cohomology] makes this a unique section $\alpha_V(s)$, natural in $V$. For
a morphism $h:V^{\prime}\to V$, both $h^*\alpha_V(s)$ and $\alpha_{V^{\prime}}(h^*s)$ restrict
over $V^{\prime}\times_XX_a$ to $A_a(h^*s)$ by naturality of $A_a$; uniqueness of gluing proves
naturality of $\alpha$. Define $B_V(t)$ for $t\in T(V)$ to be the unique section of
$(\nu_X^*T_0)(V)$ whose restriction over $V\times_XX_a$ is $A_a^{-1}(t|_{V\times_XX_a})$. These
local sections agree because $A_a=A_b$ on overlaps. Restriction of $B_V(t)$ along $h$ and
$B_{V^{\prime}}(h^*t)$ have equal local restrictions, so $B$ is a sheaf map. The restrictions of
$B\alpha$ and $\alpha B$ are $A_a^{-1}A_a$ and $A_aA_a^{-1}$ respectively; the sheaf axiom makes
both composites identities. For local sections $g,s$, the sections $\alpha(gs)$ and $g\alpha(s)$
restrict to $A_a(gs)=gA_a(s)$, so they are equal by uniqueness of gluing. Thus
$\alpha:\nu_X^*T_0\xrightarrow{\sim}T$ is an isomorphism of torsors. This uses the fact in
[sk-def-pe-site] that every open cover is a pro-etale cover, with no finiteness requirement on the
affine cover of $X$.

7. Uniqueness concerns the pair $(T_0,\alpha)$. If $(T'_0,\alpha')$ is another such pair, full
faithfulness in [det-pe-classical-sheaves-unit] on $X$ gives a unique $f:T_0\to T'_0$ with
$\nu_X^*f=(\alpha')^{-1}\alpha$. Its inverse is the unique lift of $\alpha^{-1}\alpha'$, as
verified by faithfulness. The equivariance equation for $f$ follows by applying faithfulness to
the two maps out of $G_0\times T_0$; their pullbacks are equal because $(\alpha')^{-1}\alpha$ is
equivariant and [def-weil-pbc-site-comparison-morphism] preserves finite products. Hence $f$ is
the unique torsor isomorphism satisfying $\alpha'\circ\nu_X^*f=\alpha$. This is the asserted
uniqueness up to unique isomorphism, with the specified comparison to $T$ included.

8. By [det-pe-classical-sheaves-image], the isomorphism $T\cong\nu_X^*T_0$ makes $T$ classical.
The composites $W_a\to X_a\to X$ from step 2 are etale and jointly surjective, so they form an
etale covering by [def-weil-pbc-etale-site]. A chosen section of $T_{0,a}(W_a)$ trivializes $T_0$
there: $g\mapsto g\cdot s_a$ is an isomorphism by simple transitivity, also on every further test
object. Pulling this isomorphism back and using step 1 and $\alpha$ from step 6 trivializes $T$ on
$W_a$. Thus the asserted etale trivializing covering is an actual covering of $X$, not just a
collection of local covers. -/
theorem torsorComparisonGlue (X : Scheme.{u})
    (G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (T : ComparisonTorsor G₀) :
    (∃ (T₀ : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀)
      (α : ComparisonTorsor.ModelIso T₀ T),
      ∀ (T₀' : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀)
        (α' : ComparisonTorsor.ModelIso T₀' T),
        ∃! e : T₀.sheaf ≅ T₀'.sheaf,
          etaleTorsorAction T₀ ≫ e.hom =
            (𝟙 (groupSets G₀) ⊗ₘ e.hom) ≫ etaleTorsorAction T₀' ∧
          (comparisonSets X).map e.hom ≫ α'.iso.hom = α.iso.hom) ∧
    IsClassical T.sheaf ∧
    ∃ (I : Type (u + 1)) (U : I → X.Etale),
      (∀ x : X, ∃ (i : I) (y : (U i).left), (U i).hom y = x) ∧
      ∀ i : I, Nonempty (ComparisonTorsor.Trivialization T ((Scheme.toProEt X).obj (U i))) := by
  have hc : IsClassical T.sheaf := classical_of_torsor T
  obtain ⟨P, ⟨α⟩⟩ := model_of_classical T hc
  exact ⟨⟨P, α, fun Q β ↦ modelIso_unique T P Q α β⟩,
    hc, model_etale_cover T P α⟩

end AlgebraicGeometry.ProEtale
