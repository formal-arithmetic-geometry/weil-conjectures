/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryAbelianSquare
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryEdges
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinarySquareCoherence

/-! # The ordinary coefficient-normalized component square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {T : Type u₄} [Category.{v₄} T] [MonoidalCategory T]
  (F : C ⥤ D) (G : D ⥤ T) (H : C ⥤ E) (I : E ⥤ T)
  [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] [I.LaxMonoidal]
  {A : C} [MonObj A] {B : D} [MonObj B] {R : E} [MonObj R] {S : T} [MonObj S]
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare

namespace CategoryTheory

private theorem double_action
    (a : B ⟶ F.obj A) [IsMonHom a] (b : S ⟶ G.obj B) [IsMonHom b]
    (M : Mod C A) :
    Mod.act (((F.mapMod A ⋙ Mod.comap a) ⋙ (G.mapMod B ⋙ Mod.comap b)).obj M).X =
      (b ≫ G.map a) ▷ (F ⋙ G).obj M.X ≫
        Functor.LaxMonoidal.μ (F ⋙ G) A M.X ≫ (F ⋙ G).map (Mod.act M.X) := by
  simp only [Functor.comp_obj, Mod.act_comap_obj, Functor.act_mapMod_obj,
    Functor.map_comp, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
    comp_whiskerRight, Category.assoc]
  change b ▷ G.obj (F.obj M.X) ≫
      Functor.LaxMonoidal.μ G B (F.obj M.X) ≫
        G.map (a ▷ F.obj M.X) ≫ _ = _
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]

private theorem double_linear (e : F ⋙ G ≅ H ⋙ I) [NatTrans.IsMonoidal e.hom]
    (a : B ⟶ F.obj A) [IsMonHom a] (b : S ⟶ G.obj B) [IsMonHom b]
    (c : R ⟶ H.obj A) [IsMonHom c] (d : S ⟶ I.obj R) [IsMonHom d]
    (he : b ≫ G.map a ≫ e.hom.app A = d ≫ I.map c) (M : Mod C A) :
    Mod.act (((F.mapMod A ⋙ Mod.comap a) ⋙ (G.mapMod B ⋙ Mod.comap b)).obj M).X ≫
        e.hom.app M.X =
      S ◁ e.hom.app M.X ≫
        Mod.act (((H.mapMod A ⋙ Mod.comap c) ⋙ (I.mapMod R ⋙ Mod.comap d)).obj M).X := by
  rw [double_action F G a b M, double_action H I c d M]
  simp only [Category.assoc]
  rw [e.hom.naturality, NatTrans.IsMonoidal.tensor_assoc]
  erw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, Category.assoc, he]
  rw [← whisker_exchange_assoc]

private def doubleIso (e : F ⋙ G ≅ H ⋙ I) [NatTrans.IsMonoidal e.hom]
    (a : B ⟶ F.obj A) [IsMonHom a] (b : S ⟶ G.obj B) [IsMonHom b]
    (c : R ⟶ H.obj A) [IsMonHom c] (d : S ⟶ I.obj R) [IsMonHom d]
    (he : b ≫ G.map a ≫ e.hom.app A = d ≫ I.map c) :
    (F.mapMod A ⋙ Mod.comap a) ⋙ (G.mapMod B ⋙ Mod.comap b) ≅
      (H.mapMod A ⋙ Mod.comap c) ⋙ (I.mapMod R ⋙ Mod.comap d) :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk (e.app M.X) (double_linear F G H I e a b c d he M))
    (fun f ↦ Mod.hom_ext _ _ (e.hom.naturality f.hom))

/-- The actual ordinary component pullbacks and their coherent comparisons.
Source: HRS construction (4.1), pp. 8--9; the ordinary part of the component-square
argument (blueprint: lem-zl-component-ordinary-pullback-square).

Proof: the relative component tests preserve finite limits and finite covering families.
The site inverse-image theorem equips their sheaf pullbacks with the canonical braided
strong tensor structure and exactness. Base change on profinite slices has the same
properties. Its composite with the absolute slice projection is identified with the
absolute test functor by the two product projections. Take the unit-normalized mates
of these restriction comparisons; evaluating their monoidal comparisons at the
condensed coefficient ring gives the prescribed coefficient isomorphisms.

Apply sheaves contravariantly to the specified lift-base-change isomorphisms. Their
mates give the abelian square. The two absolute-test comparisons agree on both
coordinates, so mate uniqueness gives the coefficient equation. Transport scalar
actions along the ring isomorphisms to lift this comparison to actual module sheaves;
linearity follows from naturality of the mate with multiplication and action.

The identity and composition test comparisons are the canonical maps fixed by their
projections. The lift-base-change theorem gives the corresponding equations, and
uniqueness of mates carries them first to abelian sheaves and then, by faithfulness of
the forgetful functor, to module sheaves. These are exactly the two equations in
`OrdinarySystem`. Empty schemes and the zero coefficient ring require no separate
choice or nonemptiness assumption. -/
theorem component_ordinary_pullback_square
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    Nonempty (OrdinarySystem Λ) := by
  classical
  let s := (component_ordinary_edges Λ).some
  let sq : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      Square Λ f (s.corner X) (s.corner Y) (s.slice f) :=
    fun f ↦ liftAbelianSquare Λ
      (component_ordinary_abelian_square Λ f (s.corner _) (s.corner _) (s.slice f)).some
  obtain ⟨hi, hc⟩ := component_ordinary_square_coherence Λ s sq
  exact ⟨{
    corner := s.corner
    slice := s.slice
    square := sq
    sliceIdentity := s.identity
    sliceComposition := s.composition
    identity := hi
    composition := hc }⟩

private def liftAbelianSquare
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : NormalizedAbelianSquare Λ f sX sY sh) : Square Λ f sX sY sh := by
  let G := upperStar Ab.{u + 1} f
  let φ := condensedPullbackHom Λ.X f
  let a := sX.coefficient
  let b := asIso φ
  let c := sh.coefficient
  let d := sY.coefficient
  have hi : b.inv ≫ G.map a.inv.hom ≫ sq.abelian.hom.app
      (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) =
      d.inv.hom ≫ sY.inverse.map c.inv.hom := by
    rw [← cancel_mono (sY.inverse.map c.hom.hom ≫ d.hom.hom)]
    calc
      _ = b.inv ≫ G.map a.inv.hom ≫
          (sq.abelian.hom.app _ ≫ sY.inverse.map c.hom.hom ≫ d.hom.hom) := by
        simp only [Category.assoc]
      _ = b.inv ≫ G.map a.inv.hom ≫ (G.map a.hom.hom ≫ b.hom) := by
        rw [← sq.coefficient]
        rfl
      _ = 𝟙 _ := by
        have ha : a.inv.hom ≫ a.hom.hom = 𝟙 _ :=
          congrArg Mon.Hom.hom a.inv_hom_id
        rw [← G.map_comp_assoc, ha, G.map_id, Category.id_comp, b.inv_hom_id]
      _ = _ := by
        have hc : c.inv.hom ≫ c.hom.hom = 𝟙 _ :=
          congrArg Mon.Hom.hom c.inv_hom_id
        have hd : d.inv.hom ≫ d.hom.hom = 𝟙 _ :=
          congrArg Mon.Hom.hom d.inv_hom_id
        simp only [Category.assoc]
        rw [← sY.inverse.map_comp_assoc, hc, sY.inverse.map_id,
          Category.id_comp, hd]
  let e := CategoryTheory.doubleIso sX.inverse G sh.inverse sY.inverse sq.abelian
    a.inv.hom b.inv c.inv.hom d.inv.hom hi
  let es : CondensedRing.upperStar Λ.X f ≅ G.mapMod
      (condensedRingObj Λ.X X) ⋙ Mod.comap b.inv :=
    Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ.X X))
      (Mod.extendScalarsIsoComapInv φ)
  let em : sX.modules Λ X ⋙ CondensedRing.upperStar Λ.X f ≅
      sh.modules Λ ⋙ sY.modules Λ Y := by
    unfold Corner.modules Slice.modules
    exact Functor.isoWhiskerLeft
      (sX.inverse.mapMod (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ⋙
        Mod.comap sX.coefficient.inv.hom) es ≪≫ e
  refine {
    tests := sq.tests
    tests_eq := sq.tests_eq
    abelian := sq.abelian
    abelian_mate := sq.abelian_mate
    coefficient := sq.coefficient
    ordinary := em
    ordinary_underlying := ?_ }
  intro M
  unfold Corner.modules Slice.modules at em ⊢
  rfl

end CategoryTheory
