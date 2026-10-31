/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarGeometricPullComposition

/-! Pullback-compositor transport for the open projection coefficient square.
(blueprint: lem-sf-open-projection-factor-compositor-transport).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  reductionDerivedChange completedAdicDerivedChange presheafToSheaf
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] scalarTensor scalarPull openComparison
  proEtaleCanonicalTensorComparison geometricPullComposition

private theorem openProjectionInverse_naturality (R : Coefficients.{u})
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    {M M' : DerivedCategory (pbcModules U (R.ring U))}
    {N N' : DerivedCategory (pbcModules V (R.ring V))} (f : M ⟶ M') (g : N ⟶ N') :
    (openExtension R j).mapDerivedCategory.map
        (a.tensor.map (Prod.mkHom f ((pull R j).map g))) ≫
      openProjectionInverse R j a b M' N' =
    openProjectionInverse R j a b M N ≫
      b.tensor.map (Prod.mkHom ((openExtension R j).mapDerivedCategory.map f) g) := by
  let J := (openExtension R j).mapDerivedCategory
  let P := pull R j
  let adj := openDerivedAdjunction R j
  let e := proEtaleCanonicalTensorComparison j (R.ring V) (R.ring U) (R.pull j) b a
  apply adj.homEquiv_naturality_right_square
  change a.tensor.map (Prod.mkHom f (P.map g)) ≫
      (a.tensor.map (Prod.mkHom (adj.unit.app M') (𝟙 _)) ≫ e.inv.app (J.obj M', N')) =
    (a.tensor.map (Prod.mkHom (adj.unit.app M) (𝟙 _)) ≫ e.inv.app (J.obj M, N)) ≫
      P.map (b.tensor.map (Prod.mkHom (J.map f) g))
  have hn : Prod.mkHom f (P.map g) ≫ Prod.mkHom (adj.unit.app M') (𝟙 _) =
      Prod.mkHom (adj.unit.app M) (𝟙 _) ≫ (P.prod P).map (Prod.mkHom (J.map f) g) := by
    ext
    · exact adj.unit.naturality f
    · simp
  rw [← Category.assoc, ← a.tensor.map_comp, hn, a.tensor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact e.inv.naturality (Prod.mkHom (J.map f) g)

private theorem openProjectionHom_naturality (R : Coefficients.{u})
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    {M M' : DerivedCategory (pbcModules U (R.ring U))}
    {N N' : DerivedCategory (pbcModules V (R.ring V))} (f : M ⟶ M') (g : N ⟶ N') :
    b.tensor.map (Prod.mkHom ((openExtension R j).mapDerivedCategory.map f) g) ≫
        (openProjectionIso R j a b M' N').hom =
      (openProjectionIso R j a b M N).hom ≫
        (openExtension R j).mapDerivedCategory.map
          (a.tensor.map (Prod.mkHom f ((pull R j).map g))) := by
  let e : (((𝟭 _).prod (pull R j)) ⋙ a.tensor) ⋙
      (openExtension R j).mapDerivedCategory ≅
        ((openExtension R j).mapDerivedCategory.prod (𝟭 _)) ⋙ b.tensor :=
    NatIso.ofComponents (fun MN ↦ (openProjectionIso R j a b MN.1 MN.2).symm)
      (fun h ↦ openProjectionInverse_naturality R j a b h.1 h.2)
  exact e.inv.naturality (Prod.mkHom f g)

private theorem tensor_iso_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : C ⥤ D) (T : A × B ⥤ C)
    {M : A} {N N' : B} {P : D}
    (p : P ≅ F.obj (T.obj (M, N))) (e : N ≅ N') :
    (p ≪≫ F.mapIso (T.mapIso (Iso.prod (Iso.refl M) e))).hom =
      p.hom ≫ F.map (T.map (Prod.mkHom (𝟙 M) e.hom)) := by
  rfl

private theorem factor_square_transport
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁]
    (JR : C₀ ⥤ C₁) (DZ : C₁ ⥤ D₁) (DX : C₀ ⥤ D₀) (JS : D₀ ⥤ D₁)
    (α : JR ⋙ DZ ⟶ DX ⋙ JS)
    {A : C₁} {B C : C₀} {E F : D₀}
    (p : A ⟶ JR.obj B) (t : B ⟶ C)
    (u : DX.obj C ⟶ F) (v : DX.obj B ⟶ E) (w : E ⟶ F)
    (h : DX.map t ≫ u = v ≫ w) :
    DZ.map (p ≫ JR.map t) ≫ α.app C ≫ JS.map u =
      DZ.map p ≫ α.app B ≫ JS.map v ≫ JS.map w := by
  rw [DZ.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ (α.app C)]
  have hn := α.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← JS.map_comp, h, JS.map_comp]

private theorem two_squares_transport
    {C : Type*} [Category C] {A B C₀ D E G H J : C}
    (m : A ⟶ B) (q : B ⟶ C₀) (r : D ⟶ E)
    (g : B ⟶ D) (h : C₀ ⟶ E) (p : C₀ ⟶ G) (s : E ⟶ H)
    (j : G ⟶ H) (k : H ⟶ J)
    (hp : h ≫ s = p ≫ j) (hq : q ≫ h = g ≫ r) :
    m ≫ q ≫ p ≫ j ≫ k = m ≫ g ≫ r ≫ s ≫ k := by
  rw [← reassoc_of% hp, reassoc_of% hq]

private theorem projectionOpenFactor_hom (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (K : DerivedCategory (pbcModules X (R.ring X)))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (projectionOpenFactor R c aX aZ hR K L).hom =
      (openProjectionIso R c.i aX aZ K ((pull R c.g).obj L)).hom ≫
        (openExtension R c.i).mapDerivedCategory.map
          (aX.tensor.map (Prod.mkHom (𝟙 K)
            (((geometricPullComposition R c.i c.g hR).symm ≪≫
              eqToIso (congrArg (fun g : X ⟶ Y ↦ pull R g) c.comm.symm)).hom.app L))) := by
  have hi : projectionOpenFactor R c aX aZ hR K L =
      openProjectionIso R c.i aX aZ K ((pull R c.g).obj L) ≪≫
        (openExtension R c.i).mapDerivedCategory.mapIso
          (aX.tensor.mapIso (Iso.prod (Iso.refl K)
            (((geometricPullComposition R c.i c.g hR).symm ≪≫
              eqToIso (congrArg (fun g : X ⟶ Y ↦ pull R g) c.comm.symm)).app L))) := rfl
  rw [hi]
  exact tensor_iso_hom (openExtension R c.i).mapDerivedCategory aX.tensor
    (openProjectionIso R c.i aX aZ K ((pull R c.g).obj L))
    (((geometricPullComposition R c.i c.g hR).symm ≪≫
      eqToIso (congrArg (fun g : X ⟶ Y ↦ pull R g) c.comm.symm)).app L)

private theorem scalarPull_triangle {R S : Coefficients.{u}} (a : Change R S)
    {X Z Y : Scheme.{u}} (h : X ⟶ Z) (k : Z ⟶ Y) (f : X ⟶ Y) (w : h ≫ k = f)
    (hR : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring Y) (R.ring Z) (R.ring X) (R.pull k) (R.pull h))
    (hS : S.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (S.ring Y) (S.ring Z) (S.ring X) (S.pull k) (S.pull h))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (pbcDerivedExtend (a.map X)).map
        (((geometricPullComposition R h k hR).symm ≪≫
          eqToIso (congrArg (fun g : X ⟶ Y ↦ pull R g) w)).hom.app L) ≫
        (scalarPull a f).hom.app L =
      (scalarPull a h).hom.app ((pull R k).obj L) ≫
        (pull S h).map ((scalarPull a k).hom.app L) ≫
        ((geometricPullComposition S h k hS).symm ≪≫
          eqToIso (congrArg (fun g : X ⟶ Y ↦ pull S g) w)).hom.app
            ((pbcDerivedExtend (a.map Y)).obj L) := by
  subst f
  simpa only [eqToIso_refl, Iso.trans_refl, Iso.symm_hom] using
    scalarPull_geometric_composition a h k hR hS L

/-- The compactification pullback compositor transports the open projection square.

Source: Stacks Project, Tags 0D6D, 07A6 and 0E8I.  The two equations are the
naturality/compositor part of the proof; they contain no open projection mate.
They are strictly simpler than the coefficient compatibility theorem itself.
(blueprint: lem-sf-open-projection-factor-compositor-transport).
-/
theorem openProjectionFactor_compositor_transport
    {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (bX : ProEtaleTensorModel X (S.ring X))
    (bZ : ProEtaleTensorModel c.Z (S.ring c.Z))
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (hS : S.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (S.ring Y) (S.ring c.Z) (S.ring X) (S.pull c.g) (S.pull c.i))
    (K : DerivedCategory (pbcModules X (R.ring X)))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (pbcDerivedExtend (a.map c.Z)).map
        (projectionOpenFactor R c aX aZ hR K L).hom ≫
      (openComparison a c.i).app
        (aX.tensor.obj (K, (pull R f).obj L)) ≫
      (openExtension S c.i).mapDerivedCategory.map
        ((scalarTensor (a.map X) aX bX).hom.app (K, (pull R f).obj L) ≫
          bX.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a f).hom.app L))) =
      (pbcDerivedExtend (a.map c.Z)).map
        (openProjectionIso R c.i aX aZ K ((pull R c.g).obj L)).hom ≫
      (openComparison a c.i).app
        (aX.tensor.obj (K, (pull R c.i).obj ((pull R c.g).obj L))) ≫
      (openExtension S c.i).mapDerivedCategory.map
        ((scalarTensor (a.map X) aX bX).hom.app
            (K, (pull R c.i).obj ((pull R c.g).obj L)) ≫
          bX.tensor.map (Prod.mkHom (𝟙 _)
            ((scalarPull a c.i).hom.app ((pull R c.g).obj L)))) ≫
      (openExtension S c.i).mapDerivedCategory.map
        (bX.tensor.map (Prod.mkHom (𝟙 _)
          ((pull S c.i).map ((scalarPull a c.g).hom.app L) ≫
            ((geometricPullComposition S c.i c.g hS).symm ≪≫
              eqToIso (congrArg (fun g : X ⟶ Y ↦ pull S g) c.comm.symm)).hom.app
                ((pbcDerivedExtend (a.map Y)).obj L)))) ∧
    (scalarTensor (a.map c.Z) aZ bZ).hom.app
        ((openExtension R c.i).mapDerivedCategory.obj K, (pull R c.g).obj L) ≫
      bZ.tensor.map (Prod.mkHom ((openComparison a c.i).app K) (𝟙 _)) ≫
      (openProjectionIso S c.i bX bZ
        ((pbcDerivedExtend (a.map X)).obj K)
        ((pbcDerivedExtend (a.map c.Z)).obj ((pull R c.g).obj L))).hom ≫
      (openExtension S c.i).mapDerivedCategory.map
        (bX.tensor.map (Prod.mkHom (𝟙 _)
          ((pull S c.i).map ((scalarPull a c.g).hom.app L) ≫
            ((geometricPullComposition S c.i c.g hS).symm ≪≫
              eqToIso (congrArg (fun g : X ⟶ Y ↦ pull S g) c.comm.symm)).hom.app
                ((pbcDerivedExtend (a.map Y)).obj L)))) =
    (scalarTensor (a.map c.Z) aZ bZ).hom.app
        ((openExtension R c.i).mapDerivedCategory.obj K, (pull R c.g).obj L) ≫
      bZ.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a c.g).hom.app L)) ≫
      bZ.tensor.map (Prod.mkHom ((openComparison a c.i).app K) (𝟙 _)) ≫
      (projectionOpenFactor S c bX bZ hS
        ((pbcDerivedExtend (a.map X)).obj K)
        ((pbcDerivedExtend (a.map Y)).obj L)).hom := by
  let ER := (geometricPullComposition R c.i c.g hR).symm ≪≫
    eqToIso (congrArg (fun g : X ⟶ Y ↦ pull R g) c.comm.symm)
  let ES := (geometricPullComposition S c.i c.g hS).symm ≪≫
    eqToIso (congrArg (fun g : X ⟶ Y ↦ pull S g) c.comm.symm)
  let J := (openExtension S c.i).mapDerivedCategory
  let D := pbcDerivedExtend (a.map X)
  let t := aX.tensor.map (Prod.mkHom (𝟙 K) (ER.hom.app L))
  have hp := scalarPull_triangle a c.i c.g f c.comm.symm hR hS L
  have ht := (scalarTensor (a.map X) aX bX).hom.naturality
    (Prod.mkHom (𝟙 K) (ER.hom.app L))
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  erw [(pbcDerivedExtend (a.map X)).map_id] at ht
  let μ₀ := (scalarTensor (a.map X) aX bX).hom.app
    (K, (pull R c.i).obj ((pull R c.g).obj L))
  let μ₁ := (scalarTensor (a.map X) aX bX).hom.app (K, (pull R f).obj L)
  let s₀ := (scalarPull a c.i).hom.app ((pull R c.g).obj L)
  let s₁ := (scalarPull a f).hom.app L
  let v := (pull S c.i).map ((scalarPull a c.g).hom.app L) ≫
    ES.hom.app ((pbcDerivedExtend (a.map Y)).obj L)
  have hinner : D.map t ≫ μ₁ ≫ bX.tensor.map (Prod.mkHom (𝟙 _) s₁) =
      μ₀ ≫ bX.tensor.map (Prod.mkHom (𝟙 _) s₀) ≫
        bX.tensor.map (Prod.mkHom (𝟙 _) v) := by
    calc
      _ = μ₀ ≫ bX.tensor.map (Prod.mkHom (𝟙 _) (D.map (ER.hom.app L))) ≫
          bX.tensor.map (Prod.mkHom (𝟙 _) s₁) := by
        simpa only [D, t, μ₀, μ₁, Functor.comp_obj,
          Category.assoc] using congrArg
            (fun z ↦ z ≫ bX.tensor.map (Prod.mkHom (𝟙 (D.obj K)) s₁)) ht
      _ = μ₀ ≫ bX.tensor.map
          (Prod.mkHom (𝟙 _) (D.map (ER.hom.app L) ≫ s₁)) := by
        rw [← bX.tensor.map_comp]
        simp only [prod_comp, Prod.mkHom, Category.id_comp]
      _ = μ₀ ≫ bX.tensor.map (Prod.mkHom (𝟙 _) (s₀ ≫ v)) := by rw [hp]
      _ = _ := by
        rw [← bX.tensor.map_comp]
        simp only [prod_comp, Prod.mkHom, Category.id_comp]
  constructor
  · rw [projectionOpenFactor_hom]
    exact factor_square_transport (openExtension R c.i).mapDerivedCategory
      (pbcDerivedExtend (a.map c.Z)) D J (openComparison a c.i)
      (openProjectionIso R c.i aX aZ K ((pull R c.g).obj L)).hom t
      (μ₁ ≫ bX.tensor.map (Prod.mkHom (𝟙 _) s₁))
      (μ₀ ≫ bX.tensor.map (Prod.mkHom (𝟙 _) s₀))
      (bX.tensor.map (Prod.mkHom (𝟙 _) v))
      (by simpa only [Category.assoc] using hinner)
  · let M := D.obj K
    let q := (openComparison a c.i).app K
    let g := (scalarPull a c.g).hom.app L
    let e := ES.hom.app ((pbcDerivedExtend (a.map Y)).obj L)
    have hn := openProjectionHom_naturality S c.i bX bZ (𝟙 M) g
    erw [(openExtension S c.i).mapDerivedCategory.map_id] at hn
    have hv : bX.tensor.map (Prod.mkHom (𝟙 M) ((pull S c.i).map g ≫ e)) =
        bX.tensor.map (Prod.mkHom (𝟙 M) ((pull S c.i).map g)) ≫
          bX.tensor.map (Prod.mkHom (𝟙 M) e) := by
      rw [← bX.tensor.map_comp]
      simp only [prod_comp, Prod.mkHom]
      erw [Category.id_comp]
    have hq : bZ.tensor.map (Prod.mkHom q (𝟙 _)) ≫
        bZ.tensor.map (Prod.mkHom (𝟙 _) g) =
      bZ.tensor.map (Prod.mkHom (𝟙 _) g) ≫
        bZ.tensor.map (Prod.mkHom q (𝟙 _)) := by
      rw [← bZ.tensor.map_comp, ← bZ.tensor.map_comp]
      simp only [prod_comp, Prod.mkHom, Category.id_comp, Category.comp_id]
    rw [projectionOpenFactor_hom]
    change _ ≫ _ ≫ _ ≫ J.map
      (bX.tensor.map (Prod.mkHom (𝟙 M) ((pull S c.i).map g ≫ e))) = _
    rw [hv, J.map_comp]
    exact two_squares_transport _ _ _ _ _ _ _ _ _ hn hq

end WeilConjectures.PurCompactSupport
