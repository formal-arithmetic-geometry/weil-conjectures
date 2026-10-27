/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SmoothPurityNormalizedEquivalence
public import Sheaf.Paper.IntegralDirectImageTower
public import Sheaf.Paper.IntegralAdjunctionBijection
public import Sheaf.Paper.TowerAdjointCompositorRealization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Total-limit realization of the adjoint composition comparisons

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-composition,
`sk-prop-sp-composition-comparisons.proof.md`, (1), (3)
(blueprint: lem-sp-integral-compositor-limit-realization).

All maps are maps of the ordinary derived categories of strict varying-coefficient towers.
The functor `realize` is exactly reduction, a tower operation, and total derived limit.
The two compositor definitions insert the middle equivalence counit in opposite directions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u v₁ v₂ v₃ w₁ w₂ w₃ h₁ h₂ h₃ j₁ j₂ j₃
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralCompositorLimit

section Categorical
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₃ : Type w₃}
  {N₁ : Type v₁} {N₂ : Type v₂} {N₃ : Type v₃}
  [Category.{h₁} I₁] [Category.{h₂} I₂] [Category.{h₃} I₃]
  [Category.{j₁} N₁] [Category.{j₂} N₂] [Category.{j₃} N₃]

/-- Conjugation by the specified reduction/total-limit equivalences, with real functor data.
Source: blueprint comparisons (3), integral realization
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def realize (e₁ : I₁ ≌ N₁) (e₂ : I₂ ≌ N₂) (F : N₁ ⥤ N₂) : I₁ ⥤ I₂ :=
  e₁.functor ⋙ F ⋙ e₂.inverse

/-- The canonical identification red L F red = F red, using the actual equivalence counit.
Source: blueprint comparisons (3), b_h and c_h
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def realizationReduction (e₁ : I₁ ≌ N₁) (e₂ : I₂ ≌ N₂) (F : N₁ ⥤ N₂) :
    realize e₁ e₂ F ⋙ e₂.functor ≅ e₁.functor ⋙ F :=
  Functor.isoWhiskerLeft e₁.functor
    (Functor.isoWhiskerLeft F e₂.counitIso ≪≫ Functor.rightUnitor F)

/-- Insert kappa in the middle: L G red L F red -> L G F red.
Source: blueprint comparisons (3), first displayed integral expression
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def realizationComposition (e₁ : I₁ ≌ N₁) (e₂ : I₂ ≌ N₂) (e₃ : I₃ ≌ N₃)
    (F : N₁ ⥤ N₂) (G : N₂ ⥤ N₃) :
    realize e₁ e₂ F ⋙ realize e₂ e₃ G ≅ realize e₁ e₃ (F ⋙ G) :=
  Functor.isoWhiskerLeft e₁.functor
    (Functor.isoWhiskerLeft F
      (Functor.isoWhiskerRight e₂.counitIso (G ⋙ e₃.inverse) ≪≫
        Functor.leftUnitor (G ⋙ e₃.inverse)))

private theorem composition_reduction
    (e₁ : I₁ ≌ N₁) (e₂ : I₂ ≌ N₂) (e₃ : I₃ ≌ N₃)
    (F : N₁ ⥤ N₂) (G : N₂ ⥤ N₃) (M : I₁) :
    e₃.functor.map ((realizationComposition e₁ e₂ e₃ F G).hom.app M) ≫
        (realizationReduction e₁ e₃ (F ⋙ G)).hom.app M =
      (realizationReduction e₂ e₃ G).hom.app ((realize e₁ e₂ F).obj M) ≫
        G.map ((realizationReduction e₁ e₂ F).hom.app M) := by
  simp [realizationComposition, realizationReduction, realize]

private theorem comparison_reduction
    (e₁ : I₁ ≌ N₁) (e₂ : I₂ ≌ N₂) (e₃ : I₃ ≌ N₃)
    {A : I₁ ⥤ I₂} {B : I₂ ⥤ I₃} {C : I₁ ⥤ I₃}
    {F : N₁ ⥤ N₂} {G : N₂ ⥤ N₃} {H : N₁ ⥤ N₃}
    (a : A ≅ realize e₁ e₂ F) (b : B ≅ realize e₂ e₃ G)
    (c : C ≅ realize e₁ e₃ H) (alpha : F ⋙ G ≅ H) (M : I₁) :
    e₃.functor.map
      (((Functor.isoWhiskerRight a B ≪≫ Functor.isoWhiskerLeft _ b ≪≫
        realizationComposition e₁ e₂ e₃ F G ≪≫
        Functor.isoWhiskerLeft e₁.functor (Functor.isoWhiskerRight alpha e₃.inverse) ≪≫
        c.symm).hom.app M)) ≫
        (Functor.isoWhiskerRight c e₃.functor ≪≫
          realizationReduction e₁ e₃ H).hom.app M =
      (Functor.isoWhiskerRight b e₃.functor ≪≫
          realizationReduction e₂ e₃ G).hom.app (A.obj M) ≫
        G.map ((Functor.isoWhiskerRight a e₂.functor ≪≫
          realizationReduction e₁ e₂ F).hom.app M) ≫ alpha.hom.app (e₁.functor.obj M) := by
  have hw : e₃.functor.map (e₃.inverse.map (alpha.hom.app (e₁.functor.obj M))) ≫
      (realizationReduction e₁ e₃ H).hom.app M =
      (realizationReduction e₁ e₃ (F ⋙ G)).hom.app M ≫
        alpha.hom.app (e₁.functor.obj M) := by
    simp [realizationReduction, realize]
  have hb := congrArg e₃.functor.map (b.hom.naturality (a.hom.app M))
  have hd := (realizationReduction e₂ e₃ G).hom.naturality (a.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hb hd
  simp only [Functor.map_comp] at hb
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← e₃.functor.map_comp_assoc (c.inv.app M) (c.hom.app M),
    c.inv_hom_id_app, e₃.functor.map_id, Category.id_comp]
  rw [hw, reassoc_of% (composition_reduction e₁ e₂ e₃ F G M)]
  rw [← Category.assoc (e₃.functor.map (B.map _)) (e₃.functor.map (b.hom.app _)), hb]
  simp only [Category.assoc]
  rw [← Category.assoc (e₃.functor.map ((realize e₂ e₃ G).map _))
    ((realizationReduction e₂ e₃ G).hom.app _), hd]
  simp only [Category.assoc]

private theorem inverse_comparison_reduction
    (e₁ : I₁ ≌ N₁) (e₂ : I₂ ≌ N₂) (e₃ : I₃ ≌ N₃)
    {F : N₁ ⥤ N₂} {G : N₂ ⥤ N₃} {H : N₁ ⥤ N₃}
    (theta : H ≅ F ⋙ G) (M : I₁) :
    e₃.functor.map
      (((Functor.isoWhiskerLeft e₁.functor
        (Functor.isoWhiskerRight theta e₃.inverse) ≪≫
        (realizationComposition e₁ e₂ e₃ F G).symm).hom.app M)) ≫
      (realizationReduction e₂ e₃ G).hom.app ((realize e₁ e₂ F).obj M) ≫
        G.map ((realizationReduction e₁ e₂ F).hom.app M) =
      (realizationReduction e₁ e₃ H).hom.app M ≫ theta.hom.app (e₁.functor.obj M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← composition_reduction e₁ e₂ e₃ F G M]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp [realizationReduction, realize]

private theorem composite_counit_reduction
    (r₁ : I₁ ⥤ N₁) (r₂ : I₂ ⥤ N₂) (r₃ : I₃ ⥤ N₃)
    {A : I₁ ⥤ I₂} {B : I₂ ⥤ I₃} {R : I₂ ⥤ I₁} {S : I₃ ⥤ I₂}
    {F : N₁ ⥤ N₂} {G : N₂ ⥤ N₃} {P : N₂ ⥤ N₁} {Q : N₃ ⥤ N₂}
    (a : A ⊣ R) (b : B ⊣ S) (f : F ⊣ P) (g : G ⊣ Q)
    (ba : A ⋙ r₂ ≅ r₁ ⋙ F) (bb : B ⋙ r₃ ≅ r₂ ⋙ G)
    (ca : R ⋙ r₁ ≅ r₂ ⋙ P) (cb : S ⋙ r₂ ≅ r₃ ⋙ Q)
    (ha : ∀ K, r₂.map (a.counit.app K) =
      ba.hom.app (R.obj K) ≫ F.map (ca.hom.app K) ≫ f.counit.app (r₂.obj K))
    (hb : ∀ K, r₃.map (b.counit.app K) =
      bb.hom.app (S.obj K) ≫ G.map (cb.hom.app K) ≫ g.counit.app (r₃.obj K))
    (K : I₃) :
    r₃.map ((a.comp b).counit.app K) =
      bb.hom.app (A.obj (R.obj (S.obj K))) ≫
        G.map (ba.hom.app (R.obj (S.obj K))) ≫
        (F ⋙ G).map (ca.hom.app (S.obj K) ≫ P.map (cb.hom.app K)) ≫
        (f.comp g).counit.app (r₃.obj K) := by
  rw [Adjunction.comp_counit_app, r₃.map_comp, hb]
  have hn := bb.hom.naturality (a.counit.app (S.obj K))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [ha]
  simp only [Functor.comp_map, Functor.map_comp, Adjunction.comp_counit_app,
    Category.assoc]
  have he := f.counit.naturality (cb.hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at he
  rw [← G.map_comp_assoc (f.counit.app _) (cb.hom.app K), ← he]
  simp only [Functor.map_comp, Category.assoc]

private theorem counit_comparison_transport
    (r₁ : I₁ ⥤ N₁) (r₂ : I₂ ⥤ N₂) [r₂.Faithful]
    {A B : I₁ ⥤ I₂} {R S : I₂ ⥤ I₁}
    {F G : N₁ ⥤ N₂} {P Q : N₂ ⥤ N₁}
    (a : A ⊣ R) (b : B ⊣ S) (f : F ⊣ P) (g : G ⊣ Q)
    (ba : A ⋙ r₂ ≅ r₁ ⋙ F) (bb : B ⋙ r₂ ≅ r₁ ⋙ G)
    (ca : R ⋙ r₁ ≅ r₂ ⋙ P) (cb : S ⋙ r₁ ≅ r₂ ⋙ Q)
    (ha : ∀ K, r₂.map (a.counit.app K) =
      ba.hom.app (R.obj K) ≫ F.map (ca.hom.app K) ≫ f.counit.app (r₂.obj K))
    (hb : ∀ K, r₂.map (b.counit.app K) =
      bb.hom.app (S.obj K) ≫ G.map (cb.hom.app K) ≫ g.counit.app (r₂.obj K))
    (alpha : A ≅ B) (theta : S ≅ R) (al : F ≅ G) (th : Q ≅ P)
    (hl : ∀ M, r₂.map (alpha.hom.app M) ≫ bb.hom.app M =
      ba.hom.app M ≫ al.hom.app (r₁.obj M))
    (hr : ∀ K, r₁.map (theta.hom.app K) ≫ ca.hom.app K =
      cb.hom.app K ≫ th.hom.app (r₂.obj K))
    (hc : ∀ K, F.map (th.hom.app K) ≫ f.counit.app K =
      al.hom.app (Q.obj K) ≫ g.counit.app K) (K : I₂) :
    A.map (theta.hom.app K) ≫ a.counit.app K =
      alpha.hom.app (S.obj K) ≫ b.counit.app K := by
  apply r₂.map_injective
  simp only [Functor.map_comp]
  rw [ha, hb]
  have hn := ba.hom.naturality (theta.hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hr]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc]
  have hn' := al.hom.naturality (cb.hom.app K)
  simp only [Functor.comp_obj] at hn'
  rw [reassoc_of% hn', ← reassoc_of% (hl (S.obj K))]

end Categorical

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified constructible restriction of the normalized equivalence. Equalities
identify both functors with the recorded reduction and total limit; HEq records the same
unit and counit when these equalities identify their endpoints. No object is chosen here.
Source: det-sp-normalized-equivalence and integral adjunction Normalization
(blueprint: lem-sp-integral-compositor-limit-realization). -/
structure Space (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) where
  reduction : SpReductionTower l E T D
  normalized : SpNormalizedEquivalence l E T D reduction
  equivalence : sfIntegralConstructibleCategory l E T ≌
    spNormalizedConstructibleTorTowerCategory l E T D
  reduction_eq : equivalence.functor ⋙ (spNormalizedConstructibleTorTowers l E T D).ι =
    SpIntegralAdjunction.reduction l E T D reduction
  limit_eq : equivalence.inverse ⋙ (sfIntegralConstructible l E T).ι =
    (spNormalizedConstructibleTorTowers l E T D).ι ⋙
      SpIntegralAdjunction.limit l E T D reduction normalized
  unit_eq : ∀ M : sfIntegralConstructibleCategory l E T,
    HEq ((sfIntegralConstructible l E T).ι.map (equivalence.unitIso.hom.app M))
      (normalized.adjunction.unit.app M.obj)
  counit_eq : ∀ C : spNormalizedConstructibleTorTowerCategory l E T D,
    HEq ((spNormalizedConstructibleTorTowers l E T D).ι.map
      (equivalence.counitIso.hom.app C)) (normalized.adjunction.counit.app C.obj)

/-- The existing full inclusion of normalized towers into uniform constructible towers.
Source: blueprint comparisons (3), restriction to N
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def inclusion (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    spNormalizedConstructibleTorTowerCategory l E T D ⥤
      spConstructibleTorTowerCategory l E T D :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.1)

/-- Restrict an actual tower functor to normalized towers, retaining its derived maps.
Source: blueprint comparisons (3), six functors preserve N
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def restrict {X Y : Scheme.{u}}
    (DX : SpCoefficientTowersAbelian l E X) (DY : SpCoefficientTowersAbelian l E Y)
    (F : spConstructibleTorTowerCategory l E X DX ⥤
      spConstructibleTorTowerCategory l E Y DY)
    (h : ∀ C : spConstructibleTorTowerCategory l E X DX,
      IsSpNormalizedTower l E X DX C.obj →
      IsSpNormalizedTower l E Y DY (F.obj C).obj) :
    spNormalizedConstructibleTorTowerCategory l E X DX ⥤
      spNormalizedConstructibleTorTowerCategory l E Y DY :=
  (spNormalizedConstructibleTorTowers l E Y DY).lift
    (inclusion l E X DX ⋙ F ⋙ (spConstructibleTorTowers l E Y DY).ι)
    (fun C ↦ ⟨(F.obj ((inclusion l E X DX).obj C)).property,
      h _ C.property.2⟩)

variable (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The tower adjunction supplied by the recorded compositor node, with its normalization
preservation. This is a package of the stated input, not a replacement tower operation.
Source: blueprint comparisons (3), given tower functors
(blueprint: lem-sp-integral-compositor-limit-realization). -/
structure TowerEdge {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  pair : TowerAdjointCompositor.Pair l E b o q c
  preserves : TowerAdjointCompositor.PreservesNormalized l E b o q pair

/-- The actual normalized compact-support tower functor.
Source: blueprint comparisons (3), F_bullet on N
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def towerLeft {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (P : TowerEdge l E b o q c) :=
  restrict l E (q.abelian X) (q.abelian Y)
    (TowerAdjointCompositor.left l E b o q P.pair) P.preserves.1

/-- The actual normalized exceptional tower functor.
Source: blueprint comparisons (3), H_bullet on N
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def towerRight {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (P : TowerEdge l E b o q c) :=
  restrict l E (q.abelian Y) (q.abelian X) P.pair.right P.preserves.2

/-- Restrict the actual tower adjunction along the full normalized inclusions.
Source: blueprint comparisons (1), (3), counit-preserving restriction
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def towerAdjunction {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (P : TowerEdge l E b o q c) : towerLeft l E b o q P ⊣ towerRight l E b o q P :=
  P.pair.adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1))
    (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1)) (Iso.refl _) (Iso.refl _)

/-- The specified integral compact-support comparison with total limit, and the integral
adjunction normalized by the given Hom chain. The left functor is the independently
constructed completed-ring Rp_* j_!, and the right functor is L H_bullet red.
Source: det-sp-integral-direct-image-tower (2), det-sp-integral-adjunction-bijection
(blueprint: lem-sp-integral-compositor-limit-realization). -/
structure IntegralEdge {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : Space l E X (q.abelian X)) (T : Space l E Y (q.abelian Y))
    (P : TowerEdge l E b o q c) where
  closed : ∀ M : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((CompleteCompactificationLimit.image l E c).obj M.obj)
  comparison : SpIntegralAdjunction.support l E c closed ≅
    realize S.equivalence T.equivalence (towerLeft l E b o q P)
  adjunction : SpIntegralAdjunction.support l E c closed ⊣
    realize T.equivalence S.equivalence (towerRight l E b o q P)
  hom_eq : adjunction = (towerAdjunction l E b o q P).restrictFullyFaithful
    S.equivalence.fullyFaithfulFunctor T.equivalence.fullyFaithfulFunctor
    ((Functor.isoWhiskerRight comparison T.equivalence.functor ≪≫
      realizationReduction S.equivalence T.equivalence (towerLeft l E b o q P)).symm)
    (realizationReduction T.equivalence S.equivalence (towerRight l E b o q P)).symm

/-- Reduction of the actual integral compact-support functor through its specified
comparison and kappa. Source: blueprint comparisons (3), b_h
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def leftReduction {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : Space l E X (q.abelian X)} {T : Space l E Y (q.abelian Y)}
    {P : TowerEdge l E b o q c} (J : IntegralEdge l E b o q S T P) :=
  Functor.isoWhiskerRight J.comparison T.equivalence.functor ≪≫
    realizationReduction S.equivalence T.equivalence (towerLeft l E b o q P)

private theorem integral_counit_reduction
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S : Space l E X (q.abelian X)} {T : Space l E Y (q.abelian Y)}
    {P : TowerEdge l E b o q c} (J : IntegralEdge l E b o q S T P)
    (K : sfIntegralConstructibleCategory l E Y) :
    T.equivalence.functor.map (J.adjunction.counit.app K) =
      (leftReduction l E b o q J).hom.app
          ((realize T.equivalence S.equivalence (towerRight l E b o q P)).obj K) ≫
        (towerLeft l E b o q P).map
          ((realizationReduction T.equivalence S.equivalence
            (towerRight l E b o q P)).hom.app K) ≫
        (towerAdjunction l E b o q P).counit.app (T.equivalence.functor.obj K) := by
  rw [J.hom_eq, Adjunction.map_restrictFullyFaithful_counit_app]
  rfl

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {cf : Compactification f} {cg : Compactification g} {ch : Compactification (f ≫ g)}
  (S : Space l E X (q.abelian X)) (T : Space l E Y (q.abelian Y))
  (U : Space l E Z (q.abelian Z))
  (Pf : TowerEdge l E b o q cf) (Pg : TowerEdge l E b o q cg)
  (Ph : TowerEdge l E b o q ch)
  (Jf : IntegralEdge l E b o q S T Pf) (Jg : IntegralEdge l E b o q T U Pg)
  (Jh : IntegralEdge l E b o q S U Ph)

/-- The first displayed integral composition expression, through the specified comparisons.
Its middle map is L_Z F_g kappa_Y F_f red_X, followed by L_Z alpha red_X.
Source: blueprint comparisons (3), first expression
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def leftCompositor
    (alpha : towerLeft l E b o q Pf ⋙ towerLeft l E b o q Pg ≅ towerLeft l E b o q Ph) :
    SpIntegralAdjunction.support l E cf Jf.closed ⋙
        SpIntegralAdjunction.support l E cg Jg.closed ≅
      SpIntegralAdjunction.support l E ch Jh.closed :=
  Functor.isoWhiskerRight Jf.comparison (SpIntegralAdjunction.support l E cg Jg.closed) ≪≫
    Functor.isoWhiskerLeft _ Jg.comparison ≪≫
    realizationComposition S.equivalence T.equivalence U.equivalence
      (towerLeft l E b o q Pf) (towerLeft l E b o q Pg) ≪≫
    Functor.isoWhiskerLeft S.equivalence.functor
      (Functor.isoWhiskerRight alpha U.equivalence.inverse) ≪≫ Jh.comparison.symm

/-- The second displayed integral expression: L_X theta red_Z followed by the inverse
of L_X H_f kappa_Y H_g red_Z. Source: blueprint comparisons (3), second expression
(blueprint: lem-sp-integral-compositor-limit-realization). -/
def rightCompositor
    (theta : towerRight l E b o q Ph ≅ towerRight l E b o q Pg ⋙ towerRight l E b o q Pf) :
    realize U.equivalence S.equivalence (towerRight l E b o q Ph) ≅
      realize U.equivalence T.equivalence (towerRight l E b o q Pg) ⋙
        realize T.equivalence S.equivalence (towerRight l E b o q Pf) :=
  Functor.isoWhiskerLeft U.equivalence.functor
    (Functor.isoWhiskerRight theta S.equivalence.inverse) ≪≫
    (realizationComposition U.equivalence T.equivalence S.equivalence
      (towerRight l E b o q Pg) (towerRight l E b o q Pf)).symm

/-- The two reduction equations, integral counit normalization and uniqueness. Unit and
counit reduction use exactly the Hom-chain adjunctions supplied in IntegralEdge.
Source: blueprint comparisons (1), (3)
(blueprint: lem-sp-integral-compositor-limit-realization). -/
structure Laws
    (alpha : towerLeft l E b o q Pf ⋙ towerLeft l E b o q Pg ≅ towerLeft l E b o q Ph)
    (theta : towerRight l E b o q Ph ≅ towerRight l E b o q Pg ⋙ towerRight l E b o q Pf) :
    Prop where
  left_reduction : ∀ M : sfIntegralConstructibleCategory l E X,
    U.equivalence.functor.map
        ((leftCompositor l E b o q S T U Pf Pg Ph Jf Jg Jh alpha).hom.app M) ≫
        (leftReduction l E b o q Jh).hom.app M =
      (leftReduction l E b o q Jg).hom.app
          ((SpIntegralAdjunction.support l E cf Jf.closed).obj M) ≫
        (towerLeft l E b o q Pg).map ((leftReduction l E b o q Jf).hom.app M) ≫
        alpha.hom.app (S.equivalence.functor.obj M)
  right_reduction : ∀ K : sfIntegralConstructibleCategory l E Z,
    S.equivalence.functor.map
        ((rightCompositor l E b o q S T U Pf Pg Ph theta).hom.app K) ≫
      (realizationReduction T.equivalence S.equivalence
        (towerRight l E b o q Pf)).hom.app
          ((realize U.equivalence T.equivalence (towerRight l E b o q Pg)).obj K) ≫
      (towerRight l E b o q Pf).map
        ((realizationReduction U.equivalence T.equivalence
          (towerRight l E b o q Pg)).hom.app K) =
      (realizationReduction U.equivalence S.equivalence
        (towerRight l E b o q Ph)).hom.app K ≫
        theta.hom.app (U.equivalence.functor.obj K)
  counit : ∀ K : sfIntegralConstructibleCategory l E Z,
    (SpIntegralAdjunction.support l E cf Jf.closed ⋙
        SpIntegralAdjunction.support l E cg Jg.closed).map
          ((rightCompositor l E b o q S T U Pf Pg Ph theta).hom.app K) ≫
      (Jf.adjunction.comp Jg.adjunction).counit.app K =
      (leftCompositor l E b o q S T U Pf Pg Ph Jf Jg Jh alpha).hom.app
        ((realize U.equivalence S.equivalence (towerRight l E b o q Ph)).obj K) ≫
        Jh.adjunction.counit.app K
  unique : ∀ t : realize U.equivalence S.equivalence (towerRight l E b o q Ph) ⟶
      realize U.equivalence T.equivalence (towerRight l E b o q Pg) ⋙
        realize T.equivalence S.equivalence (towerRight l E b o q Pf),
    (∀ K, (SpIntegralAdjunction.support l E cf Jf.closed ⋙
        SpIntegralAdjunction.support l E cg Jg.closed).map (t.app K) ≫
      (Jf.adjunction.comp Jg.adjunction).counit.app K =
      (leftCompositor l E b o q S T U Pf Pg Ph Jf Jg Jh alpha).hom.app
        ((realize U.equivalence S.equivalence (towerRight l E b o q Ph)).obj K) ≫
        Jh.adjunction.counit.app K) →
      t = (rightCompositor l E b o q S T U Pf Pg Ph theta).hom
  composite_counit : ∀ K : sfIntegralConstructibleCategory l E Z,
    (Jf.adjunction.comp Jg.adjunction).counit.app K =
      (SpIntegralAdjunction.support l E cg Jg.closed).map
        (Jf.adjunction.counit.app
          ((realize U.equivalence T.equivalence (towerRight l E b o q Pg)).obj K)) ≫
        Jg.adjunction.counit.app K

/-- The displayed total-limit constructions give the integral composition isomorphisms;
their reductions are the given tower compositors, and the right one is the unique
counit-preserving adjunction comparison for the left one. This includes E = Q_ell.
Source: latest blueprint comparisons proof (1), (3)
(blueprint: lem-sp-integral-compositor-limit-realization).

Proof, following the six DAG steps:
1. det-sp-normalized-equivalence identifies the integral and normalized tower categories.
The direct-image comparison and det-sp-integral-adjunction-bijection identify the actual
integral functors and Hom chains. Set b_h=kappa F_h red and c_h=kappa H_h red.
2. Insert the middle equivalence counit, then apply total limit to alpha. For theta,
apply total limit first and insert the inverse middle counit. These are precisely
leftCompositor and rightCompositor; whiskering and composition preserve natural isomorphisms.
3. Naturality of kappa gives both reduction identities. Every normalized tower is
isomorphic to red L of itself, so these identities apply to every normalized input.
4. lem-sp-fully-faithful-adjunction-restriction gives the unit and counit formulas.
Compose the Hom chains: the intermediate full-faithfulness bijections cancel. The
composite counit is epsilon_g after F_g epsilon_f, by def-weil-pbc-composite-adjunction.
5. Reduce the proposed integral counit equation. Substitute the two reduction identities,
use naturality of b and alpha, and use the given tower counit equation from
lem-sp-tower-adjoint-compositor-realization. Faithfulness of reduction proves the equation.
6. Transport the gf adjunction through the left compositor. det-sp-unique-right-adjoint
identifies its right adjoint with the composite, uniquely by the counit equation.
The units are transposes of identities, so they have the same normalization. No restriction
on the degree of E was used, and its degree-one case gives E=Q_ell. -/
theorem integralCompositorLimitRealization
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (alpha : towerLeft l E b o q Pf ⋙ towerLeft l E b o q Pg ≅ towerLeft l E b o q Ph)
    (theta : towerRight l E b o q Ph ≅ towerRight l E b o q Pg ⋙ towerRight l E b o q Pf)
    (_towerCounit : ∀ K,
      (towerLeft l E b o q Pf ⋙ towerLeft l E b o q Pg).map (theta.hom.app K) ≫
        ((towerAdjunction l E b o q Pf).comp (towerAdjunction l E b o q Pg)).counit.app K =
      alpha.hom.app ((towerRight l E b o q Ph).obj K) ≫
        (towerAdjunction l E b o q Ph).counit.app K) :
    Laws l E b o q S T U Pf Pg Ph Jf Jg Jh alpha theta := by
  have hl := comparison_reduction S.equivalence T.equivalence U.equivalence
    Jf.comparison Jg.comparison Jh.comparison alpha
  have hr := inverse_comparison_reduction U.equivalence T.equivalence S.equivalence theta
  let bc : (SpIntegralAdjunction.support l E cf Jf.closed ⋙
      SpIntegralAdjunction.support l E cg Jg.closed) ⋙ U.equivalence.functor ≅
      S.equivalence.functor ⋙ (towerLeft l E b o q Pf ⋙ towerLeft l E b o q Pg) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (SpIntegralAdjunction.support l E cf Jf.closed)
        (leftReduction l E b o q Jg) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (leftReduction l E b o q Jf) (towerLeft l E b o q Pg) ≪≫
      Functor.associator _ _ _
  let cc : (realize U.equivalence T.equivalence (towerRight l E b o q Pg) ⋙
      realize T.equivalence S.equivalence (towerRight l E b o q Pf)) ⋙
        S.equivalence.functor ≅
      U.equivalence.functor ⋙ (towerRight l E b o q Pg ⋙ towerRight l E b o q Pf) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (realize U.equivalence T.equivalence (towerRight l E b o q Pg))
        (realizationReduction T.equivalence S.equivalence (towerRight l E b o q Pf)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (realizationReduction U.equivalence T.equivalence (towerRight l E b o q Pg))
        (towerRight l E b o q Pf) ≪≫ Functor.associator _ _ _
  have hf := integral_counit_reduction l E b o q Jf
  have hg := integral_counit_reduction l E b o q Jg
  have hh := integral_counit_reduction l E b o q Jh
  have hc : ∀ K,
      (SpIntegralAdjunction.support l E cf Jf.closed ⋙
        SpIntegralAdjunction.support l E cg Jg.closed).map
          ((rightCompositor l E b o q S T U Pf Pg Ph theta).hom.app K) ≫
        (Jf.adjunction.comp Jg.adjunction).counit.app K =
      (leftCompositor l E b o q S T U Pf Pg Ph Jf Jg Jh alpha).hom.app
        ((realize U.equivalence S.equivalence (towerRight l E b o q Ph)).obj K) ≫
        Jh.adjunction.counit.app K := by
    intro K
    apply counit_comparison_transport S.equivalence.functor U.equivalence.functor
      (Jf.adjunction.comp Jg.adjunction) Jh.adjunction
      ((towerAdjunction l E b o q Pf).comp (towerAdjunction l E b o q Pg))
      (towerAdjunction l E b o q Ph) bc (leftReduction l E b o q Jh) cc
      (realizationReduction U.equivalence S.equivalence (towerRight l E b o q Ph))
      _ hh (leftCompositor l E b o q S T U Pf Pg Ph Jf Jg Jh alpha)
      (rightCompositor l E b o q S T U Pf Pg Ph theta) alpha theta _ _ _towerCounit K
    · intro K
      simp only [bc, cc, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc]
      exact composite_counit_reduction S.equivalence.functor T.equivalence.functor
        U.equivalence.functor Jf.adjunction Jg.adjunction
        (towerAdjunction l E b o q Pf) (towerAdjunction l E b o q Pg)
        (leftReduction l E b o q Jf) (leftReduction l E b o q Jg)
        (realizationReduction T.equivalence S.equivalence (towerRight l E b o q Pf))
        (realizationReduction U.equivalence T.equivalence (towerRight l E b o q Pg))
        hf hg K
    · intro M
      simpa only [bc, leftCompositor, leftReduction, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc] using hl M
    · intro K
      simpa only [cc, rightCompositor, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc] using hr K
  refine ⟨hl, hr, hc, ?_, ?_⟩
  · intro t ht
    apply NatTrans.ext
    funext K
    apply ((Jf.adjunction.comp Jg.adjunction).homEquiv _ K).symm.injective
    exact (ht K).trans (hc K).symm
  · exact fun K ↦ Adjunction.comp_counit_app Jf.adjunction Jg.adjunction K

end AlgebraicGeometry.ProEtale.IntegralCompositorLimit
