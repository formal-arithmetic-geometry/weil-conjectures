/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerExceptionalBaseChange

/-! # Named compactification coordinates for tower purity base change

These constructions let the orientation and tensor steps be proved independently
without an import cycle. Gamma uses its equivalent factor formula directly, avoiding
a dependent compactification elimination; the other constructors are unchanged.
Source: latest blueprint smooth-purity base-change factors.
(blueprint: def-sp-purity-bc-tower-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

private theorem tensorComparison_naturality
    {C : Type*} [Category C] {D : Type*} [Category D]
    (T : C × C ⥤ C) (T' : D × D ⥤ D) (U : C ⥤ D)
    (c : T ⋙ U ≅ (U.prod U) ⋙ T')
    {A : C} {A' : D} (j : U.obj A ⟶ A') {W W' : C} (h : W ⟶ W') :
    U.map (T.map (Prod.mkHom (𝟙 A) h)) ≫
        (c.hom.app (A, W') ≫ T'.map (Prod.mkHom j (𝟙 (U.obj W')))) =
      (c.hom.app (A, W) ≫ T'.map (Prod.mkHom j (𝟙 (U.obj W)))) ≫
        T'.map (Prod.mkHom (𝟙 A') (U.map h)) := by
  have hn := c.hom.naturality (Prod.mkHom (𝟙 A) h)
  change U.map (T.map (Prod.mkHom (𝟙 A) h)) ≫ c.hom.app (A, W') =
    c.hom.app (A, W) ≫ T'.map (Prod.mkHom (U.map (𝟙 A)) (U.map h)) at hn
  rw [U.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, Category.assoc]
  congr 1
  simp only [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]

section Towers
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  {f : X ⟶ Y} [QuasiCompact f] [HasCompactification f]
  (c : Compactification f) (d : ℕ) (w : SpChartAdmissibility.Twists ell E X)
  (hF : ∀ M : SpTowerCalculus.C ell E b q X,
    spConstructibleTorTowers ell E Y (q.abelian Y)
      ((SpTowerCalculus.F ell E b o q c).obj M.obj))
  (G : SpTowerCalculus.C ell E b q Y ⥤ SpTowerCalculus.C ell E b q X)
  (adj : SpTowerGluing.support ell E b o q c hF ⊣ G)
  (lv : SpTowerGluing.Levels ell E b o q c hF G adj)

/-- Reindex the published finite-level adjunction package along the same
compactification equation. Its evaluation comparisons are retained by transport.
Source: factors, use of det-sp-tower-gluing (blueprint: det-sp-purity-bc-factors). -/
def towerFactorizationLevels :
    SpTowerGluing.Levels ell E b o q (SpTowerGamma.factorization c.i c.g) hF G adj := by
  rcases c with ⟨Z, p, j, rfl, hp, hj⟩
  exact lv

/-- The published tower purity data at a named compactification. Only the equality
c.i followed by c.g = f is transported; no new purity datum is introduced.
Source: det-sp-tower-gamma, (1)--(2) (blueprint: det-sp-purity-bc-factors). -/
def TowerPurityAt : Type _ :=
  letI : QuasiCompact (c.i ≫ c.g) := c.comm ▸ inferInstance
  letI : HasCompactification (c.i ≫ c.g) :=
    (SpTowerGamma.factorization c.i c.g).hasCompactification
  SpTowerGamma.Purity ell E b o q c.i c.g d w hF G adj
    (towerFactorizationLevels ell E b o q c hF G adj lv)

/-- The actual tensor/counit transpose, transporting the compactification equation.
Source: factors (2), t_K (blueprint: det-sp-purity-bc-factors). -/
def towerTensorMap (P : TowerPurityAt ell E b o q c d w hF G adj lv)
    (K : SpTowerCalculus.C ell E b q Y) :
    (SpTowerGamma.tensorSource ell E b o q f
      ((SpTowerGamma.exceptional ell E b q G).obj
        ⟨SpTowerGamma.originalUnit ell E b q Y, P.unit_mem⟩)).obj K ⟶
      (SpTowerGamma.exceptional ell E b q G).obj K := by
  rcases c with ⟨Z, p, j, rfl, hp, hj⟩
  exact SpTowerGamma.tensorMate ell E b o q (SpTowerGamma.factorization j p)
    P.tensorX P.tensorY hF G adj P.unit_mem K (P.tensor_mem K) (P.projection_iso K)

/-- The actual tower purity composite, transporting only the compactification equation.
Source: factors, consequence (blueprint: det-sp-purity-bc-factors). -/
def towerGamma (P : TowerPurityAt ell E b o q c d w hF G adj lv)
    (K : SpTowerCalculus.C ell E b q Y) :
    (SpTowerGamma.source ell E b o q f w d).obj K ⟶
      (SpTowerGamma.exceptional ell E b q G).obj K :=
  (SpTowerShriek.tensor ell E b X).map (Prod.mkHom (𝟙 _) P.orientation.hom) ≫
    towerTensorMap ell E b o q c d w hF G adj lv P K

/-- Expand tower gamma into its two factors, transporting only c.comm.
Source: latest blueprint purity-bc-factors, final paragraph
(blueprint: def-sp-purity-bc-tower-data). -/
theorem towerGamma_eq (P : TowerPurityAt ell E b o q c d w hF G adj lv)
    (K : SpTowerCalculus.C ell E b q Y) :
    towerGamma ell E b o q c d w hF G adj lv P K =
      (SpTowerShriek.tensor ell E b X).map (Prod.mkHom (𝟙 _) P.orientation.hom) ≫
        towerTensorMap ell E b o q c d w hF G adj lv P K := by
  rfl

end Towers

section TowerSquare
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)
  {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {v : Y' ⟶ Y} {sq : IsPullback u' f' f v}
  {c : Compactification f} (a : SpTowerMate.Data ell E b o q sq c)

/-- The given counit mate in the section-preserving realization. The first factor
is the realization counit inverse, not an independently selected comparison.
Source: factors, definition of e_K (blueprint: det-sp-purity-bc-factors). -/
def towerExchange (x : SpTowerShriek.OpenExchange ell E b o)
    (hb : IsIso (SpTowerMate.beta ell E b o q a x))
    (K : SpTowerCalculus.C ell E b q Y) :
    (SpTowerShriek.pull ell E b (o.geometry u')).obj
        ((SpTowerGamma.exceptional ell E b q a.right).obj K) ⟶
      (SpTowerGamma.exceptional ell E b q a.right').obj
        ((SpTowerMate.V ell E b o q a).obj K) :=
  (SpTowerCalculus.realization ell E b X' (q.abelian X')).counitIso.inv.app _ ≫
    (SpTowerCalculus.realization ell E b X' (q.abelian X')).functor.map
      ((SpTowerMate.mate ell E b o q a x hb).app K).hom

/-- Inverse-image composition around the given square, followed by the inverse of
the realization counit for v^*K. Source: factors (2), source identification
(blueprint: det-sp-purity-bc-factors). -/
def towerPullSquare (K : SpTowerCalculus.C ell E b q Y) :
    (SpTowerShriek.pull ell E b (o.geometry u')).obj
        ((SpTowerShriek.pull ell E b (o.geometry f)).obj
          ((SpTowerGamma.realization ell E b q Y).obj K)) ≅
      (SpTowerShriek.pull ell E b (o.geometry f')).obj
        ((SpTowerGamma.realization ell E b q Y').obj
          ((SpTowerMate.V ell E b o q a).obj K)) :=
  (SpTowerShriek.square ell E b o u' f' f v sq.w).symm.app _ ≪≫
    (SpTowerShriek.pull ell E b (o.geometry f')).mapIso
      ((SpTowerCalculus.realization ell E b Y' (q.abelian Y')).counitIso.symm.app _)

/-- The fixed tensor/pullback comparison and the square compositor, with no
exceptional orientation included. Source: factors (2), monoidal comparisons
(blueprint: det-sp-purity-bc-factors). -/
def towerTensorComparison (K : SpTowerCalculus.C ell E b q Y)
    (W : SpTowerShriek.D ell E X) :
    (SpTowerShriek.pull ell E b (o.geometry u')).obj
      ((SpTowerGamma.tensorSource ell E b o q f W).obj K) ≅
    (SpTowerShriek.tensor ell E b X').obj
      ((SpTowerShriek.pull ell E b (o.geometry f')).obj
        ((SpTowerGamma.realization ell E b q Y').obj
          ((SpTowerMate.V ell E b o q a).obj K)),
        (SpTowerShriek.pull ell E b (o.geometry u')).obj W) :=
  (o.geometry u').tensorPullback.app _ ≪≫
    (SpTowerShriek.tensor ell E b X').mapIso
      (Iso.prod (towerPullSquare ell E b o q a K) (Iso.refl _))

/-- The original strict-tower identification of v^*1 with 1, induced by the
specified section-model unit comparison. Source: factors, unit identification
(blueprint: det-sp-purity-bc-factors). -/
def towerUnitIdentification
    (hY : spConstructibleTorTowers ell E Y (q.abelian Y)
      (SpTowerGamma.originalUnit ell E b q Y))
    (hY' : spConstructibleTorTowers ell E Y' (q.abelian Y')
      (SpTowerGamma.originalUnit ell E b q Y'))
    (s : (SpTowerShriek.pull ell E b (o.geometry v)).obj
        (SpTowerGamma.unit ell E Y) ≅ SpTowerGamma.unit ell E Y') :
    (SpTowerMate.V ell E b o q a).obj
        ⟨SpTowerGamma.originalUnit ell E b q Y, hY⟩ ⟶
      ⟨SpTowerGamma.originalUnit ell E b q Y', hY'⟩ :=
  ObjectProperty.homMk
    ((SpTowerCalculus.realization ell E b Y' (q.abelian Y')).inverse.map
      ((SpTowerShriek.pull ell E b (o.geometry v)).map
        ((SpTowerCalculus.realization ell E b Y (q.abelian Y)).counitIso.hom.app
          (SpTowerGamma.unit ell E Y)) ≫ s.hom))

/-- The unit component of the same exceptional counit mate, with v^*1=1.
Source: factors (1), e_1 (blueprint: det-sp-purity-bc-factors). -/
def towerUnitExchange (x : SpTowerShriek.OpenExchange ell E b o)
    (hb : IsIso (SpTowerMate.beta ell E b o q a x))
    (hY : spConstructibleTorTowers ell E Y (q.abelian Y)
      (SpTowerGamma.originalUnit ell E b q Y))
    (hY' : spConstructibleTorTowers ell E Y' (q.abelian Y')
      (SpTowerGamma.originalUnit ell E b q Y'))
    (s : (SpTowerShriek.pull ell E b (o.geometry v)).obj
        (SpTowerGamma.unit ell E Y) ≅ SpTowerGamma.unit ell E Y') :
    (SpTowerShriek.pull ell E b (o.geometry u')).obj
      ((SpTowerGamma.exceptional ell E b q a.right).obj
        ⟨SpTowerGamma.originalUnit ell E b q Y, hY⟩) ⟶
    (SpTowerGamma.exceptional ell E b q a.right').obj
      ⟨SpTowerGamma.originalUnit ell E b q Y', hY'⟩ :=
  towerExchange ell E b o q a x hb _ ≫
    (SpTowerGamma.exceptional ell E b q a.right').map
      (towerUnitIdentification ell E b o q a hY hY' s)

/-- Naturality of the tensor comparison in its coefficient factor.
Source: latest blueprint purity-bc-factors, final composition
(blueprint: def-sp-purity-bc-tower-data). -/
theorem towerTensorComparison_naturality (K : SpTowerCalculus.C ell E b q Y)
    {W W' : SpTowerShriek.D ell E X} (h : W ⟶ W') :
    (SpTowerShriek.pull ell E b (o.geometry u')).map
        ((SpTowerShriek.tensor ell E b X).map (Prod.mkHom (𝟙 _) h)) ≫
        (towerTensorComparison ell E b o q a K W').hom =
      (towerTensorComparison ell E b o q a K W).hom ≫
        (SpTowerShriek.tensor ell E b X').map
          (Prod.mkHom (𝟙 _) ((SpTowerShriek.pull ell E b (o.geometry u')).map h)) := by
  exact tensorComparison_naturality (SpTowerShriek.tensor ell E b X)
    (SpTowerShriek.tensor ell E b X') (SpTowerShriek.pull ell E b (o.geometry u'))
    (o.geometry u').tensorPullback (towerPullSquare ell E b o q a K).hom h

end TowerSquare

end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
