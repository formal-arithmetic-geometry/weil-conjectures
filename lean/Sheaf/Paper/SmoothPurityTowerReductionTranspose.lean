/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.CoefficientTowerShriekInterfaces
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
import Sheaf.Paper.TowerIntrinsicShriekTransition

/-!
# The global counit transpose of a strict tower reduction

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Levels, final sentence
(blueprint: lem-sp-tower-reduction-transpose).

Index n means positive exponent n+1, as in the recorded tower interfaces. All
coordinate changes preserve sections or the specified adjunction unit. In particular
`reduction` below is the existing actual strict-tower reduction, not a chosen arrow.
No normalization is imposed on either tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.SpTowerCalculus

namespace AlgebraicGeometry.ProEtale.SpTowerReductionTranspose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : Coordinates l E b)

/-- Bundle an evaluated constructible finite-Tor tower in the existing full finite
subcategory. Source: blueprint, G_n and K_n, Levels
(blueprint: lem-sp-tower-reduction-transpose). -/
def level (T : Scheme.{u}) (M : C l E b q T) (n : ℕ) :
    spFiniteConstructibleTorCategory T (SpTowerShriek.R l E n) :=
  ⟨(spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj M.obj, M.property.1 n⟩

/-- Evaluate the actual tower counit using the inverse of the specified compact-support
evaluation comparison. Source: blueprint, evaluated representing pairs, Levels
(blueprint: lem-sp-tower-reduction-transpose). -/
def counit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (v : ∀ n : ℕ, Evaluation l E b o q c n)
    (G : C l E b q X) (K : C l E b q Y)
    (ε : (F l E b o q c).obj G.obj ⟶ K.obj) (n : ℕ) :
    (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj
        (level l E b q X G n).obj ⟶ (level l E b q Y K n).obj :=
  (v n).comparison.inv.app G.obj ≫
    (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map ε

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (hF : ∀ (n : ℕ) (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
      ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj M.obj))
  (hS : ∀ (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (M : spFiniteConstructibleTorCategory T (SpTowerShriek.R l E n)),
    spFiniteConstructibleTor T (SpTowerShriek.R l E m)
      ((scalarExtensionFunctor (quotient l E h) T).obj M.obj))
  (H : ∀ n : ℕ, spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n) ⥤
    spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n))
  (adj : ∀ n : ℕ, reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (hF n) ⊣ H n)
  (hb : ∀ {m n : ℕ} (h : m ≤ n)
    (L : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)),
    IsIso ((reductionDirectImageComparison (quotient l E h) c.i c.g).app ((H n).obj L).obj))

/-- The specified exceptional coefficient comparison: transpose the scalar extension
of the finite counit after the inverse of the proper-counit/open-tensor comparison.
This is the defining equation of det-sp-reduction-exceptional, not an arbitrary iso.
Source: blueprint, coefficient comparison c_(n,m), Levels
(blueprint: lem-sp-tower-reduction-transpose). -/
def comparison {m n : ℕ} (h : m ≤ n)
    (L : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :
    (reductionCtfScalar (quotient l E h) X (hS X h)).obj ((H n).obj L) ⟶
      (H m).obj ((reductionCtfScalar (quotient l E h) Y (hS Y h)).obj L) :=
  (adj m).homEquiv _ _ (ObjectProperty.homMk
    (@inv _ _ _ _ ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
        ((H n).obj L).obj) (hb h L) ≫
      (scalarExtensionFunctor (quotient l E h) Y).map ((adj n).counit.app L).hom))

/-- The reduction transported through the counit-preserving finite identifications.
Source: blueprint, reduction under iota_n and iota_m, Levels
(blueprint: lem-sp-tower-reduction-transpose). -/
def transportedReduction (G : C l E b q X) (K : C l E b q Y)
    (ι : ∀ n : ℕ, level l E b q X G n ≅ (H n).obj (level l E b q Y K n))
    {m n : ℕ} (h : m ≤ n) :
    (scalarExtensionFunctor (quotient l E h) X).obj
        ((H n).obj (level l E b q Y K n)).obj ⟶
      ((H m).obj (level l E b q Y K m)).obj :=
  (scalarExtensionFunctor (quotient l E h) X).map (ι n).inv.hom ≫
    reduction l E X (q.abelian X) h (q.scalar X h) G.obj ≫ (ι m).hom.hom

/-- The exceptional reduction word, with the input reduction sent through the finite
right adjoint. Source: blueprint, f_m^!(r_K) c_(n,m), Levels
(blueprint: lem-sp-tower-reduction-transpose). -/
def exceptionalReduction (K : C l E b q Y) {m n : ℕ} (h : m ≤ n) :
    (scalarExtensionFunctor (quotient l E h) X).obj
        ((H n).obj (level l E b q Y K n)).obj ⟶
      ((H m).obj (level l E b q Y K m)).obj :=
  (comparison l E b c hF hS H adj hb h (level l E b q Y K n)).hom ≫
    ((H m).map (ObjectProperty.homMk
      (X := (reductionCtfScalar (quotient l E h) Y (hS Y h)).obj
        (level l E b q Y K n))
      (Y := level l E b q Y K m)
      (reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj))).hom

/-- Identity and triple compatibility of actual reductions in intrinsic scalar
coordinates. Source: blueprint, identity and triple reductions
(blueprint: lem-sp-tower-reduction-transpose). -/
def ReductionCoherent (T : Scheme.{u})
    (M : spDerivedCoefficientTowers l E T (q.abelian T)) : Prop :=
  (∀ n : ℕ,
    reduction l E T (q.abelian T) (Nat.le_refl n) (q.scalar T (Nat.le_refl n)) M =
      (scalarUnit l E b q T n).hom.app
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj M)) ∧
  (∀ {r m n : ℕ} (h : r ≤ m) (a : m ≤ n),
    (scalarExtensionFunctor (quotient l E h) T).map
        (reduction l E T (q.abelian T) a (q.scalar T a) M) ≫
      reduction l E T (q.abelian T) h (q.scalar T h) M =
    (scalarAssoc l E b q T h a).hom.app
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj M) ≫
      reduction l E T (q.abelian T) (h.trans a) (q.scalar T (h.trans a)) M)

attribute [local implicit_reducible] level reductionCtfCompactSupport reductionCtfScalar
  catToReflQuiver Functor.category

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transpose_isIso_of_other_adjoints
    {C₀ D₀ C₁ D₁ : Type*} [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    {P : C₀ ⥤ D₀} {R R₀ : D₀ ⥤ C₀} {P' : C₁ ⥤ D₁} {R' R₀' : D₁ ⥤ C₁}
    (a : P ⊣ R) (a₀ : P ⊣ R₀) (a' : P' ⊣ R') (a₀' : P' ⊣ R₀')
    (S : C₀ ⥤ C₁) (T : D₀ ⥤ D₁) (β : P ⋙ T ≅ S ⋙ P')
    (z : ∀ K, S.obj (R.obj K) ⟶ R'.obj (T.obj K))
    (z₀ : ∀ K, S.obj (R₀.obj K) ⟶ R₀'.obj (T.obj K))
    (hz : ∀ K, P'.map (z K) ≫ a'.counit.app (T.obj K) =
      β.inv.app (R.obj K) ≫ T.map (a.counit.app K))
    (hz₀ : ∀ K, P'.map (z₀ K) ≫ a₀'.counit.app (T.obj K) =
      β.inv.app (R₀.obj K) ≫ T.map (a₀.counit.app K))
    (hi : ∀ K, IsIso (z₀ K)) (K : D₀) : IsIso (z K) := by
  let e := a₀.rightAdjointUniq a
  let e' := a₀'.rightAdjointUniq a'
  have heq : z K = S.map (e.inv.app K) ≫ z₀ K ≫ e'.hom.app (T.obj K) := by
    apply (a'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [hz]
    rw [Adjunction.rightAdjointUniq_hom_app_counit, hz₀]
    have hn := β.inv.naturality_assoc (e.inv.app K) (T.map (a₀.counit.app K))
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    rw [← T.map_comp]
    congr 2
    exact (Adjunction.rightAdjointUniq_hom_app_counit a a₀ K).symm
  rw [heq]
  have := hi K
  infer_instance

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem reduction_naturality (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    {M N : spDerivedCoefficientTowers l E T (q.abelian T)} (a : M ⟶ N) :
    (scalarExtensionFunctor (quotient l E h) T).map
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).map a) ≫
      reduction l E T (q.abelian T) h (q.scalar T h) N =
    reduction l E T (q.abelian T) h (q.scalar T h) M ≫
      (spDerivedCoefficientEvaluation l E T (q.abelian T) m).map a := by
  let t : spDerivedCoefficientEvaluation l E T (q.abelian T) n ⋙
      scalarExtensionFunctor (quotient l E h) T ⟶
        spDerivedCoefficientEvaluation l E T (q.abelian T) m :=
    Functor.whiskerLeft _ (q.scalar T h).scalar.inv ≫ (q.abelian T).reduction h
  exact t.naturality a

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem reduction_coherent (T : Scheme.{u})
    (M : spDerivedCoefficientTowers l E T (q.abelian T)) :
    ReductionCoherent l E b q T M := by
  constructor
  · intro n
    dsimp only [reduction]
    rw [(q.abelian T).reduction_identity]
    rfl
  · intro r m n h a
    dsimp only [reduction, scalarAssoc, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [(q.scalar T h).scalar.inv.naturality_assoc]
    erw [(q.abelian T).reduction_comp]
    simp only [Iso.hom_inv_id_app_assoc]
    unfold spDerivedCoefficientEvaluation
    rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coefficient_torsion {m n : ℕ} (h : m ≤ n)
    (x : SpTowerShriek.R l E m) : (l ^ (n + 1)) • x = 0 := by
  have hz : ((l ^ (n + 1) : ℕ) : SpTowerShriek.R l E m) = 0 := by
    have hm := Ideal.pow_mem_pow
      (Ideal.mem_span_singleton_self (l : Padic.coefficientExtensionIntegers l E)) (n + 1)
    have hi : spEllIdeal l E ^ (n + 1) ≤ spEllIdeal l E ^ (m + 1) :=
      Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr (hi hm))
  rw [nsmul_eq_mul, hz, zero_mul]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparison_counit {m n : ℕ} (h : m ≤ n)
    (L : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :
    (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (comparison l E b c hF hS H adj hb h L).hom ≫
      ((adj m).counit.app ((reductionCtfScalar (quotient l E h) Y (hS Y h)).obj L)).hom =
    @inv _ _ _ _ ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
        ((H n).obj L).obj) (hb h L) ≫
      (scalarExtensionFunctor (quotient l E h) Y).map ((adj n).counit.app L).hom := by
  let A := (reductionCtfScalar (quotient l E h) X (hS X h)).obj ((H n).obj L)
  let B := (reductionCtfScalar (quotient l E h) Y (hS Y h)).obj L
  let t : (reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g (hF m)).obj A ⟶ B :=
    ObjectProperty.homMk
      (@inv _ _ _ _ ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
          ((H n).obj L).obj) (hb h L) ≫
        (scalarExtensionFunctor (quotient l E h) Y).map ((adj n).counit.app L).hom)
  have he : ((adj m).homEquiv A B).symm ((adj m).homEquiv A B t) = t :=
    (adj m).homEquiv A B |>.symm_apply_apply t
  rw [Adjunction.homEquiv_counit] at he
  have he' := congrArg (fun a ↦ a.hom) he
  exact he'

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exceptional_counit (K : C l E b q Y) {m n : ℕ} (h : m ≤ n) :
    (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (exceptionalReduction l E b q c hF hS H adj hb K h) ≫
      ((adj m).counit.app (level l E b q Y K m)).hom =
    @inv _ _ _ _ ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
        ((H n).obj (level l E b q Y K n)).obj) (hb h _) ≫
      (scalarExtensionFunctor (quotient l E h) Y).map
        ((adj n).counit.app (level l E b q Y K n)).hom ≫
      reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj := by
  have hn := congrArg (fun a ↦ a.hom) ((adj m).counit.naturality
    (ObjectProperty.homMk
      (X := (reductionCtfScalar (quotient l E h) Y (hS Y h)).obj (level l E b q Y K n))
      (Y := level l E b q Y K m)
      (reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj)))
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.comp_map,
    Functor.id_map] at hn
  change (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
      (((H m).map (ObjectProperty.homMk
        (X := (reductionCtfScalar (quotient l E h) Y (hS Y h)).obj
          (level l E b q Y K n)) (Y := level l E b q Y K m)
        (reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj))).hom) ≫
      ((adj m).counit.app (level l E b q Y K m)).hom = _ at hn
  dsimp only [exceptionalReduction]
  rw [Functor.map_comp, Category.assoc]
  change _ ≫ (_ ≫ _) = _
  erw [hn]
  rw [← Category.assoc, comparison_counit]
  exact Category.assoc _ _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transported_eq (v : ∀ n : ℕ, Evaluation l E b o q c n)
    (G : C l E b q X) (K : C l E b q Y)
    (ε : (F l E b o q c).obj G.obj ⟶ K.obj)
    (ι : ∀ n : ℕ, level l E b q X G n ≅ (H n).obj (level l E b q Y K n))
    (hι : ∀ n : ℕ,
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map (ι n).hom.hom ≫
        ((adj n).counit.app (level l E b q Y K n)).hom = counit l E b o q c v G K ε n)
    {m n : ℕ} (h : m ≤ n)
    (bi : (scalarExtensionFunctor (quotient l E h) Y).obj
        ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj
          (level l E b q X G n).obj) ≅
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).obj
        ((scalarExtensionFunctor (quotient l E h) X).obj (level l E b q X G n).obj))
    (hbi : bi.hom = (reductionDirectImageComparison (quotient l E h) c.i c.g).app
      (level l E b q X G n).obj)
    (hg : (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (reduction l E X (q.abelian X) h (q.scalar X h) G.obj) ≫
      counit l E b o q c v G K ε m =
      bi.inv ≫ (scalarExtensionFunctor (quotient l E h) Y).map
        (counit l E b o q c v G K ε n) ≫
      reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj) :
    transportedReduction l E b q H G K ι h =
      exceptionalReduction l E b q c hF hS H adj hb K h := by
  let M := (reductionCtfScalar (quotient l E h) X (hS X h)).obj
    ((H n).obj (level l E b q Y K n))
  apply congrArg (fun a : M ⟶ (H m).obj (level l E b q Y K m) ↦ a.hom)
  apply (adj m).homEquiv _ _ |>.symm.injective
  apply ObjectProperty.hom_ext
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  change (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
      (transportedReduction l E b q H G K ι h) ≫ _ =
    (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
      (exceptionalReduction l E b q c hF hS H adj hb K h) ≫ _
  rw [exceptional_counit]
  dsimp only [transportedReduction]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  erw [hι m, hg]
  have hn := congrArg
    (fun a ↦ (scalarExtensionFunctor (quotient l E h) Y).map a) (hι n)
  rw [← hn, Functor.map_comp]
  simp only [Category.assoc]
  have : IsIso ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
      (level l E b q X G n).obj) := hbi ▸ bi.isIso_hom
  have hbinv : bi.inv = inv
      ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
        (level l E b q X G n).obj) := by
    apply IsIso.eq_inv_of_hom_inv_id
    exact hbi ▸ bi.hom_inv_id
  rw [hbinv]
  have nat := (reductionDirectImageComparison (quotient l E h) c.i c.g).naturality
    (ι n).inv.hom
  change (scalarExtensionFunctor (quotient l E h) Y).map
      ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map (ι n).inv.hom) ≫
      (reductionDirectImageComparison (quotient l E h) c.i c.g).app
        (level l E b q X G n).obj =
    (reductionDirectImageComparison (quotient l E h) c.i c.g).app
      ((H n).obj (level l E b q Y K n)).obj ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        ((scalarExtensionFunctor (quotient l E h) X).map (ι n).inv.hom) at nat
  have hninv :
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
          ((scalarExtensionFunctor (quotient l E h) X).map (ι n).inv.hom) ≫
        inv ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
          (level l E b q X G n).obj) =
      @inv _ _ _ _ ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
          ((H n).obj (level l E b q Y K n)).obj) (hb h _) ≫
        (scalarExtensionFunctor (quotient l E h) Y).map
          ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map (ι n).inv.hom) := by
    have := hb h (level l E b q Y K n)
    have : IsIso ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
      (level l E b q X G n).obj) := hbi ▸ bi.isIso_hom
    apply (IsIso.eq_inv_comp _).2
    rw [← Category.assoc, ← nat]
    simp
  rw [← Category.assoc, hninv]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [ObjectProperty.isoInv_hom_id_hom]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transported_identity (G : C l E b q X) (K : C l E b q Y)
    (ι : ∀ n : ℕ, level l E b q X G n ≅ (H n).obj (level l E b q Y K n))
    (n : ℕ) : transportedReduction l E b q H G K ι (Nat.le_refl n) =
      (scalarUnit l E b q X n).hom.app ((H n).obj (level l E b q Y K n)).obj := by
  dsimp only [transportedReduction]
  rw [(reduction_coherent l E b q X G.obj).1 n]
  have hn := (scalarUnit l E b q X n).hom.naturality (ι n).inv.hom
  simp only [Functor.id_map] at hn
  erw [← Category.assoc, hn]
  simp only [Category.assoc, ObjectProperty.isoInv_hom_id_hom]
  exact Category.comp_id _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transported_composition (G : C l E b q X) (K : C l E b q Y)
    (ι : ∀ n : ℕ, level l E b q X G n ≅ (H n).obj (level l E b q Y K n))
    {r m n : ℕ} (h : r ≤ m) (a : m ≤ n) :
    (scalarExtensionFunctor (quotient l E h) X).map
        (transportedReduction l E b q H G K ι a) ≫
      transportedReduction l E b q H G K ι h =
    (scalarAssoc l E b q X h a).hom.app ((H n).obj (level l E b q Y K n)).obj ≫
      transportedReduction l E b q H G K ι (h.trans a) := by
  dsimp only [transportedReduction]
  simp only [Functor.map_comp, Category.assoc]
  erw [← Functor.map_comp_assoc _ (ι m).hom.hom (ι m).inv.hom]
  erw [ObjectProperty.isoHom_inv_id_hom, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← Category.assoc _ (reduction l E X (q.abelian X) h (q.scalar X h) G.obj)]
  erw [(reduction_coherent l E b q X G.obj).2 h a]
  simp only [Category.assoc]
  erw [← (scalarAssoc l E b q X h a).hom.naturality_assoc]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Global counit transposition determines actual finite reductions, including
identity and triple reductions. Source: blueprint, gluing proof, Levels final sentence
(blueprint: lem-sp-tower-reduction-transpose).

Proof:
1. Write ell = u varpi^e using det-sp-tower-shriek-levels. The ideal equality gives
A_s = A_(E,e*s); def-weil-l-adic-coefficient-extension makes these rings finite.
The quotient maps are unital and ell^n kills both A_n and A_m for m <= n.
2. Exact evaluation detects vanishing of the cohomology tower below the common
lower bound. Thus G is bounded below. Apply the generic
lem-sp-shriek-normalized-transition-comparison with the stipulated compactification:
r_(FG) = F_m(r_G) b(G_n). The scalar-extension theorem preserves ctf and its Tor
interval without flatness; reduction-direct-image makes the specified b invertible.
3. Naturality of the actual derived reduction at epsilon gives
r_(FG) epsilon_m = T(epsilon_n) r_K. Substitute Step 2 and cancel b to obtain
the global equality stated here. No chartwise equality detection is used.
4. Transport r_G through iota. Counit preservation and naturality of b identify its
finite counit transpose with b(H_n K_n)^(-1) T(counit_n) r_K. The definition of
comparison and counit naturality give exactly the same transpose for
c_(n,m) H_m(r_K). The finite adjunction is injective on this ctf test object,
so these two reductions agree.
5. The strict identity transition transposes to the tensor unitor. For a triple,
use det-sp-coefficient-towers-abelian's composition equation and the normalized
derived tensor associator of det-sp-scalar-extension-functor. Substitute Step 4;
naturality of the associator cancels the intermediate iota and its inverse. This
also proves triple compatibility of the counit equations. No normalization of the
towers, quotient flatness or finite projective dimension was used. -/
theorem tower_reduction_transpose
    (pchar : ℕ) (_hp : 0 < pchar) (_hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    [c.Z.Over (Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (v : ∀ n : ℕ, Evaluation l E b o q c n)
    (G : C l E b q X) (K : C l E b q Y)
    (ε : (F l E b o q c).obj G.obj ⟶ K.obj)
    (_hrep : ∀ (n : ℕ) (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)),
      Function.Bijective (fun a : M ⟶ level l E b q X G n ↦
        (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map a.hom ≫
          counit l E b o q c v G K ε n))
    (ι : ∀ n : ℕ, level l E b q X G n ≅ (H n).obj (level l E b q Y K n))
    (_hι : ∀ n : ℕ,
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map (ι n).hom.hom ≫
        ((adj n).counit.app (level l E b q Y K n)).hom = counit l E b o q c v G K ε n) :
    (∀ {m n : ℕ} (h : m ≤ n),
      spFiniteConstructibleTor X (SpTowerShriek.R l E m)
        ((scalarExtensionFunctor (quotient l E h) X).obj (level l E b q X G n).obj) ∧
      ∃ (bi : (scalarExtensionFunctor (quotient l E h) Y).obj
          ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj
            (level l E b q X G n).obj) ≅
        (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).obj
          ((scalarExtensionFunctor (quotient l E h) X).obj (level l E b q X G n).obj)),
      bi.hom = (reductionDirectImageComparison (quotient l E h) c.i c.g).app
          (level l E b q X G n).obj ∧
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
          (reduction l E X (q.abelian X) h (q.scalar X h) G.obj) ≫
        counit l E b o q c v G K ε m =
      bi.inv ≫ (scalarExtensionFunctor (quotient l E h) Y).map
          (counit l E b o q c v G K ε n) ≫
        reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      IsIso (comparison l E b c hF hS H adj hb h (level l E b q Y K n)) ∧
      transportedReduction l E b q H G K ι h =
        exceptionalReduction l E b q c hF hS H adj hb K h ∧
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
          (exceptionalReduction l E b q c hF hS H adj hb K h) ≫
        ((adj m).counit.app (level l E b q Y K m)).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
          ((H n).obj (level l E b q Y K n)).obj) (hb h _) ≫
        (scalarExtensionFunctor (quotient l E h) Y).map
          ((adj n).counit.app (level l E b q Y K n)).hom ≫
        reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj) ∧
    (∀ n : ℕ, exceptionalReduction l E b q c hF hS H adj hb K (Nat.le_refl n) =
      (scalarUnit l E b q X n).hom.app ((H n).obj (level l E b q Y K n)).obj) ∧
    (∀ {r m n : ℕ} (h : r ≤ m) (a : m ≤ n),
      (scalarExtensionFunctor (quotient l E h) X).map
          (exceptionalReduction l E b q c hF hS H adj hb K a) ≫
        exceptionalReduction l E b q c hF hS H adj hb K h =
      (scalarAssoc l E b q X h a).hom.app ((H n).obj (level l E b q Y K n)).obj ≫
        exceptionalReduction l E b q c hF hS H adj hb K (h.trans a)) ∧
    ReductionCoherent l E b q X G.obj ∧
    ReductionCoherent l E b q Y K.obj ∧
    ReductionCoherent l E b q Y ((F l E b o q c).obj G.obj) ∧
    (∀ n : ℕ, Finite (SpTowerShriek.R l E n) ∧
      spEllIdeal l E ^ (n + 1) =
        Padic.coefficientExtensionIdeal l E (b.ramification * (n + 1))) ∧
    (∀ {m n : ℕ} (_h : m ≤ n),
      (∀ x : SpTowerShriek.R l E n, (l ^ (n + 1)) • x = 0) ∧
      (∀ x : SpTowerShriek.R l E m, (l ^ (n + 1)) • x = 0)) := by
  have htors {m n : ℕ} (h : m ≤ n) :
      ∀ x : SpTowerShriek.R l E m, (l ^ (n + 1)) • x = 0 :=
    coefficient_torsion l E h
  have hB {m n : ℕ} (h : m ≤ n)
      (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)) :
      IsIso ((reductionDirectImageComparison (quotient l E h) c.i c.g).app M.obj) := by
    obtain ⟨a, z, _, hv⟩ := M.property.1
    have hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X (SpTowerShriek.R l E n))) i).obj
          M.obj)} := by
      apply (Set.finite_Icc a z).subset
      intro i hi
      exact ⟨le_of_not_gt (fun h ↦ hi (hv i (Or.inl h))),
        le_of_not_gt (fun h ↦ hi (hv i (Or.inr h)))⟩
    exact (reductionDirectImage_isIso l pchar _hp _hne k f c.i c.g c.comm.symm
      ⟨n + 1, htors (Nat.le_refl n)⟩ ⟨n + 1, htors h⟩ (quotient l E h) M.obj
      hbounded M.property.2.1 M.property.2.2).1
  have hci {m n : ℕ} (h : m ≤ n)
      (L : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n)) :
      IsIso (comparison l E b c hF hS H adj hb h L) := by
    obtain ⟨hFA, hFB, hSX, hSY, GA, GB, aA, aB, RA, RB, hb₀, cc, hcc, _⟩ :=
      reductionExceptional_isIso l pchar _hp _hne k f d c.i c.g c.comm.symm
        ⟨n + 1, htors (Nat.le_refl n)⟩ ⟨n + 1, htors h⟩ (quotient l E h)
    let β : reductionCtfCompactSupport (SpTowerShriek.R l E n) c.i c.g (hF n) ⋙
        reductionCtfScalar (quotient l E h) Y (hS Y h) ≅
      reductionCtfScalar (quotient l E h) X (hS X h) ⋙
        reductionCtfCompactSupport (SpTowerShriek.R l E m) c.i c.g (hF m) := by
      apply NatIso.ofComponents (fun M ↦ ?_) (fun a ↦ ?_)
      · letI := hB h M
        exact (spFiniteConstructibleTor Y (SpTowerShriek.R l E m)).isoMk
          (asIso ((reductionDirectImageComparison (quotient l E h) c.i c.g).app M.obj))
      · apply ObjectProperty.hom_ext
        exact (reductionDirectImageComparison (quotient l E h) c.i c.g).naturality a.hom
    have hβ (M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n)) :
        (β.inv.app M).hom =
          @inv _ _ _ _ ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
            M.obj) (hB h M) := by
      apply IsIso.eq_inv_of_hom_inv_id
      change (β.hom.app M).hom ≫ (β.inv.app M).hom = 𝟙 _
      exact congrArg (fun a ↦ a.hom) (β.hom_inv_id_app M)
    apply transpose_isIso_of_other_adjoints (adj n) aA (adj m) aB
      (reductionCtfScalar (quotient l E h) X (hS X h))
      (reductionCtfScalar (quotient l E h) Y (hS Y h)) β
      (comparison l E b c hF hS H adj hb h) (fun M ↦ cc.app M) ?_ ?_ hcc.2.1 L
    · intro M
      apply ObjectProperty.hom_ext
      simp only [ObjectProperty.FullSubcategory.comp_hom, hβ]
      change (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (comparison l E b c hF hS H adj hb h M).hom ≫ _ =
        inv ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
          ((H n).obj M).obj) ≫ _
      exact comparison_counit l E b c hF hS H adj hb h M
    · intro M
      apply ObjectProperty.hom_ext
      simp only [ObjectProperty.FullSubcategory.comp_hom, hβ]
      change (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (cc.app M).hom ≫ _ =
        inv ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
          (GA.obj M).obj) ≫ _
      exact hcc.1 M
  have hglobal {m n : ℕ} (h : m ≤ n) :
      spFiniteConstructibleTor X (SpTowerShriek.R l E m)
        ((scalarExtensionFunctor (quotient l E h) X).obj (level l E b q X G n).obj) ∧
      ∃ (bi : (scalarExtensionFunctor (quotient l E h) Y).obj
          ((reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj
            (level l E b q X G n).obj) ≅
        (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).obj
          ((scalarExtensionFunctor (quotient l E h) X).obj (level l E b q X G n).obj)),
      bi.hom = (reductionDirectImageComparison (quotient l E h) c.i c.g).app
          (level l E b q X G n).obj ∧
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
          (reduction l E X (q.abelian X) h (q.scalar X h) G.obj) ≫
        counit l E b o q c v G K ε m =
      bi.inv ≫ (scalarExtensionFunctor (quotient l E h) Y).map
          (counit l E b o q c v G K ε n) ≫
        reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj := by
    have := hB h (level l E b q X G n)
    let bi := asIso ((reductionDirectImageComparison (quotient l E h) c.i c.g).app
      (level l E b q X G n).obj)
    refine ⟨hS X h _, bi, rfl, ?_⟩
    have ht := tower_intrinsic_shriek_transition l E b o q pchar _hp _hne k c v G h
    have hn := reduction_naturality l E b q Y h ε
    dsimp only [counit]
    apply bi.eq_inv_comp.mpr
    have he := congrArg (fun a ↦
      (scalarExtensionFunctor (quotient l E h) Y).map
        ((v n).comparison.inv.app G.obj) ≫ a) ht
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app] at he
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at he
    change (reductionDirectImageComparison (quotient l E h) c.i c.g).app
      ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj G.obj) ≫ _ = _
    erw [← Category.assoc, he]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_app_assoc, ← hn]
    simp only [Functor.map_comp, Category.assoc]
  have heq {m n : ℕ} (h : m ≤ n) :
      transportedReduction l E b q H G K ι h =
        exceptionalReduction l E b q c hF hS H adj hb K h := by
    obtain ⟨_, bi, hbi, hg⟩ := hglobal h
    exact transported_eq l E b o q c hF hS H adj hb v G K ε ι _hι h bi hbi hg
  refine ⟨hglobal, ?_, ?_, ?_, reduction_coherent l E b q X G.obj,
    reduction_coherent l E b q Y K.obj,
    reduction_coherent l E b q Y ((F l E b o q c).obj G.obj),
    fun n ↦ ⟨b.finite n, b.ideals n⟩, fun h ↦ ⟨htors (Nat.le_refl _), htors h⟩⟩
  · intro m n h
    exact ⟨hci h _, heq h, exceptional_counit l E b q c hF hS H adj hb K h⟩
  · intro n
    rw [← heq]
    exact transported_identity l E b q H G K ι n
  · intro r m n h a
    rw [← heq a, ← heq h, ← heq (h.trans a)]
    exact transported_composition l E b q H G K ι h a

end AlgebraicGeometry.ProEtale.SpTowerReductionTranspose
