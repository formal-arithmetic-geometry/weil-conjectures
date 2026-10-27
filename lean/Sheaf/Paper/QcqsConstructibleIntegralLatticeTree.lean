/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SixFunctors.SchemeRefinementTree
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import all Sheaf.Paper.FiniteEtaleLocallyFreeModels
import all Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.Paper.CartesianCoefficients

/-!
# Finite open--closed refinement of supplied integral lattice partitions

Source: main-20261015, sk-lem-stratified-lattice, finite refinement before and after
lattice construction; Stacks Project, Topology, Tag 09Y4
(blueprint: lem-sfb-qcqs-constructible-integral-lattice-tree).

The two coefficient cases are stated together. The auxiliary predicates only package
this statement: every lattice scalar map is instantiated by its canonical inclusion.
The moreover clause gives a replacement tree at each old tip, which is precisely a
finite refinement by trees; the existing `SchemeRefinementTree.bind` grafts them.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj ZeroObject IntermediateField

namespace AlgebraicGeometry.ProEtale

/-- All complementary quasi-compact open--closed splits are allowed. This is the existing
recursive scheme refinement tree, specialized without imposing further branch conditions.
Source: Stacks 09Y4 (blueprint: lem-sfb-qcqs-constructible-integral-lattice-tree). -/
abbrev LatticeRefinementTree (V T : Scheme.{u}) (t : T ⟶ V) :=
  Scheme.SchemeRefinementTree V (fun _ _ _ _ _ _ ↦ True) T t

private theorem relax_tree {V T : Scheme.{u}}
    {allowed : ∀ (W : Scheme.{u}), (W ⟶ V) → ∀ (L R : Scheme.{u}),
      (L ⟶ W) → (R ⟶ W) → Prop}
    {t : T ⟶ V} (tree : Scheme.SchemeRefinementTree V allowed T t)
    {P : ∀ (W : Scheme.{u}), (W ⟶ V) → Prop}
    (hP : tree.AllLeaves P) :
    ∃ tree' : LatticeRefinementTree V T t, tree'.AllLeaves P := by
  induction tree with
  | tip t hc hq hi => exact ⟨.tip t hc hq hi, hP⟩
  | node t l r hc hq hi hl hr hlqc hrqc hcover hd ha left right ihl ihr =>
    obtain ⟨left', hleft⟩ := ihl hP.1
    obtain ⟨right', hright⟩ := ihr hP.2
    exact ⟨.node t l r hc hq hi hl hr hlqc hrqc hcover hd trivial left' right',
      hleft, hright⟩

private theorem lattice_refinement {W : Scheme.{u}}
    [CompactSpace W] [QuasiSeparatedSpace W] (S₀ : Scheme.Stratification W) :
    ∃ tree : LatticeRefinementTree W W (𝟙 W),
      tree.AllLeaves (fun T t ↦ Nonempty T →
        ∃ j : Fin S₀.n, ∃ f : T ⟶ S₀.domain j, f ≫ S₀.immersion j = t) := by
  classical
  let m := 1
  let n := fun _ : Fin m ↦ S₀.n
  let S := fun _ : Fin m ↦ S₀.domain
  let s := fun _ : Fin m ↦ S₀.immersion
  have hcover (a : Fin m) : (⋃ j : Fin (n a), Set.range (s a j).base) = Set.univ := by
    simpa only [s, n, S₀.range_immersion] using S₀.iUnion_stratum_eq_univ
  have hcon (a : Fin m) (j : Fin (n a)) :
      Topology.IsConstructible (Set.range (s a j).base) := by
    simpa only [s, S₀.range_immersion] using S₀.isConstructible_stratum j
  have hs (a : Fin m) (j : Fin (n a)) : IsImmersion (s a j) := S₀.isImmersion j
  let (a : Fin m) (j : Fin (n a)) : IsImmersion (s a j) := hs a j
  choose O Q Z o c q z ho hc hq hz hco hoqc hqqc hqr hzr using
    fun (a : Fin m) (j : Fin (n a)) ↦
      Scheme.exists_constructible_cut (s a j) (hcon a j)
  let allowed := fun (T : Scheme.{u}) (t : T ⟶ W) (L R : Scheme.{u})
      (l : L ⟶ T) (r : R ⟶ T) ↦
    ∃ a : Fin m, ∃ j : Fin (n a),
      ((∃ h₁ : L = pullback t (o a j), ∃ h₂ : R = pullback t (z a j),
          l = eqToHom h₁ ≫ pullback.fst t (o a j) ∧
          r = eqToHom h₂ ≫ pullback.fst t (z a j)) ∨
       (∃ f : T ⟶ O a j, f ≫ o a j = t ∧
          ∃ h₁ : L = pullback f (q a j), ∃ h₂ : R = pullback f (c a j),
          l = eqToHom h₁ ≫ pullback.fst f (q a j) ∧
          r = eqToHom h₂ ≫ pullback.fst f (c a j)))
  let resolved := fun (k : (a : Fin m) × Fin (n a)) (T : Scheme.{u}) (t : T ⟶ W) ↦
    Disjoint (Set.range t.base) (Set.range (s k.1 k.2).base) ∨
      ∃ f : T ⟶ S k.1 k.2, f ≫ s k.1 k.2 = t
  have resolved_comp (k : (a : Fin m) × Fin (n a))
      {T R : Scheme.{u}} (t : T ⟶ W) (r : R ⟶ T)
      (ht : resolved k T t) : resolved k R (r ≫ t) := by
    rcases ht with ht | ⟨f, hf⟩
    · left
      apply Set.disjoint_left.mpr
      rintro x ⟨y, rfl⟩ hx
      exact Set.disjoint_left.mp ht ⟨r y, rfl⟩ hx
    · exact Or.inr ⟨r ≫ f, by rw [Category.assoc, hf]⟩
  have step (k : (a : Fin m) × Fin (n a)) (T : Scheme.{u}) (t : T ⟶ W)
      (hcompact : CompactSpace T) (hqs : QuasiSeparatedSpace T) (himm : IsImmersion t) :
      ∃ tree : Scheme.SchemeRefinementTree W allowed T t,
        tree.AllLeaves (fun R r ↦
          (∃ p : R ⟶ T, p ≫ t = r) ∧ resolved k R r) := by
    let := hcompact
    let := hqs
    let := himm
    let a := k.1
    let j := k.2
    have := ho a j
    have := hc a j
    have := hq a j
    have := hz a j
    have := hoqc a j
    have := hqqc a j
    let A := pullback t (o a j)
    let D := pullback t (z a j)
    let p : A ⟶ T := pullback.fst t (o a j)
    let d : D ⟶ T := pullback.fst t (z a j)
    let f : A ⟶ O a j := pullback.snd t (o a j)
    let B := pullback f (q a j)
    let C := pullback f (c a j)
    let b : B ⟶ A := pullback.fst f (q a j)
    let c' : C ⟶ A := pullback.fst f (c a j)
    have : CompactSpace A := inferInstance
    have : CompactSpace D := inferInstance
    have : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated p
    have : QuasiSeparatedSpace D := quasiSeparatedSpace_of_quasiSeparated d
    have : CompactSpace B := inferInstance
    have : CompactSpace C := inferInstance
    have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated b
    have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c'
    have hfc : f ≫ o a j = p ≫ t := (pullback.condition (f := t) (g := o a j)).symm
    have hqr' : Set.range (q a j).base = (Set.range (c a j).base)ᶜ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩ ⟨v, hv⟩
        have hy : o a j (q a j y) ∈ Set.range (q a j ≫ o a j).base := ⟨y, rfl⟩
        rw [hqr a j] at hy
        apply hy.2
        refine ⟨v, ?_⟩
        rw [← hco a j]
        exact congrArg (o a j) hv
      · intro hx
        have hxW : o a j x ∈ Set.range (q a j ≫ o a j).base := by
          rw [hqr a j]
          refine ⟨⟨x, rfl⟩, ?_⟩
          rintro ⟨v, hv⟩
          apply hx
          refine ⟨v, (o a j).isEmbedding.injective ?_⟩
          simpa only [← hco a j, Scheme.Hom.comp_apply] using hv
        obtain ⟨y, hy⟩ := hxW
        exact ⟨y, (o a j).isEmbedding.injective hy⟩
    have houter : Set.range p.base ∪ Set.range d.base = Set.univ ∧
        Disjoint (Set.range p.base) (Set.range d.base) := by
      change Set.range (pullback.fst t (o a j)).base ∪
          Set.range (pullback.fst t (z a j)).base = Set.univ ∧
        Disjoint (Set.range (pullback.fst t (o a j)).base)
          (Set.range (pullback.fst t (z a j)).base)
      simp only [Scheme.Pullback.range_fst, hzr, Set.preimage_compl]
      exact ⟨Set.union_compl_self _, disjoint_compl_right⟩
    have hinner : Set.range b.base ∪ Set.range c'.base = Set.univ ∧
        Disjoint (Set.range b.base) (Set.range c'.base) := by
      change Set.range (pullback.fst f (q a j)).base ∪
          Set.range (pullback.fst f (c a j)).base = Set.univ ∧
        Disjoint (Set.range (pullback.fst f (q a j)).base)
          (Set.range (pullback.fst f (c a j)).base)
      simp only [Scheme.Pullback.range_fst, hqr', Set.preimage_compl]
      exact ⟨Set.compl_union_self _, disjoint_compl_left⟩
    refine ⟨.node t p d inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance houter.1 houter.2
      ⟨a, j, Or.inl ⟨rfl, rfl, by simp [p], by simp [d]⟩⟩
      (.node (p ≫ t) b c' inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance hinner.1 hinner.2
        ⟨a, j, Or.inr ⟨f, hfc, rfl, rfl, by simp [b], by simp [c']⟩⟩
        (.tip _ inferInstance inferInstance inferInstance)
        (.tip _ inferInstance inferInstance inferInstance))
      (.tip _ inferInstance inferInstance inferInstance), ?_⟩
    change ((_ ∧ resolved k B (b ≫ p ≫ t)) ∧
      (_ ∧ resolved k C (c' ≫ p ≫ t))) ∧ (_ ∧ resolved k D (d ≫ t))
    refine ⟨⟨⟨⟨b ≫ p, (Category.assoc ..)⟩, ?_⟩,
      ⟨⟨c' ≫ p, (Category.assoc ..)⟩, ?_⟩⟩, ⟨⟨d, rfl⟩, ?_⟩⟩
    · left
      have hb : b ≫ p ≫ t = pullback.snd f (q a j) ≫ q a j ≫ o a j := by
        change pullback.fst f (q a j) ≫ p ≫ t = _
        rw [← hfc, ← Category.assoc, pullback.condition, Category.assoc]
      apply Set.disjoint_left.mpr
      rintro x ⟨y, rfl⟩ hx
      have hy : (b ≫ p ≫ t) y ∈ Set.range (q a j ≫ o a j).base := by
        rw [hb]
        exact ⟨pullback.snd f (q a j) y, rfl⟩
      rw [hqr a j] at hy
      exact hy.2 hx
    · right
      refine ⟨pullback.snd f (c a j), ?_⟩
      change pullback.snd f (c a j) ≫ s a j = c' ≫ p ≫ t
      rw [← hco a j, ← Category.assoc, ← pullback.condition, Category.assoc, hfc]
    · left
      have hd : Set.range (d ≫ t).base =
          Set.range t.base ∩ (Set.range (o a j).base)ᶜ := by
        change Set.range (pullback.fst t (z a j) ≫ t).base = _
        rw [Scheme.Pullback.range_fst_comp, hzr a j]
      apply Set.disjoint_left.mpr
      intro x hx hxS
      have hxO := (hd ▸ hx).2
      obtain ⟨v, rfl⟩ := hxS
      apply hxO
      refine ⟨c a j v, ?_⟩
      exact congrArg (fun g : S a j ⟶ W ↦ g v) (hco a j)
  have build (K : Finset ((a : Fin m) × Fin (n a))) :
      ∃ tree : Scheme.SchemeRefinementTree W allowed W (𝟙 W),
        tree.AllLeaves (fun T t ↦ ∀ k ∈ K, resolved k T t) := by
    induction K using Finset.induction_on with
    | empty =>
      exact ⟨.tip _ inferInstance inferInstance inferInstance, by simp [
        Scheme.SchemeRefinementTree.AllLeaves]⟩
    | @insert k K hk ih =>
      obtain ⟨tree, htree⟩ := ih
      choose replacement hreplacement using step k
      refine ⟨tree.bind replacement, Scheme.SchemeRefinementTree.allLeaves_bind replacement ?_ tree
        htree⟩
      intro T t hcompact hqs himm hprocessed
      apply Scheme.SchemeRefinementTree.allLeaves_mono _ (replacement T t hcompact hqs himm)
        (hreplacement T t hcompact hqs himm)
      rintro R r ⟨⟨p, hp⟩, hnew⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hnew
      · rw [← hp]
        exact resolved_comp i t p (hprocessed i hi)
  obtain ⟨tree, htree⟩ := build Finset.univ
  have hleaf : tree.AllLeaves (fun T t ↦ Nonempty T →
      ∀ a : Fin m, ∃ j : Fin (n a), ∃ f : T ⟶ S a j, f ≫ s a j = t) := by
    apply Scheme.SchemeRefinementTree.allLeaves_mono _ tree htree
    intro T t ht hT a
    obtain ⟨x⟩ := hT
    have hx : t x ∈ ⋃ j : Fin (n a), Set.range (s a j).base := by
      rw [hcover a]
      exact Set.mem_univ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rcases ht ⟨a, j⟩ (Finset.mem_univ _) with havoid | hfactor
    · exact False.elim (Set.disjoint_left.mp havoid ⟨x, rfl⟩ hj)
    · exact ⟨j, hfactor⟩
  obtain ⟨tree', htree'⟩ := relax_tree tree hleaf
  refine ⟨tree', Scheme.SchemeRefinementTree.allLeaves_mono ?_ tree' htree'⟩
  intro T t ht hT
  exact ht hT 0

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A nonempty leaf has an actual morphism through a witnessing stratum and lisse
restriction. Source: the first assertion of the finite refinement construction
(blueprint: lem-sfb-qcqs-constructible-integral-lattice-tree). -/
def IsConstructibleLatticeLeaf {V : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))
    (S : Scheme.Stratification V) (T : Scheme.{u}) (t : T ⟶ V) : Prop :=
  Nonempty T →
    (∃ a : Fin S.n, ∃ h : T ⟶ S.domain a, h ≫ S.immersion a = t) ∧
      IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ t).obj M)

/-- The conclusion at every new tip of a replacement tree, including the zero model
on an empty tip. The integral model on a nonempty tip is the actual pullback of the
supplied module, not an independently chosen lattice.
Source: finite refinement after lattice construction, Stacks 09Y4 and 03EL
(blueprint: lem-sfb-qcqs-constructible-integral-lattice-tree). -/
def IsPulledIntegralLatticeLeaf (ℓ : ℕ) [Fact ℓ.Prime]
    {I : Type} (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (a : ∀ i : I, Profinite.padicIntegersRingObj.{u} ℓ (F i).1 ⟶ Λ)
    [∀ i : I, IsMonHom (a i)] (i₀ : I)
    {V : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))
    (S₀ : Scheme.Stratification V) {T : Scheme.{u}} (t : T ⟶ V)
    (S : Scheme.Stratification T) (f : Fin S.n → I)
    (B : ∀ s : Fin S.n,
      Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ (F (f s)).1) (S.domain s)))
    (W : Scheme.{u}) (w : W ⟶ T) : Prop :=
  IsConstructibleLatticeLeaf Λ M S₀ W (w ≫ t) ∧
    (Nonempty W → ∃ s : Fin S.n, ∃ h : W ⟶ S.domain s,
      h ≫ S.immersion s = w ∧
      IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ (F (f s)).1)
        ((CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ (F (f s)).1) h).obj
          (B s)) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (a (f s)) W)).obj
          ((CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ (F (f s)).1) h).obj
            (B s)) ≅ (CondensedRing.upperStar Λ (w ≫ t)).obj M)) ∧
    (IsEmpty W →
      IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ (F i₀).1) (X := W) 0 ∧
      Nonempty ((Mod.extendScalars (coefficientMap (a i₀) W)).obj 0 ≅
        (CondensedRing.upperStar Λ (w ≫ t)).obj M))

/-- A prescribed old nonempty leaf admits a replacement tree subordinate to any supplied
constructible partition and its lisse integral models. Empty old leaves are retained.
Source: the moreover clause, finite refinement after lattice construction
(blueprint: lem-sfb-qcqs-constructible-integral-lattice-tree). -/
def IntegralLatticeLeafRefinable (ℓ : ℕ) [Fact ℓ.Prime]
    {I : Type} (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (a : ∀ i : I, Profinite.padicIntegersRingObj.{u} ℓ (F i).1 ⟶ Λ)
    [∀ i : I, IsMonHom (a i)] (i₀ : I)
    {V : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))
    (S₀ : Scheme.Stratification V) (T : Scheme.{u}) (t : T ⟶ V) : Prop :=
  (IsEmpty T →
    IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ (F i₀).1) (X := T) 0 ∧
    Nonempty ((Mod.extendScalars (coefficientMap (a i₀) T)).obj 0 ≅
      (CondensedRing.upperStar Λ t).obj M)) ∧
  (Nonempty T → ∀ (S : Scheme.Stratification T) (f : Fin S.n → I)
    (B : ∀ s : Fin S.n,
      Mod (Sheaf (Scheme.ProEt.topology (S.domain s)) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ (F (f s)).1) (S.domain s))),
    (∀ s : Fin S.n, IsLisseCoefficientModule
      (Profinite.padicIntegersRingObj ℓ (F (f s)).1) (B s)) →
    (∀ s : Fin S.n,
      Nonempty ((Mod.extendScalars (coefficientMap (a (f s)) (S.domain s))).obj (B s) ≅
        (CondensedRing.upperStar Λ (S.immersion s ≫ t)).obj M)) →
    ∃ tree : LatticeRefinementTree T T (𝟙 T),
      Scheme.SchemeRefinementTree.AllLeaves
        (IsPulledIntegralLatticeLeaf Λ ℓ F a i₀ M S₀ t S f B) tree)

/-- Both assertions of the node for one of its two rational coefficient rings. The
second assertion quantifies over every old tree of the required kind, and supplies
finite replacement trees at all its tips. Finite binary trees and complementary
splits already encode disjoint covering of the nonempty leaves and qcqs vertices.
Source: finite refinement before and after the stratified lattice construction
(blueprint: lem-sfb-qcqs-constructible-integral-lattice-tree). -/
def ConstructibleIntegralLatticeTreeAssertion (ℓ : ℕ) [Fact ℓ.Prime]
    {I : Type} (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (a : ∀ i : I, Profinite.padicIntegersRingObj.{u} ℓ (F i).1 ⟶ Λ)
    [∀ i : I, IsMonHom (a i)] (i₀ : I) (V : Scheme.{u}) : Prop :=
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V),
    IsConstantModelConstructible Λ V M →
      (∃ S : Scheme.Stratification V,
        (∀ s : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain s)
          ((CondensedRing.upperStar Λ (S.immersion s)).obj M)) ∧
        ∃ tree : LatticeRefinementTree V V (𝟙 V),
          Scheme.SchemeRefinementTree.AllLeaves (IsConstructibleLatticeLeaf Λ M S) tree) ∧
      (∀ S : Scheme.Stratification V,
        (∀ s : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain s)
          ((CondensedRing.upperStar Λ (S.immersion s)).obj M)) →
        ∀ tree : LatticeRefinementTree V V (𝟙 V),
          Scheme.SchemeRefinementTree.AllLeaves (IsConstructibleLatticeLeaf Λ M S) tree →
          Scheme.SchemeRefinementTree.AllLeaves
            (IntegralLatticeLeafRefinable Λ ℓ F a i₀ M S) tree)

private theorem lattice_lisse_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsLisseCoefficientModule Λ M) : IsLisseCoefficientModule Λ N := by
  exact CondensedRing.locFree_iso e.symm hM

private theorem lattice_lisse_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLisseCoefficientModule Λ M) :
    IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M) := by
  exact CondensedRing.locFree_pullback Λ f M hM

private theorem lattice_lisse_zero (X : Scheme.{u}) :
    IsLisseCoefficientModule Λ (X := X) 0 := by
  let C := X.affineCover.weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage
  refine ⟨C, fun i ↦ ⟨0, ⟨?_⟩⟩⟩
  apply (((CondensedRing.upperStar Λ (C.f i)).map_isZero (isZero_zero _))).iso
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro j
  exact Fin.elim0 j

omit [IsCommMonObj Λ] in
private theorem lattice_module_empty {X : Scheme.{u}} [IsEmpty X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsZero M := by
  have hM : IsZero M.X := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    have : IsEmpty T.left := ⟨fun t ↦ @IsEmpty.false X ‹IsEmpty X› (T.hom t)⟩
    exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X T).isZero
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (Mod.forget (condensedRingObj Λ X)).map_injective
  exact hM.eq_of_src _ _

private theorem lattice_empty_model (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (a : Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ Λ) [IsMonHom a]
    {V W : Scheme.{u}} (w : W ⟶ V) [IsEmpty W]
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) (X := W) 0 ∧
      Nonempty ((Mod.extendScalars (coefficientMap a W)).obj 0 ≅
        (CondensedRing.upperStar Λ w).obj M) := by
  exact ⟨lattice_lisse_zero _ W,
    ⟨((Mod.extendScalars (coefficientMap a W)).map_isZero (isZero_zero _)).iso
      (lattice_module_empty Λ _)⟩⟩

private theorem lattice_leaf_pullback {V T W : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))
    (S₀ : Scheme.Stratification V) (t : T ⟶ V) (w : W ⟶ T)
    (hT : IsConstructibleLatticeLeaf Λ M S₀ T t) :
    IsConstructibleLatticeLeaf Λ M S₀ W (w ≫ t) := by
  intro hW
  have hTN : Nonempty T := hW.map w
  obtain ⟨⟨j, h, hh⟩, hl⟩ := hT hTN
  refine ⟨⟨j, w ≫ h, by rw [Category.assoc, hh]⟩, ?_⟩
  exact lattice_lisse_iso Λ ((CondensedRing.upperStarComp Λ w t).app M).symm
    (lattice_lisse_pullback Λ w hl)

private theorem lattice_assertion
    (hmodels : ∀ (X : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      HasFiniteConstantLocalModel Λ X M → IsLisseCoefficientModule Λ M)
    (ℓ : ℕ) [Fact ℓ.Prime] {I : Type}
    (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (a : ∀ i : I, Profinite.padicIntegersRingObj.{u} ℓ (F i).1 ⟶ Λ)
    [∀ i : I, IsMonHom (a i)] (i₀ : I)
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V] :
    ConstructibleIntegralLatticeTreeAssertion Λ ℓ F a i₀ V := by
  classical
  intro M hM
  have hstrat : IsFiniteConstantStratified Λ V M := by
    simpa only [IsConstantModelConstructible, if_pos
      (show CompactSpace V ∧ QuasiSeparatedSpace V from ⟨inferInstance, inferInstance⟩)] using hM
  constructor
  · obtain ⟨S, hS⟩ := hstrat
    obtain ⟨tree, htree⟩ := lattice_refinement S
    refine ⟨S, hS, tree, Scheme.SchemeRefinementTree.allLeaves_mono ?_ tree htree⟩
    intro T t ht hT
    obtain ⟨j, h, hh⟩ := ht hT
    refine ⟨⟨j, h, hh⟩, ?_⟩
    rw [← hh]
    exact lattice_lisse_iso Λ
      ((CondensedRing.upperStarComp Λ h (S.immersion j)).app M).symm
      (lattice_lisse_pullback Λ h (hmodels _ _ (hS j)))
  · intro S _ tree htree
    suffices h : ∀ (T : Scheme.{u}) (t : T ⟶ V) (tr : LatticeRefinementTree V T t),
        tr.AllLeaves (IsConstructibleLatticeLeaf Λ M S) →
        tr.AllLeaves (IntegralLatticeLeafRefinable Λ ℓ F a i₀ M S) from h _ _ tree htree
    intro T t tr htree
    induction tr with
    | tip t hc hq hi =>
      have : CompactSpace _ := hc
      have : QuasiSeparatedSpace _ := hq
      constructor
      · intro hempty
        have := hempty
        exact lattice_empty_model Λ ℓ (F i₀) (a i₀) t M
      · intro _ S' f B hB he
        obtain ⟨newtree, hnewtree⟩ := lattice_refinement S'
        refine ⟨newtree, Scheme.SchemeRefinementTree.allLeaves_mono ?_ newtree hnewtree⟩
        intro W w hw
        refine ⟨lattice_leaf_pullback Λ M S t w htree, ?_, ?_⟩
        · intro hW
          obtain ⟨j, h, hh⟩ := hw hW
          refine ⟨j, h, hh, lattice_lisse_pullback _ h (hB j), ?_⟩
          obtain ⟨ej⟩ := he j
          refine ⟨((CondensedRing.pullIso (a (f j)) h).app (B j)) ≪≫
            (CondensedRing.upperStar Λ h).mapIso ej ≪≫
            ((CondensedRing.upperStarComp Λ h (S'.immersion j ≫ t)).app M).symm ≪≫ ?_⟩
          exact eqToIso (congrArg (fun g ↦ (CondensedRing.upperStar Λ g).obj M)
            (by rw [← Category.assoc, hh]))
        · intro hempty
          have := hempty
          exact lattice_empty_model Λ ℓ (F i₀) (a i₀) (w ≫ t) M
    | node t l r hc hq hi hl hr hlqc hrqc hcover hd ha left right ihl ihr =>
      exact ⟨ihl htree.1, ihr htree.2⟩

private theorem scalar_ring_monObj
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :
    (scalarSections.{u}).monObjObj (coefficientHeartRingObj R) =
      AddCommGrpCat.ringMonObj (R.obj.obj (Opposite.op (Profinite.of PUnit.{u + 1}))) := by
  rw [scalarSections_monoidal_eq]
  apply MonObj.ext
  let : MonObj (coefficientHeartRingObj R).obj := R.obj.monObjCompForget₂
  exact congr_app (Sheaf.μ_comp_map_mul (coefficientHeartRingObj R))
    (Opposite.op (Profinite.of PUnit.{u + 1}))

set_option backward.isDefEq.respectTransparency false in
private theorem lattice_scalar_free
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (K : Type (u + 1)) [Field K]
    (eK : K ≃+* R.obj.obj (Opposite.op (Profinite.of PUnit.{u + 1})))
    (P : Mod Ab.{u + 1} (scalarRingObj (coefficientHeartRingObj R)))
    (hP : Mod.IsFinitelyPresented (scalarRingObj (coefficientHeartRingObj R)) P) :
    Mod.IsFree (scalarRingObj (coefficientHeartRingObj R)) P := by
  classical
  let A := scalarRingObj (coefficientHeartRingObj R)
  let φ : AddCommGrpCat.of K ⟶ A := eK.toAddEquiv.toAddCommGrpIso.hom
  have : IsIso φ := by dsimp [φ]; infer_instance
  have : IsMonHom φ := by
    change @IsMonHom _ _ _ _ _ _ ((scalarSections.{u}).monObjObj _) _
    rw [scalar_ring_monObj R]
    exact AddCommGrpCat.isMonHom_ofHom_ringHom eK.toRingHom
  let Q := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : Q.IsEquivalence := by dsimp only [Q]; infer_instance
  have : Q.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [Q]
    infer_instance
  let r : (Mod.comap φ).obj (Mod.regular A) ≅ Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  let b : Q.obj (Mod.regular A) ≃ₗ[K] K :=
    ((internalToModule K).mapIso r).toLinearEquiv.trans
      (internalRegularCoordinates K)
  let c (n : ℕ) := finiteFreeEvaluationCoords (Mod.regular A) Q b n
  obtain ⟨n, m, f, ⟨e⟩⟩ := hP
  let eQ : Q.obj P ≅ cokernel (Q.map f) :=
    Q.mapIso e ≪≫ PreservesCokernel.iso Q f
  have : Module.Finite K (Q.obj (Mod.finiteFree A n)) :=
    Module.Finite.of_injective (c n).toLinearMap (c n).injective
  have : Module.Finite K (cokernel (Q.map f) : ModuleCat K) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient (Q.map f)).toLinearEquiv.symm
  have : Module.Finite K (Q.obj P) := Module.Finite.equiv eQ.toLinearEquiv.symm
  let B := Module.finBasis K (Q.obj P)
  refine ⟨Module.finrank K (Q.obj P), ⟨Q.preimageIso ?_⟩⟩
  exact (B.equivFun.trans (c _).symm).toModuleIso

private noncomputable def finite_point_scalars
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ULift.{u + 1} E.1 ≃+*
      (Profinite.continuousMapRingSheaf.{u} E.1).obj.obj
        (Opposite.op (Profinite.of PUnit.{u + 1})) where
  toFun x := ULift.up (ContinuousMap.const _ x.down)
  invFun f := ULift.up (f.down PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro y
    exact congrArg f.down (Subsingleton.elim PUnit.unit y)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private noncomputable def closure_point_scalars (ℓ : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} (PadicAlgCl ℓ) ≃+*
      (Profinite.padicAlgClCondensedRing.{u} ℓ).obj.obj
        (Opposite.op (Profinite.of PUnit.{u + 1})) where
  toFun x := ULift.up ⟨ContinuousMap.const _ x.down,
    ℚ_[ℓ]⟮x.down⟯, IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral x.down),
    fun _ ↦ IntermediateField.mem_adjoin_simple_self _ x.down⟩
  invFun f := ULift.up (f.down.1 PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro y
    exact congrArg f.down.1 (Subsingleton.elim PUnit.unit y)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Constructible rational modules admit finite open--closed lattice refinements.
The first conjunct is the finite field E case; the second is the finite-subextension
algebraic closure case. There is no hypothesis asserting existence of integral lattices.

Source: main-20261015, sk-lem-stratified-lattice, finite refinement before and after
lattice construction; Stacks 09Y4, 03DO, 03EL
(blueprint: lem-sfb-qcqs-constructible-integral-lattice-tree).

Proof plan, following the node:
1. Choose the finite constructibility stratification. Its local models are finite scalar
matrices over the field E or Omega. Gaussian elimination turns each cokernel into a finite
free module, including zero ranks and empty matrices.
2. Apply lem-fix-constructible-open-closed-refinement to the stratification. It gives qcqs
vertices, quasi-compact complementary splits, and actual morphisms through the original
stratum schemes. Pullback composition and lem-weil-pbc-continuous-locally-free-pullback
make the restricted modules lisse.
3. For each old nonempty leaf apply the same refinement theorem to the supplied finite
constructible lattice partition, preserving the supplied scheme structures.
4. Graft these finite trees into the old finite tree (SchemeRefinementTree.bind); retain
empty old tips. Complementarity gives disjoint covering leaves; compositions give the
immersions into V and the original constructibility strata.
5. Pull each given integral module back along the actual factoring morphism. Local finite
freeness is preserved. Apply lem-sfb-internal-extension-inverse-image and the coefficient
identifications of sk-prop-sfb-cartesian-coefficients. Naturality of alpha in the integral
coefficient inclusion identifies the scalar maps; pullback composition then gives the
required scalar-extension isomorphism to M restricted to the new leaf. On empty tips use
the zero A_E-module. The one-tip tree handles empty V.
-/
theorem qcqs_constructible_integral_lattice_tree
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V] :
    ConstructibleIntegralLatticeTreeAssertion (Profinite.continuousMapRingObj E.1) ℓ
      (fun _ : Unit ↦ E) (fun _ ↦ padicIntegersRingObjToContinuousMapRingObj ℓ E) () V ∧
    ConstructibleIntegralLatticeTreeAssertion (Profinite.padicAlgClRingObj ℓ) ℓ
      (fun F : PadicAlgCl.FiniteIntermediateField ℓ ↦ F)
      (fun F ↦ padicIntegersRingObjToContinuousMapRingObj ℓ F ≫
        Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) E V := by
  constructor
  · apply lattice_assertion
    intro X M hM
    exact models_free_cover _ M
      (lattice_scalar_free (Profinite.continuousMapRingSheaf E.1)
        (ULift.{u + 1} E.1) (finite_point_scalars ℓ E)) hM
  · apply lattice_assertion
    intro X M hM
    exact models_free_cover _ M
      (lattice_scalar_free (Profinite.padicAlgClCondensedRing ℓ)
        (ULift.{u + 1} (PadicAlgCl ℓ)) (closure_point_scalars ℓ)) hM

end AlgebraicGeometry.ProEtale
