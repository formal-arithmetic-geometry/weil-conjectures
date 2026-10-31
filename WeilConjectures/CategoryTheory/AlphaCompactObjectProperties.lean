/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The support and closure API for alpha-compact objects

Source: Krause (2001), conditions (G3)--(G4), pages 121--122,
and alpha-localizing closure, page 124.
(blueprint: lem-sfb-alpha-compact-object-api)
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C]

/-- Alpha-compact objects are alpha-small by construction.
Source: Krause (2001), page 122.
(blueprint: lem-sfb-alpha-compact-object-api) -/
theorem IsAlphaCompact.isAlphaSmall {U : C} {α : Cardinal.{v}}
    (hU : IsAlphaCompact U α) : IsAlphaSmall U α := by
  obtain ⟨S, hSU, hsmall, _⟩ := hU
  exact hsmall U hSU

/-- The maximal class itself satisfies (G4), since the witnessing class for the
source object also contains every object in its factorization.
Source: Krause (2001), page 122, maximal-class construction.
(blueprint: lem-sfb-alpha-compact-object-api) -/
theorem IsAlphaCompact.factorizationClass (α : Cardinal.{v}) :
    (alphaCompactObjects C α).IsCoproductFactorizationClass := by
  intro U hU I Y f
  obtain ⟨S, hSU, hsmall, hfactor⟩ := hU
  obtain ⟨Z, hZ, a, g, hg⟩ := hfactor U hSU I Y f
  exact ⟨Z, fun i ↦ ⟨S, hZ i, hsmall, hfactor⟩, a, g, hg⟩

/-- Krause's factorization condition (G4) implies perfectness (G2).
Source: Krause (2001), page 123, first implication of Lemma 4.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: factor a map through a coproduct of objects of S, lift each component by
the given surjectivity, and compose the coproduct of lifts with the factorization. -/
theorem ObjectProperty.IsCoproductFactorizationClass.perfect
    {S : ObjectProperty C} (hS : S.IsCoproductFactorizationClass)
    (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) :
    ∀ U, S U → Function.Surjective (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f) := by
  classical
  intro U hU h
  obtain ⟨Z, hZ, a, g, hg⟩ := hS U hU I Y h
  choose b hb using fun i ↦ hf i (Z i) (hZ i) (a i)
  refine ⟨g ≫ Limits.Sigma.map b, ?_⟩
  change (g ≫ Limits.Sigma.map b) ≫ Limits.Sigma.map f = h
  rw [Category.assoc, Limits.Sigma.map_comp_map]
  simpa only [hb] using hg

/-- Increasing the cardinal only relaxes the bound on support.
Source: Krause (2001), condition (G3).
(blueprint: lem-sfb-alpha-compact-object-api) -/
theorem IsAlphaSmall.of_le {U : C} {α β : Cardinal.{v}}
    (hU : IsAlphaSmall U α) (h : α ≤ β) : IsAlphaSmall U β := by
  intro I Y f
  obtain ⟨J, hJ, g, hg⟩ := hU I Y f
  exact ⟨J, hJ.of_le h, g, hg⟩

/-- Alpha-compactness is monotone in the cardinal.
Source: Krause (2001), page 122, maximal-class construction.
(blueprint: lem-sfb-alpha-compact-object-api) -/
theorem IsAlphaCompact.of_le {U : C} {α β : Cardinal.{v}}
    (hU : IsAlphaCompact U α) (h : α ≤ β) : IsAlphaCompact U β := by
  obtain ⟨S, hSU, hsmall, hfactor⟩ := hU
  exact ⟨S, hSU, fun V hV ↦ (hsmall V hV).of_le h, hfactor⟩

/-- Smallness is invariant under isomorphism, by precomposing a factorization.
Source: Krause (2001), condition (G3).
(blueprint: lem-sfb-alpha-compact-object-api) -/
theorem IsAlphaSmall.of_iso {U V : C} {α : Cardinal.{v}}
    (hU : IsAlphaSmall U α) (e : U ≅ V) : IsAlphaSmall V α := by
  intro I Y f
  obtain ⟨J, hJ, g, hg⟩ := hU I Y (e.hom ≫ f)
  refine ⟨J, hJ, e.inv ≫ g, ?_⟩
  rw [Category.assoc, hg]
  simp

/-- Repletion preserves the smallness and factorization conditions.
Source: Krause (2001), page 122, maximal-class construction.
(blueprint: lem-sfb-alpha-compact-object-api) -/
theorem IsAlphaCompact.of_iso {U V : C} {α : Cardinal.{v}}
    (hU : IsAlphaCompact U α) (e : U ≅ V) : IsAlphaCompact V α := by
  obtain ⟨S, hSU, hsmall, hfactor⟩ := hU
  refine ⟨S.isoClosure, ⟨U, hSU, ⟨e.symm⟩⟩, ?_, ?_⟩
  · rintro X ⟨Y, hY, ⟨eXY⟩⟩
    exact (hsmall Y hY).of_iso eXY.symm
  · rintro X ⟨Z, hZ, ⟨eXZ⟩⟩ I Y f
    obtain ⟨W, hW, a, g, hg⟩ := hfactor Z hZ I Y (eXZ.inv ≫ f)
    refine ⟨W, fun i ↦ S.le_isoClosure _ (hW i), a, eXZ.hom ≫ g, ?_⟩
    rw [Category.assoc, hg]
    simp

instance isAlphaCompact_isClosedUnderIsomorphisms (α : Cardinal.{v}) :
    (alphaCompactObjects C α).IsClosedUnderIsomorphisms where
  of_iso e hU := hU.of_iso e

/-- A coproduct of fewer than alpha alpha-small objects is alpha-small.
Source: Krause (2001), page 124, alpha-localizing closure of alpha-small objects.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: factor each component map through a support of size less than alpha.
Regularity bounds the union of these supports by alpha. Map every component
factorization into that union, then use the coproduct universal property. -/
theorem IsAlphaSmall.coproduct (α : Cardinal.{v}) [Fact α.IsRegular]
    (I : Type v) (U : I → C) (hI : HasCardinalLT I α)
    (hU : ∀ i, IsAlphaSmall (U i) α) : IsAlphaSmall (∐ U) α := by
  classical
  intro J Y f
  choose K hK g hg using fun i ↦ hU i J Y (Sigma.ι U i ≫ f)
  let L : Set J := ⋃ i, K i
  have hL : HasCardinalLT L α := hasCardinalLT_iUnion K hI hK
  let k (i : I) : (∐ fun j : K i ↦ Y j) ⟶ ∐ fun j : L ↦ Y j :=
    Sigma.desc (fun j ↦ Sigma.ι (fun j : L ↦ Y j)
      ⟨j.1, Set.mem_iUnion.mpr ⟨i, j.2⟩⟩)
  refine ⟨L, hL, Sigma.desc (fun i ↦ g i ≫ k i), ?_⟩
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_desc_assoc, Category.assoc]
  have hk : k i ≫ Sigma.desc (fun j : L ↦ Sigma.ι Y j) =
      Sigma.desc (fun j : K i ↦ Sigma.ι Y j) := by
    apply Sigma.hom_ext
    intro j
    simp [k]
  rw [hk, hg]

/-- Coproducts of fewer than alpha alpha-compact objects are alpha-compact.
Source: Krause (2001), page 124, alpha-localizing closure of T^alpha.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: take the replete class of coproducts of fewer than alpha alpha-compact
objects. Its objects are alpha-small by regularity. To factor a map from such
a coproduct, apply (G4) to each of its components. For each target summand take
the coproduct of the resulting component objects, still indexed by fewer than
alpha objects. These objects belong to the witnessing class. The two coproduct
universal properties assemble the factorizations and verify (G4). -/
theorem IsAlphaCompact.coproduct (α : Cardinal.{v}) [Fact α.IsRegular]
    (I : Type v) (U : I → C) (hI : HasCardinalLT I α)
    (hU : ∀ i, IsAlphaCompact (U i) α) : IsAlphaCompact (∐ U) α := by
  classical
  let S : ObjectProperty C := fun X ↦
    ∃ (J : Type v), HasCardinalLT J α ∧
      ∃ Y : J → C, (∀ j, IsAlphaCompact (Y j) α) ∧ Nonempty (X ≅ ∐ Y)
  refine ⟨S, ⟨I, hI, U, hU, ⟨Iso.refl _⟩⟩, ?_, ?_⟩
  · rintro X ⟨J, hJ, Y, hY, ⟨e⟩⟩
    exact (IsAlphaSmall.coproduct α J Y hJ (fun j ↦ (hY j).isAlphaSmall)).of_iso e.symm
  · rintro X ⟨J, hJ, V, hV, ⟨e⟩⟩ K Y f
    choose Z hZ a g hg using fun j ↦ IsAlphaCompact.factorizationClass α (V j)
      (hV j) K Y (Sigma.ι V j ≫ e.inv ≫ f)
    let W : K → C := fun k ↦ ∐ fun j ↦ Z j k
    let b (k : K) : W k ⟶ Y k := Sigma.desc (fun j ↦ a j k)
    let q (j : J) : (∐ Z j) ⟶ ∐ W :=
      Sigma.desc (fun k ↦ Sigma.ι (fun j ↦ Z j k) j ≫ Sigma.ι W k)
    let t : (∐ V) ⟶ ∐ W := Sigma.desc (fun j ↦ g j ≫ q j)
    refine ⟨W, fun k ↦ ⟨J, hJ, (fun j ↦ Z j k), (fun j ↦ hZ j k),
      ⟨Iso.refl _⟩⟩, b, e.hom ≫ t, ?_⟩
    have ht : t ≫ Limits.Sigma.map b = e.inv ≫ f := by
      apply Sigma.hom_ext
      intro j
      rw [Sigma.ι_desc_assoc, Category.assoc]
      have hq : q j ≫ Limits.Sigma.map b = Limits.Sigma.map (a j) := by
        apply Sigma.hom_ext
        intro k
        simp [q, b, Category.assoc]
      rw [hq, hg]
    rw [Category.assoc, ht]
    simp

/-- Alpha-smallness passes to retracts by precomposition with the retraction.
Source: Krause (2001), page 124, alpha-localizing closure of alpha-small objects.
(blueprint: lem-sfb-alpha-compact-object-api) -/
theorem IsAlphaSmall.of_retract {U V : C} {α : Cardinal.{v}}
    (hV : IsAlphaSmall V α) (r : Retract U V) : IsAlphaSmall U α := by
  intro I Y f
  obtain ⟨J, hJ, g, hg⟩ := hV I Y (r.r ≫ f)
  refine ⟨J, hJ, r.i ≫ g, ?_⟩
  rw [Category.assoc, hg]
  simp

/-- Alpha-compactness passes to retracts.
Source: Krause (2001), page 124, alpha-localizing closure of T^alpha.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: take the retract closure of the canonical class. Smallness passes to
retracts. For (G4), precompose with the retraction, factor using the original
canonical class, and postcompose the resulting source map with the inclusion. -/
theorem IsAlphaCompact.of_retract {U V : C} {α : Cardinal.{v}}
    (hV : IsAlphaCompact V α) (r : Retract U V) : IsAlphaCompact U α := by
  let P := alphaCompactObjects C α
  refine ⟨P.retractClosure, ⟨V, hV, ⟨r⟩⟩, ?_, ?_⟩
  · rintro X ⟨Z, hZ, ⟨rXZ⟩⟩
    exact hZ.isAlphaSmall.of_retract rXZ
  · rintro X ⟨Z, hZ, ⟨rXZ⟩⟩ I Y f
    obtain ⟨W, hW, a, g, hg⟩ := IsAlphaCompact.factorizationClass α Z hZ I Y
      (rXZ.r ≫ f)
    refine ⟨W, fun i ↦ P.le_retractClosure _ (hW i), a, rXZ.i ≫ g, ?_⟩
    rw [Category.assoc, hg]
    simp

instance isAlphaCompact_isStableUnderRetracts (α : Cardinal.{v}) :
    (alphaCompactObjects C α).IsStableUnderRetracts where
  of_retract r hV := hV.of_retract r

section Equivalence

variable {D : Type u} [Category.{v} D] [HasCoproducts.{v} D]

private theorem alphaSmall_of_equivalence (e : C ≌ D)
    {U : C} {α : Cardinal.{v}} (hU : IsAlphaSmall U α) :
    IsAlphaSmall (e.functor.obj U) α := by
  classical
  let adj := e.toAdjunction
  intro I Y f
  let s := sigmaComparison e.inverse Y
  obtain ⟨J, hJ, g, hg⟩ := hU I (fun i ↦ e.inverse.obj (Y i))
    (adj.homEquiv U (∐ Y) f ≫ inv s)
  let Z : J → D := fun j ↦ Y j
  let t := sigmaComparison e.inverse Z
  let a : (∐ Z) ⟶ ∐ Y := Sigma.desc (fun j : J ↦ Sigma.ι Y j)
  refine ⟨J, hJ, (adj.homEquiv U (∐ Z)).symm (g ≫ t), ?_⟩
  apply (adj.homEquiv U (∐ Y)).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc]
  have ht : t ≫ e.inverse.map a =
      Sigma.desc (fun j : J ↦ Sigma.ι (fun i ↦ e.inverse.obj (Y i)) j) ≫ s := by
    apply Sigma.hom_ext
    intro j
    simp [t, a, s, Z]
  rw [ht, ← Category.assoc, hg, Category.assoc]
  simp [s]

/-- Equivalences preserve alpha-compactness.
Source: Krause (2001), pages 121--122, conditions (G3)--(G4).
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: pull the canonical class back along the inverse equivalence. Coproduct
comparison isomorphisms transfer the support condition. For (G4), factor the
inverse image of the map, then transport its component objects and morphisms
back by fullness. Naturality of the coproduct comparisons verifies the equation. -/
theorem IsAlphaCompact.of_equivalence (e : C ≌ D)
    {U : C} {α : Cardinal.{v}} (hU : IsAlphaCompact U α) :
    IsAlphaCompact (e.functor.obj U) α := by
  classical
  let S : ObjectProperty D := fun X ↦ IsAlphaCompact (e.inverse.obj X) α
  refine ⟨S, hU.of_iso (e.unitIso.app U), ?_, ?_⟩
  · intro X hX
    exact (alphaSmall_of_equivalence e hX.isAlphaSmall).of_iso (e.counitIso.app X)
  · intro X hX I Y f
    let s := sigmaComparison e.inverse Y
    obtain ⟨Z, hZ, a, g, hg⟩ := IsAlphaCompact.factorizationClass α
      (e.inverse.obj X) hX I (fun i ↦ e.inverse.obj (Y i))
      (e.inverse.map f ≫ inv s)
    let W : I → D := fun i ↦ e.functor.obj (Z i)
    let b (i : I) : W i ⟶ Y i :=
      e.inverse.preimage ((e.unitIso.app (Z i)).inv ≫ a i)
    let t := sigmaComparison e.inverse W
    let q : X ⟶ ∐ W := e.inverse.preimage
      (g ≫ Limits.Sigma.map (fun i ↦ (e.unitIso.app (Z i)).hom) ≫ t)
    refine ⟨W, fun i ↦ (hZ i).of_iso (e.unitIso.app (Z i)), b, q, ?_⟩
    apply e.inverse.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    have ht : t ≫ e.inverse.map (Limits.Sigma.map b) =
        Limits.Sigma.map (fun i ↦ e.inverse.map (b i)) ≫ s := by
      apply Sigma.hom_ext
      intro i
      simp [t, s, ← Functor.map_comp]
    rw [Category.assoc, Category.assoc, ht]
    have hb (i : I) :
        (e.unitIso.app (Z i)).hom ≫ e.inverse.map (b i) = a i := by
      simp [b]
    have hd : Limits.Sigma.map (fun i ↦ (e.unitIso.app (Z i)).hom) ≫
        Limits.Sigma.map (fun i ↦ e.inverse.map (b i)) = Limits.Sigma.map a := by
      rw [Limits.Sigma.map_comp_map]
      simp only [hb]
    rw [← Category.assoc (Limits.Sigma.map (fun i ↦ (e.unitIso.app (Z i)).hom))
      (Limits.Sigma.map (fun i ↦ e.inverse.map (b i))) s, hd,
      ← Category.assoc, hg, Category.assoc]
    simp [s]

end Equivalence

/-- Shifts preserve alpha-compactness, being equivalences preserving coproducts.
Source: Krause (2001), page 124, alpha-localizing closure of T^alpha.
(blueprint: lem-sfb-alpha-compact-object-api) -/
theorem IsAlphaCompact.shift [HasShift C ℤ]
    {U : C} {α : Cardinal.{v}} (hU : IsAlphaCompact U α) (n : ℤ) :
    IsAlphaCompact (U⟦n⟧) α := hU.of_equivalence (shiftEquiv C n)

open scoped ZeroObject in
/-- The zero object is alpha-compact for every regular alpha.
Source: Krause (2001), page 124, alpha-localizing closure of T^alpha.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: the class of zero objects satisfies (G4) using zero component maps.
Every map from a zero object factors through the empty subcoproduct. -/
theorem isAlphaCompact_zero [HasZeroObject C] [HasZeroMorphisms C]
    (α : Cardinal.{v}) [Fact α.IsRegular] : IsAlphaCompact (0 : C) α := by
  let S : ObjectProperty C := fun X ↦ IsZero X
  refine ⟨S, isZero_zero C, ?_, ?_⟩
  · intro X hX I Y f
    let J : Set I := ∅
    have hJ : HasCardinalLT J α := hasCardinalLT_of_finite _ _
      (Cardinal.IsRegular.aleph0_le Fact.out)
    exact ⟨J, hJ, 0, by simpa using hX.eq_of_src 0 f⟩
  · intro X hX I Y f
    exact ⟨fun _ ↦ 0, fun _ ↦ isZero_zero C, fun _ ↦ 0, 0,
      by simpa using hX.eq_of_src 0 f⟩

private theorem subcoproduct_isSplitMono [HasZeroMorphisms C] {I : Type v} (Y : I → C) (J : Set I) :
    IsSplitMono (Sigma.desc (fun j : J ↦ Sigma.ι Y j)) := by
  classical
  refine ⟨⟨Sigma.desc (fun i ↦ if h : i ∈ J then
    Sigma.ι (fun j : J ↦ Y j) ⟨i, h⟩ else 0), ?_⟩⟩
  apply Sigma.hom_ext
  intro j
  simp

section Triangle

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

open Pretriangulated

/-- Alpha-small objects are closed under extensions.
Source: Krause (2001), page 124, alpha-localizing closure of alpha-small objects.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: restrict a map from the middle vertex to the first vertex and factor it
through a small support J. The subcoproduct inclusion is split monic, so the
obstruction to extending that factorization vanishes. Triangle exactness lifts
it to a map from the middle vertex to the J-subcoproduct. The difference from
the original map factors through the third vertex, and hence through another
small support K. The union J union K is still small and contains both maps. -/
theorem IsAlphaSmall.extension (α : Cardinal.{v}) [Fact α.IsRegular]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsAlphaSmall T.obj₁ α) (h₃ : IsAlphaSmall T.obj₃ α) :
    IsAlphaSmall T.obj₂ α := by
  classical
  intro I Y f
  obtain ⟨J, hJ, a, ha⟩ := h₁ I Y (T.mor₁ ≫ f)
  let j : (∐ fun x : J ↦ Y x) ⟶ ∐ Y := Sigma.desc (fun x : J ↦ Sigma.ι Y x)
  have : IsSplitMono j := subcoproduct_isSplitMono Y J
  have hz : T.invRotate.mor₁ ≫ a = 0 := by
    apply (cancel_mono j).mp
    rw [Category.assoc, ha, ← Category.assoc]
    have hz := comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hT)
    change T.invRotate.mor₁ ≫ T.mor₁ = 0 at hz
    simp only [hz, zero_comp]
  obtain ⟨g, hg⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang _ hT) a hz
  change T.obj₂ ⟶ ∐ fun x : J ↦ Y x at g
  change a = T.mor₁ ≫ g at hg
  have hd : T.mor₁ ≫ (f - g ≫ j) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, ← hg, ha, sub_self]
  obtain ⟨b, hb⟩ := T.yoneda_exact₂ hT _ hd
  obtain ⟨K, hK, c, hc⟩ := h₃ I Y b
  let L : Set I := J ∪ K
  have hL : HasCardinalLT L α := hasCardinalLT_union
    (Cardinal.IsRegular.aleph0_le Fact.out) hJ hK
  let l : (∐ fun x : L ↦ Y x) ⟶ ∐ Y := Sigma.desc (fun x : L ↦ Sigma.ι Y x)
  let jL : (∐ fun x : J ↦ Y x) ⟶ ∐ fun x : L ↦ Y x :=
    Sigma.desc (fun x : J ↦ Sigma.ι (fun x : L ↦ Y x) ⟨x.1, Or.inl x.2⟩)
  let kL : (∐ fun x : K ↦ Y x) ⟶ ∐ fun x : L ↦ Y x :=
    Sigma.desc (fun x : K ↦ Sigma.ι (fun x : L ↦ Y x) ⟨x.1, Or.inr x.2⟩)
  have hjL : jL ≫ l = j := by
    apply Sigma.hom_ext
    intro x
    simp [jL, l, j]
  have hkL : kL ≫ l = Sigma.desc (fun x : K ↦ Sigma.ι Y x) := by
    apply Sigma.hom_ext
    intro x
    simp [kL, l]
  refine ⟨L, hL, g ≫ jL + T.mor₂ ≫ c ≫ kL, ?_⟩
  change (g ≫ jL + T.mor₂ ≫ c ≫ kL) ≫ l = f
  rw [Preadditive.add_comp, Category.assoc, hjL, Category.assoc,
    Category.assoc, hkL, hc, ← hb]
  simpa only [add_sub_assoc] using add_sub_cancel_left (g ≫ j) f

end Triangle

/-- Bounded coproducts of an essentially small class form an essentially small class.
Source: Krause (2001), Lemma 5, smallness of the alpha-localizing closure.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: embed every indexing set of cardinality less than alpha into a fixed set
of cardinality alpha. Reindex its coproduct by the image. The resulting shapes
are indexed by the v-small powerset of this fixed set; Mathlib's smallness of
colimits closure bounds all of the coproducts at once. -/
theorem ObjectProperty.EssentiallySmall.bounded_coproducts
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} P]
    (α : Cardinal.{v}) :
    ObjectProperty.EssentiallySmall.{v}
      (fun X ↦ ∃ (I : Type v) (Y : I → C), HasCardinalLT I α ∧
        (∀ i, P (Y i)) ∧ Nonempty (X ≅ ∐ Y)) := by
  classical
  let E := α.ord.ToType
  let Q := P.colimitsClosure (fun J : Set E ↦ Discrete J)
  have hQ : ObjectProperty.EssentiallySmall.{v} Q := inferInstance
  apply ObjectProperty.EssentiallySmall.of_le (Q := Q)
  rintro X ⟨I, Y, hI, hY, ⟨e⟩⟩
  have hIE : Cardinal.mk I ≤ Cardinal.mk E := by
    simpa [E] using (hasCardinalLT_iff_cardinal_mk_lt I α).mp hI |>.le
  obtain ⟨f⟩ := (Cardinal.le_def I E).mp hIE
  let J : Set E := Set.range f
  let ε : I ≃ J := Equiv.ofInjective f f.injective
  let Z : J → C := Y ∘ ε.symm
  have hZ : Q (∐ Z) := by
    apply Q.prop_of_isColimit (coproductIsCoproduct Z)
    intro j
    exact P.le_colimitsClosure _ _ (hY (ε.symm j.as))
  have er : ∐ Y ≅ ∐ Z :=
    (Sigma.mapIso (fun i ↦ eqToIso (by simp [Z]))).symm ≪≫ Sigma.reindex ε Z
  exact Q.prop_of_iso (e ≪≫ er).symm hZ

omit [HasCoproducts.{v} C] in
/-- Extensions of two essentially small classes form an essentially small class.
Source: Krause (2001), Lemma 5, smallness of the alpha-localizing closure.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: choose small representative sets for both outer vertices. The connecting
maps between their representatives form a small set by local smallness. Choose
a distinguished triangle for each such map. The triangle isomorphism axiom
identifies every extension with the chosen middle vertex for its transported
connecting map. These middle vertices therefore form a small representative set. -/
theorem ObjectProperty.EssentiallySmall.extensionProduct
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} P]
    [ObjectProperty.EssentiallySmall.{v} Q] :
    ObjectProperty.EssentiallySmall.{v} (P.extensionProduct Q) := by
  classical
  obtain ⟨P₀, hP₀, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  obtain ⟨Q₀, hQ₀, _, hQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let R := (p : Subtype P₀) × (q : Subtype Q₀) × (q.val ⟶ p.val⟦(1 : ℤ)⟧)
  have hR : Small.{v} R := inferInstance
  have ht (r : R) := Pretriangulated.distinguished_cocone_triangle₂ r.2.2
  choose M f g hT using ht
  let E : ObjectProperty C := fun X ↦ ∃ r : R, M r = X
  have hE : ObjectProperty.Small.{v} E :=
    _root_.small_of_surjective (f := fun r : R ↦ ⟨M r, ⟨r, rfl⟩⟩)
      (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩)
  refine ⟨E, hE, ?_⟩
  rintro X ⟨Y, Z, a, b, c, h, hY, hZ⟩
  obtain ⟨Y₀, hY₀, ⟨eY⟩⟩ := hP Y hY
  obtain ⟨Z₀, hZ₀, ⟨eZ⟩⟩ := hQ Z hZ
  let r : R := ⟨⟨Y₀, hY₀⟩, ⟨Z₀, hZ₀⟩,
    eZ.inv ≫ c ≫ (shiftFunctor C 1).map eY.hom⟩
  let e := Pretriangulated.isoTriangleOfIso₁₃ (Pretriangulated.Triangle.mk a b c)
    (Pretriangulated.Triangle.mk (f r) (g r) r.2.2) h (hT r) eY eZ (by
      dsimp [r]
      simp)
  exact ⟨M r, ⟨r, rfl⟩, ⟨Pretriangulated.Triangle.π₂.mapIso e⟩⟩

/-- A shift-closed localizing generating class detects zero objects.
Source: Krause (2001), condition (G1) and Lemma 5.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: the double orthogonal of G is triangulated and closed under coproducts,
and contains G. Generation makes it all of C. If Y is right orthogonal to G,
its membership in the double orthogonal forces its identity to vanish. -/
theorem ObjectProperty.isZero_of_localizing_generators
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G : ObjectProperty C) [G.IsStableUnderShift ℤ]
    (hGgen : ∀ (S : ObjectProperty C) [S.IsClosedUnderIsomorphisms] [S.IsTriangulated],
      (∀ (I : Type v) (Y : I → C), (∀ i, S (Y i)) → S (∐ Y)) →
      G ≤ S → ∀ X, S X)
    (Y : C) (hY : ∀ X, G X → ∀ f : X ⟶ Y, f = 0) : IsZero Y := by
  let S := G.rightOrthogonal.leftOrthogonal
  have hsum (I : Type v) (X : I → C) (hX : ∀ i, S (X i)) : S (∐ X) := by
    intro Z f hZ
    apply Sigma.hom_ext
    intro i
    simpa using hX i (Sigma.ι X i ≫ f) hZ
  have hGS : G ≤ S := fun X hX Z f hZ ↦ hZ f hX
  have hSY := hGgen S hsum hGS Y
  exact (Limits.IsZero.iff_id_eq_zero Y).mpr (hSY (𝟙 Y) (fun X f hX ↦ hY X hX f))

/-- Perfectness implies (G4) for a small class of alpha-small objects closed
under coproducts of fewer than alpha summands.
Source: Krause (2001), Lemma 4, page 123.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: for each target summand take the coproduct of all maps from representatives
of S into it. Each such evaluation map is surjective on Hom from S. Perfectness
lifts a map into the coproduct through their coproduct. Flatten that coproduct,
apply alpha-smallness, and group its small support by the original target index.
Each grouped support is smaller than alpha, so its coproduct belongs to S.
The component evaluations and the grouped factorization give (G4). -/
theorem ObjectProperty.factorizationClass_of_perfect
    (S : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} S]
    (α : Cardinal.{v})
    (hsmall : ∀ U, S U → IsAlphaSmall U α)
    (hsum : ∀ (I : Type v) (X : I → C), HasCardinalLT I α →
      (∀ i, S (X i)) → S (∐ X))
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
      ∀ U, S U → Function.Surjective
        (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) :
    S.IsCoproductFactorizationClass := by
  classical
  obtain ⟨S₀, hS₀, hS₀S, hSS₀⟩ := ObjectProperty.EssentiallySmall.exists_small_le S
  let R := Shrink.{v} (Subtype S₀)
  let r : R → Subtype S₀ := (equivShrink.{v} (Subtype S₀)).symm
  intro U hU I Y f
  let K (i : I) := (x : R) × ((r x).val ⟶ Y i)
  let X (i : I) := ∐ fun k : K i ↦ (r k.1).val
  let e (i : I) : X i ⟶ Y i := Sigma.desc (fun k : K i ↦ k.2)
  have he : ∀ i V, S V → Function.Surjective (fun g : V ⟶ X i ↦ g ≫ e i) := by
    intro i V hV a
    obtain ⟨V₀, hV₀, ⟨ev⟩⟩ := hSS₀ V hV
    let x : R := equivShrink.{v} (Subtype S₀) ⟨V₀, hV₀⟩
    have hx : r x = ⟨V₀, hV₀⟩ := Equiv.symm_apply_apply _ _
    let ev' : V ≅ (r x).val := ev ≪≫ eqToIso (by rw [hx])
    refine ⟨ev'.hom ≫ Sigma.ι (fun k : K i ↦ (r k.1).val)
      ⟨x, ev'.inv ≫ a⟩, ?_⟩
    dsimp [e]
    simp
  obtain ⟨q, hq⟩ := hperfect I X Y e he U hU f
  let M := (i : I) × K i
  let V (m : M) := (r m.2.1).val
  let t : (∐ V) ≅ ∐ X := (sigmaSigmaIso K (fun i (k : K i) ↦ (r k.1).val)).symm
  obtain ⟨L, hL, a, ha⟩ := hsmall U hU M V (q ≫ t.inv)
  let N (i : I) := {k : K i // (⟨i, k⟩ : M) ∈ L}
  have hN (i : I) : HasCardinalLT (N i) α :=
    hL.of_injective (f := fun k : N i ↦ (⟨⟨i, k.val⟩, k.property⟩ : L)) (by
      intro k l h
      apply Subtype.ext
      exact (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2.eq)
  let Z (i : I) := ∐ fun k : N i ↦ (r k.val.1).val
  have hZ (i : I) : S (Z i) :=
    hsum (N i) (fun k ↦ (r k.val.1).val) (hN i) (fun k ↦ hS₀S _ (r k.val.1).property)
  let b (i : I) : Z i ⟶ Y i := Sigma.desc (fun k : N i ↦ k.val.2)
  let d : (∐ fun l : L ↦ V l.val) ⟶ ∐ Z := Sigma.desc (fun l : L ↦
    Sigma.ι (fun k : N l.val.1 ↦ (r k.val.1).val) ⟨l.val.2, l.property⟩ ≫
      Sigma.ι Z l.val.1)
  refine ⟨Z, hZ, b, a ≫ d, ?_⟩
  have hd : d ≫ Limits.Sigma.map b =
      Sigma.desc (fun l : L ↦ Sigma.ι V l.val) ≫ t.hom ≫ Limits.Sigma.map e := by
    apply Sigma.hom_ext
    intro l
    simp [d, b, t, V, X, e, M, Category.assoc]
  change (a ≫ d) ≫ Limits.Sigma.map b = f
  rw [Category.assoc, hd, ← Category.assoc, ← Category.assoc, ha]
  simpa using hq

/-- A class of coproducts of perfect objects is perfect, provided it contains
the original perfect class.
Source: Krause (2001), Lemma 5, preservation of (G2) under alpha-coproduct closure.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: componentwise surjectivity on the larger class restricts to the original
class. Its perfectness lifts each summand of the source object into the target
coproduct. Assemble these lifts by the source coproduct universal property and
transport along its given isomorphism. -/
theorem ObjectProperty.perfect_of_coproduct_representatives
    (S T : ObjectProperty C) (hST : S ≤ T)
    (hrep : ∀ U, T U → ∃ (J : Type v) (Z : J → C),
      (∀ j, S (Z j)) ∧ Nonempty (U ≅ ∐ Z))
    (hperfect : ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i U, S U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
      ∀ U, S U → Function.Surjective
        (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f)) :
    ∀ (I : Type v) (X Y : I → C) (f : ∀ i, X i ⟶ Y i),
      (∀ i U, T U → Function.Surjective (fun g : U ⟶ X i ↦ g ≫ f i)) →
      ∀ U, T U → Function.Surjective
        (fun g : U ⟶ ∐ X ↦ g ≫ Limits.Sigma.map f) := by
  classical
  intro I X Y f hf U hU a
  obtain ⟨J, Z, hZ, ⟨e⟩⟩ := hrep U hU
  have hp := hperfect I X Y f (fun i V hV ↦ hf i V (hST _ hV))
  choose b hb using fun j ↦ hp (Z j) (hZ j) (Sigma.ι Z j ≫ e.inv ≫ a)
  refine ⟨e.hom ≫ Sigma.desc b, ?_⟩
  change (e.hom ≫ Sigma.desc b) ≫ Limits.Sigma.map f = a
  have h : Sigma.desc b ≫ Limits.Sigma.map f = e.inv ≫ a := by
    apply Sigma.hom_ext
    intro j
    simpa using hb j
  rw [Category.assoc, h]
  simp

omit [HasCoproducts.{v} C] in
/-- The shift closure of an essentially small class is essentially small.
Source: Krause (2001), Lemma 5, construction of the small alpha-localizing hull.
(blueprint: lem-sfb-alpha-compact-object-api)

Proof: shift every member of a small representative set by every integer. These
objects form a small representative set for the shift closure. -/
theorem ObjectProperty.EssentiallySmall.shiftClosure [HasShift C ℤ]
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{v} P] :
    ObjectProperty.EssentiallySmall.{v} (P.shiftClosure ℤ) := by
  classical
  obtain ⟨Q, hQ, _, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  let R : ObjectProperty C := ObjectProperty.ofObj
    (fun x : ℤ × Subtype Q ↦ x.2.val⟦x.1⟧)
  have hR : ObjectProperty.Small.{v} R := inferInstance
  apply ObjectProperty.EssentiallySmall.of_le (Q := R.isoClosure)
  rintro X ⟨Y, n, e, hY⟩
  obtain ⟨Z, hZ, ⟨eYZ⟩⟩ := hPQ Y hY
  exact ⟨Z⟦n⟧, ObjectProperty.ofObj_apply
    (fun x : ℤ × Subtype Q ↦ x.2.val⟦x.1⟧) (n, ⟨Z, hZ⟩),
    ⟨e ≪≫ (shiftFunctor C n).mapIso eYZ⟩⟩

end CategoryTheory
