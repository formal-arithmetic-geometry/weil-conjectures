/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Single
import Sheaf.Algebra.Homology.HomComplexProjections
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Short exact Hom sequences for a stupid source tail

Source: Stacks Project, Tag 0A8X, product Hom differential;
Tag 0117, natural long exact cohomology sequence.
(blueprint: lem-pc-stupid-tail-hom-short-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private lemma homMap_zero {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {A A' B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) (𝟙 B) = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 B : B ⟶ B).val = 0
  ext W x
  change ((𝟙 B : B ⟶ B).val.app _).hom ((φ.app W).hom 0) = 0
  rw [map_zero, map_zero]

set_option backward.isDefEq.respectTransparency true in
private lemma homComplex_preservesZero {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    (M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ((homComplexFunctor (R := R)).flip.obj M).PreservesZeroMorphisms := by
  classical
  obtain ⟨π, hlim, _, hmap⟩ :=
    homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R)
  constructor
  intro L L'
  apply HomologicalComplex.hom_ext
  intro n
  apply Fan.IsLimit.hom_ext (Classical.choice (hlim L'.unop M n))
  intro p
  change (((homComplexFunctor (R := R)).map (0 : L ⟶ L')).app M).f n ≫
    π L'.unop M n p (p + n) rfl = _
  have hm := hmap L.unop L'.unop M M (0 : L'.unop ⟶ L.unop) (𝟙 M)
    n p (p + n) rfl
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.zero_f,
    HomologicalComplex.id_f, op_zero,
    homMap_zero, comp_zero, zero_comp] using hm

private lemma homMap_add {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {A A' B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (f g : A' ⟶ A) :
    SheafOfModules.homObjMap (R := R) (f + g) (𝟙 B) =
      SheafOfModules.homObjMap (R := R) f (𝟙 B) + SheafOfModules.homObjMap (R := R) g (𝟙 B) := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map (f.val + g.val) ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 B : B ⟶ B).val = _
  ext W x
  change ((φ.app W).hom) (((f.val.app _).hom) x + ((g.val.app _).hom) x) =
    ((φ.app W).hom) ((f.val.app _).hom x) + ((φ.app W).hom) ((g.val.app _).hom x)
  exact map_add _ _ _

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
-- Elaborating the dependent product lifts and their three splitting identities needs extra steps.
private lemma homComplex_degreewise_split {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    (S : ShortComplex (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ))
    (σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)
    (M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    [((homComplexFunctor (R := R)).flip.obj M).PreservesZeroMorphisms] :
    (S.op.map ((homComplexFunctor (R := R)).flip.obj M)).ShortExact := by
  classical
  let F := homComplexFunctor (R := R)
  let ss : ∀ p, S.X₃.X p ⟶ S.X₂.X p := fun p ↦ (σ p).s
  let rr : ∀ p, S.X₂.X p ⟶ S.X₁.X p := fun p ↦ (σ p).r
  have hss (p) : ss p ≫ S.g.f p = 𝟙 _ := (σ p).s_g
  have hrr (p) : S.f.f p ≫ rr p = 𝟙 _ := (σ p).f_r
  have hid (p) : rr p ≫ S.f.f p + S.g.f p ≫ ss p = 𝟙 _ := (σ p).id
  obtain ⟨π, hlim, _, hmap⟩ :=
    homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R)
  have hm {L L' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
      (f : L' ⟶ L) (n p : ℤ) :
      ((F.map f.op).app M).f n ≫ π L' M n p (p + n) rfl =
        π L M n p (p + n) rfl ≫ SheafOfModules.homObjMap (R := R) (f.f p) (𝟙 _) := by
    simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using
      hmap L L' M M f (𝟙 M) n p (p + n) rfl
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let r : (((F.obj (op S.X₂)).obj M).X n) ⟶ (((F.obj (op S.X₃)).obj M).X n) :=
    Fan.IsLimit.lift (Classical.choice (hlim S.X₃ M n))
      (fun p ↦ π S.X₂ M n p (p + n) rfl ≫ SheafOfModules.homObjMap (R := R) (ss p) (𝟙 _))
  let t : (((F.obj (op S.X₁)).obj M).X n) ⟶ (((F.obj (op S.X₂)).obj M).X n) :=
    Fan.IsLimit.lift (Classical.choice (hlim S.X₂ M n))
      (fun p ↦ π S.X₁ M n p (p + n) rfl ≫ SheafOfModules.homObjMap (R := R) (rr p) (𝟙 _))
  have hr (p : ℤ) : r ≫ π S.X₃ M n p (p + n) rfl =
      π S.X₂ M n p (p + n) rfl ≫ SheafOfModules.homObjMap (R := R) (ss p) (𝟙 _) :=
    Fan.IsLimit.fac _ _ _
  have ht (p : ℤ) : t ≫ π S.X₂ M n p (p + n) rfl =
      π S.X₁ M n p (p + n) rfl ≫ SheafOfModules.homObjMap (R := R) (rr p) (𝟙 _) :=
    Fan.IsLimit.fac _ _ _
  apply ShortComplex.Splitting.shortExact
  refine { r := r, s := t, f_r := ?_, s_g := ?_, id := ?_ }
  · apply Fan.IsLimit.hom_ext (Classical.choice (hlim S.X₃ M n))
    intro p
    change (((F.map S.g.op).app M).f n ≫ r) ≫ π S.X₃ M n p (p + n) rfl =
      𝟙 (((F.obj (op S.X₃)).obj M).X n) ≫ π S.X₃ M n p (p + n) rfl
    rw [Category.assoc, hr, ← Category.assoc, hm, Category.assoc,
      (SheafOfModules.homObjMap_comp_homObjMap (R := R)
        (S.g.f p) (ss p) (𝟙 (M.X (p + n))) (𝟙 _))]
    simp only [Category.id_comp]
    change π S.X₃ M n p (p + n) rfl ≫
      SheafOfModules.homObjMap (R := R) ((ss p) ≫ (S.g.f p)) (𝟙 _) = _
    rw [hss p]
    simp
  · apply Fan.IsLimit.hom_ext (Classical.choice (hlim S.X₁ M n))
    intro p
    change (t ≫ ((F.map S.f.op).app M).f n) ≫ π S.X₁ M n p (p + n) rfl =
      𝟙 (((F.obj (op S.X₁)).obj M).X n) ≫ π S.X₁ M n p (p + n) rfl
    rw [Category.assoc, hm, ← Category.assoc, ht, Category.assoc,
      (SheafOfModules.homObjMap_comp_homObjMap (R := R)
        (rr p) (S.f.f p) (𝟙 (M.X (p + n))) (𝟙 _))]
    simp only [Category.id_comp]
    change π S.X₁ M n p (p + n) rfl ≫
      SheafOfModules.homObjMap (R := R) ((S.f.f p) ≫ (rr p)) (𝟙 _) = _
    rw [hrr p]
    simp
  · apply Fan.IsLimit.hom_ext (Classical.choice (hlim S.X₂ M n))
    intro p
    change (r ≫ ((F.map S.g.op).app M).f n +
      ((F.map S.f.op).app M).f n ≫ t) ≫ π S.X₂ M n p (p + n) rfl =
      𝟙 (((F.obj (op S.X₂)).obj M).X n) ≫ π S.X₂ M n p (p + n) rfl
    rw [Preadditive.add_comp, Category.assoc, hm, ← Category.assoc, hr,
      Category.assoc, (SheafOfModules.homObjMap_comp_homObjMap (R := R)
        (ss p) (S.g.f p) (𝟙 (M.X (p + n))) (𝟙 _)),
      Category.assoc, ht, ← Category.assoc, hm,
      Category.assoc, (SheafOfModules.homObjMap_comp_homObjMap (R := R)
        (S.f.f p) (rr p) (𝟙 (M.X (p + n))) (𝟙 _))]
    simp only [Category.id_comp]
    rw [← Preadditive.comp_add, ← homMap_add]
    have hs : S.g.f p ≫ (ss p) + (rr p) ≫ S.f.f p = 𝟙 _ := by
      rw [add_comm]
      exact hid p
    rw [hs]
    simp

/-- The Hom maps for the bottom source term, the entire source, and its next stupid
tail occur as the three components of a morphism of short exact sequences.
The arrow isomorphisms include the identifications of each Hom complex and its map,
so the statement supplies naturality in the second variable as well as exactness.

Source: Stacks Project, Tag 0A8X, product Hom differential;
Tag 0117, natural long exact cohomology sequence.
(blueprint: lem-pc-stupid-tail-hom-short-exact).

Proof: let T be the stupid tail of P in degrees at least k+1 and let G be P.X k
placed in degree k. Since P vanishes below k, inclusion of T and projection to G
give a degreewise split short exact sequence 0 to T to P to G to 0. Applying
internal Hom into M gives 0 to Hom(G,M) to Hom(P,M) to Hom(T,M) to 0.
Construct the maps by extending a family at k by zero and restricting a family
to degrees at least k+1. The formula d_M h - (-1)^n h d_P proves both are chain
maps: for the extension map, its source-composition term vanishes because the
only possible incoming source differential is from the zero term P.X (k-1);
restriction is compatible because the differential at a source degree p only
uses p and p+1. In each Hom degree, splitting the product index set into the
singleton k, the tail, and the zero terms below k makes this sequence split.
Use the same maps for N. Postcomposition by f commutes with extension and
restriction componentwise, giving a morphism of these short exact sequences.
Take S and T to be these two short exact Hom sequences and φ to have
these three postcomposition maps as its components. The product identifications
with the named Hom complexes give the required arrow isomorphisms.
The product splitting uses no exactness of an infinite product; it is a
splitting of an existing product into two factors, valid for unbounded P, M, N. -/
theorem exists_homComplex_stupid_tail_shortExact
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k : ℤ) (hbelow : ∀ n : ℤ, n < k → IsZero (P.X n))
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) : ∃ S T : ShortComplex (CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      ∃ φ : S ⟶ T, S.ShortExact ∧ T.ShortExact ∧
        Nonempty (Arrow.mk φ.τ₁ ≅ Arrow.mk (((homComplexFunctor (R := R)).obj
          (op ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj
            (P.X k)))).map f)) ∧
        Nonempty (Arrow.mk φ.τ₂ ≅ Arrow.mk
          (((homComplexFunctor (R := R)).obj (op P)).map f)) ∧
        Nonempty (Arrow.mk φ.τ₃ ≅ Arrow.mk (((homComplexFunctor (R := R)).obj
          (op (P.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1))))).map f)) := by
  classical
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let e := ComplexShape.embeddingUpIntGE (k + 1)
  let G := (HomologicalComplex.single A (ComplexShape.up ℤ) k).obj (P.X k)
  let i := P.ιStupidTrunc e
  have hd : ∀ n : ℤ, (ComplexShape.up ℤ).Rel n k → P.d n k ≫ 𝟙 (P.X k) = 0 := by
    intro n hn
    exact (hbelow n (by simp only [ComplexShape.up_Rel] at hn; omega)).eq_of_src _ _
  let q : P ⟶ G := HomologicalComplex.mkHomToSingle (𝟙 (P.X k)) hd
  have hiq : i ≫ q = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    apply IsZero.eq_of_src
    apply P.isZero_stupidTrunc_X e
    intro n
    simp only [e, ComplexShape.embeddingUpIntGE_f]
    omega
  let S₀ := ShortComplex.mk i q hiq
  have σ : ∀ n : ℤ, (S₀.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).Splitting := by
    intro n
    by_cases hn : n = k
    · subst n
      apply ShortComplex.Splitting.ofIsZeroOfIsIso
      · apply P.isZero_stupidTrunc_X e
        intro n
        simp only [e, ComplexShape.embeddingUpIntGE_f]
        omega
      · change IsIso (q.f k)
        dsimp [q]
        rw [HomologicalComplex.mkHomToSingle_f]
        simp only [Category.id_comp]
        infer_instance
    · apply ShortComplex.Splitting.ofIsIsoOfIsZero
      · change IsIso (i.f n)
        by_cases hkn : k + 1 ≤ n
        · obtain ⟨m, hm⟩ := Int.le.dest hkn
          exact P.isIso_ιStupidTrunc_f e (i := m) (by
            simp only [e, ComplexShape.embeddingUpIntGE_f]
            omega)
        · have hP := hbelow n (by omega)
          have hU : IsZero ((P.stupidTrunc e).X n) := by
            apply P.isZero_stupidTrunc_X e
            intro m
            simp only [e, ComplexShape.embeddingUpIntGE_f]
            omega
          exact ⟨⟨0, hU.eq_of_src _ _, hP.eq_of_src _ _⟩⟩
      · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k (P.X k) n hn
  let F := homComplexFunctor (R := R)
  let : (F.flip.obj M).PreservesZeroMorphisms := homComplex_preservesZero M
  let : (F.flip.obj N).PreservesZeroMorphisms := homComplex_preservesZero N
  let S := S₀.op.map (F.flip.obj M)
  let T := S₀.op.map (F.flip.obj N)
  let φ : S ⟶ T := S₀.op.mapNatTrans (F.flip.map f)
  refine ⟨S, T, φ, ?_, ?_, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  · exact homComplex_degreewise_split S₀ σ M
  · exact homComplex_degreewise_split S₀ σ N

end CategoryTheory
