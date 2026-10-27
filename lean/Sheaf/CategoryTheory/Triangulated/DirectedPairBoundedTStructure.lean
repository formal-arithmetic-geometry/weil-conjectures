module

public import WeilConjectures.CategoryTheory.StageSystem.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import WeilConjectures.CategoryTheory.StageSystem.TStructure

/-! # Bounded t-structures and represented truncations on directed pair categories

Source: blueprint `sec-poincare-duality/sk-lem-finite/prop-constructible-truncations`,
proof, common-stage descent sentence; BBD, Definition 1.3.1 and Proposition 1.3.3
(blueprint: lem-pod-directed-pair-bounded-tstructure).

The existing `StageSystem.PairCategory` is the common-stage quotient. Its published
preadditive, shift and triangulated instances give precisely the structures assumed in
the node. No faithfulness or reflection of bounds is required of transition functors.
`truncLT (m + 1)` denotes the upper truncation at degree `m`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w u v

namespace CategoryTheory.StageSystem

open Limits Pretriangulated Triangulated

private lemma comparison_identity
    {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (t : TStructure A) (F : A ⥤ A) (hF : F = 𝟭 A) (m : ℤ)
    (bLE : t.truncLT (m + 1) ⋙ F ≅ F ⋙ t.truncLT (m + 1))
    (bGE : t.truncGE m ⋙ F ≅ F ⋙ t.truncGE m)
    (hLE : ∀ K, bLE.hom.app K ≫ (t.truncLTι (m + 1)).app (F.obj K) =
      F.map ((t.truncLTι (m + 1)).app K))
    (hGE : ∀ K, F.map ((t.truncGEπ m).app K) ≫ bGE.hom.app K =
      (t.truncGEπ m).app (F.obj K)) (K : A) :
    HEq (bLE.hom.app K) (𝟙 ((t.truncLT (m + 1)).obj K)) ∧
      HEq (bGE.hom.app K) (𝟙 ((t.truncGE m).obj K)) := by
  subst F
  constructor
  · apply heq_of_eq
    have : t.IsLE ((t.truncLT (m + 1) ⋙ 𝟭 A).obj K) (m + 1 - 1) :=
      inferInstanceAs (t.IsLE ((t.truncLT (m + 1)).obj K) (m + 1 - 1))
    apply t.to_truncLT_obj_ext
    exact (hLE K).trans (Category.id_comp _).symm
  · apply heq_of_eq
    have : t.IsGE ((𝟭 A ⋙ t.truncGE m).obj K) m :=
      inferInstanceAs (t.IsGE ((t.truncGE m).obj K) m)
    apply t.from_truncGE_obj_ext
    simpa only [Functor.id_obj, Functor.id_map, Category.comp_id] using hGE K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma cancel_mapped_unit
    {A B : Type*} [Category* A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    [Category* B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
    (tA : TStructure A) (tB : TStructure B) (F : A ⥤ B)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tA tB]
    (n : ℤ) (X : A) {Z : B} [tB.IsGE Z n]
    (f g : F.obj ((tA.truncGE n).obj X) ⟶ Z)
    (h : F.map ((tA.truncGEπ n).app X) ≫ f =
      F.map ((tA.truncGEπ n).app X) ≫ g) : f = g := by
  let e : F.obj ((tA.truncGE n).obj X) ≅ (tB.truncGE n).obj (F.obj X) :=
    (F.eTruncGEIso tA tB n).app X
  apply (cancel_epi e.inv).1
  apply tB.from_truncGE_obj_ext
  have he : (tB.truncGEπ n).app (F.obj X) ≫ e.inv =
      F.map ((tA.truncGEπ n).app X) := by
    have hh : F.map ((tA.truncGEπ n).app X) ≫ e.hom =
        (tB.truncGEπ n).app (F.obj X) :=
      F.eTruncGEπ_app_eTruncGEIsoApp_hom tA tB n X
    rw [← hh, Category.assoc, e.hom_inv_id, Category.comp_id]
  simpa only [← Category.assoc, he] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Bounded t-structures and all canonical truncation data descend to the directed pair
category, with the displayed formulas on common-stage representatives.
Source: blueprint `prop-constructible-truncations`, common-stage descent sentence;
BBD, Definition 1.3.1 and Proposition 1.3.3
(blueprint: lem-pod-directed-pair-bounded-tstructure).

Proof:
1. The identity representative at a later stage gives the isomorphism from a pair to
   its transported pair. Common-stage composition proves its coherence with associators
   and expresses every arrow as a stage arrow conjugated by these isomorphisms.
2. Take the isomorphism closures of the stage aisles. The stage shift axioms give the
   shift axioms of these halves, which are strictly full by construction.
3. Conjugate a morphism from the upper half to the strictly higher lower half to one
   common stage. T-exactness puts its endpoints in the orthogonal stage halves, so it
   vanishes. No functor is required to reflect bounds or to be faithful.
4. Apply each exact inclusion to a stage truncation triangle. It gives the triangle
   existence property on every pair. The stage bounds prove boundedness objectwise.
5. Apply `lem-pod-texact-truncation-comparison` to every transition. The canonical-map
   equations give uniqueness; identity, composition and naturality under the associator
   give the stated comparison coherence for both signs.
6. Apply the same comparison lemma to each now t-exact inclusion. Conjugating the
   canonical pair truncation by its inclusion comparison defines the represented functor
   with the specified stage object; cancellation proves both functor laws.
7. Naturality for the transport isomorphisms and composition compatibility of comparisons
   turn the conjugated functor map into the displayed common-stage formula. Because this
   is a map on the quotient, both representative and stage independence follow.
8. The characterization equations for inclusion comparisons identify the canonical maps
   with the included stage counits and units.
9. Exact inclusions send the whole stage truncation triangle to a distinguished triangle.
   Its end bounds characterize the pair truncation triangle; uniqueness fixes the middle
   identity, the two comparison components and therefore also the shifted connecting arrow.
-/
theorem directedPair_bounded_tStructure
    {I : Type w} [PartialOrder I] [IsDirectedOrder I] [Nonempty I]
    {C : I → Type u} [∀ i : I, Category.{v} (C i)]
    [∀ i : I, Preadditive (C i)] [∀ i : I, HasZeroObject (C i)]
    [∀ i : I, HasShift (C i) ℤ]
    [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
    [∀ i : I, Pretriangulated (C i)] [∀ i : I, IsTriangulated (C i)]
    (S : StageSystem C)
    [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated]
    [∀ (i j k : I) (h : i ≤ j) (k' : j ≤ k),
      NatTrans.CommShift (S.assoc h k').hom ℤ]
    (_hidentity : ∀ i : I, S.T (le_refl i) = 𝟭 (C i))
    (_hunit : ∀ (i j : I) (h : i ≤ j) (K : C i),
      HEq ((S.assoc (le_refl i) h).hom.app K) (𝟙 ((S.T h).obj K)) ∧
      HEq ((S.assoc h (le_refl j)).hom.app K) (𝟙 ((S.T h).obj K)))
    (t : ∀ i : I, TStructure (C i)) (_hbounded : ∀ i : I, (t i).bounded = ⊤)
    [∀ (i j : I) (h : i ≤ j), (S.T h).IsTExact (t i) (t j)] :
    ∃ p : TStructure S.PairCategory,
      p.bounded = ⊤ ∧
      (∀ (n : ℤ) (X : S.PairCategory), p.le n X ↔
        ∃ (i : I) (K : C i), (t i).le n K ∧ Nonempty (X ≅ (S.ι i).obj K)) ∧
      (∀ (n : ℤ) (X : S.PairCategory), p.ge n X ↔
        ∃ (i : I) (K : C i), (t i).ge n K ∧ Nonempty (X ≅ (S.ι i).obj K)) ∧
      ∃ (cLE : ∀ {i j : I} (h : i ≤ j) (m : ℤ),
          (t i).truncLT (m + 1) ⋙ S.T h ≅ S.T h ⋙ (t j).truncLT (m + 1))
        (cGE : ∀ {i j : I} (h : i ≤ j) (m : ℤ),
          (t i).truncGE m ⋙ S.T h ≅ S.T h ⋙ (t j).truncGE m),
        (∀ (i j : I) (h : i ≤ j) (m : ℤ) (K : C i),
          (cLE h m).hom.app K ≫ ((t j).truncLTι (m + 1)).app ((S.T h).obj K) =
            (S.T h).map (((t i).truncLTι (m + 1)).app K)) ∧
        (∀ (i j : I) (h : i ≤ j) (m : ℤ) (K : C i),
          (S.T h).map (((t i).truncGEπ m).app K) ≫ (cGE h m).hom.app K =
            ((t j).truncGEπ m).app ((S.T h).obj K)) ∧
        (∀ (i j : I) (h : i ≤ j) (m : ℤ)
          (b : (t i).truncLT (m + 1) ⋙ S.T h ≅ S.T h ⋙ (t j).truncLT (m + 1)),
          (∀ K : C i, b.hom.app K ≫ ((t j).truncLTι (m + 1)).app ((S.T h).obj K) =
            (S.T h).map (((t i).truncLTι (m + 1)).app K)) → b = cLE h m) ∧
        (∀ (i j : I) (h : i ≤ j) (m : ℤ)
          (b : (t i).truncGE m ⋙ S.T h ≅ S.T h ⋙ (t j).truncGE m),
          (∀ K : C i, (S.T h).map (((t i).truncGEπ m).app K) ≫ b.hom.app K =
            ((t j).truncGEπ m).app ((S.T h).obj K)) → b = cGE h m) ∧
        (∀ (i : I) (m : ℤ) (K : C i),
          HEq ((cLE (le_refl i) m).hom.app K)
            (𝟙 (((t i).truncLT (m + 1)).obj K)) ∧
          HEq ((cGE (le_refl i) m).hom.app K) (𝟙 (((t i).truncGE m).obj K))) ∧
        (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (m : ℤ) (K : C i),
          (S.assoc h h').hom.app (((t i).truncLT (m + 1)).obj K) ≫
              (cLE (h.trans h') m).hom.app K =
            (S.T h').map ((cLE h m).hom.app K) ≫
              (cLE h' m).hom.app ((S.T h).obj K) ≫
                ((t k).truncLT (m + 1)).map ((S.assoc h h').hom.app K)) ∧
        (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (m : ℤ) (K : C i),
          (S.assoc h h').hom.app (((t i).truncGE m).obj K) ≫
              (cGE (h.trans h') m).hom.app K =
            (S.T h').map ((cGE h m).hom.app K) ≫
              (cGE h' m).hom.app ((S.T h).obj K) ≫
                ((t k).truncGE m).map ((S.assoc h h').hom.app K)) ∧
        ∃ (QLE QGE : ℤ → S.PairCategory ⥤ S.PairCategory)
          (bLE : ∀ m : ℤ, QLE m ≅ p.truncLT (m + 1))
          (bGE : ∀ m : ℤ, QGE m ≅ p.truncGE m),
          (∀ (m : ℤ) (X : S.PairCategory),
            (QLE m).obj X = ⟨X.stage, ((t X.stage).truncLT (m + 1)).obj X.obj⟩ ∧
            (QGE m).obj X = ⟨X.stage, ((t X.stage).truncGE m).obj X.obj⟩) ∧
          (∀ (m : ℤ) (X Y : S.PairCategory) (k : I)
            (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (f : X.toStage hX ⟶ Y.toStage hY),
            HEq ((QLE m).map (PairCategory.mkHom k hX hY f))
              (PairCategory.mkHom (S := S)
                (X := ⟨X.stage, ((t X.stage).truncLT (m + 1)).obj X.obj⟩)
                (Y := ⟨Y.stage, ((t Y.stage).truncLT (m + 1)).obj Y.obj⟩) k hX hY
                ((cLE hX m).hom.app X.obj ≫ ((t k).truncLT (m + 1)).map f ≫
                  (cLE hY m).inv.app Y.obj)) ∧
            HEq ((QGE m).map (PairCategory.mkHom k hX hY f))
              (PairCategory.mkHom (S := S)
                (X := ⟨X.stage, ((t X.stage).truncGE m).obj X.obj⟩)
                (Y := ⟨Y.stage, ((t Y.stage).truncGE m).obj Y.obj⟩) k hX hY
                ((cGE hX m).hom.app X.obj ≫ ((t k).truncGE m).map f ≫
                  (cGE hY m).inv.app Y.obj))) ∧
          (∀ (m : ℤ) (X : S.PairCategory),
            HEq ((bLE m).hom.app X ≫ (p.truncLTι (m + 1)).app X)
              ((S.ι X.stage).map (((t X.stage).truncLTι (m + 1)).app X.obj)) ∧
            HEq ((p.truncGEπ m).app X ≫ (bGE m).inv.app X)
              ((S.ι X.stage).map (((t X.stage).truncGEπ m).app X.obj))) ∧
          (∀ (i : I) (m : ℤ) (K : C i),
            ∃ e : (p.triangleLTGE (m + 1)).obj ((S.ι i).obj K) ≅
                (S.ι i).mapTriangle.obj (((t i).triangleLTGE (m + 1)).obj K),
              e.hom.hom₂ = 𝟙 _ ∧
              HEq e.hom.hom₁ ((bLE m).inv.app ⟨i, K⟩) ∧
              HEq e.hom.hom₃ ((bGE (m + 1)).inv.app ⟨i, K⟩)) := by
  classical
  have hle {i j : I} (h : i ≤ j) (n : ℤ) (K : C i) (hK : (t i).le n K) :
      (t j).le n ((S.T h).obj K) := by
    have : (t i).IsLE K n := ⟨hK⟩
    exact (Functor.IsTExact.isLE_obj (t i) (t j) (S.T h) K n).le
  have hge {i j : I} (h : i ≤ j) (n : ℤ) (K : C i) (hK : (t i).ge n K) :
      (t j).ge n ((S.T h).obj K) := by
    have : (t i).IsGE K n := ⟨hK⟩
    exact (Functor.IsTExact.isGE_obj (t i) (t j) (S.T h) K n).ge
  let p := S.tStructure t hle hge
  have incl : ∀ i : I, (S.ι i).IsTExact (t i) p := fun i ↦
    { isLE := fun K n hK ↦ ⟨i, le_rfl, hle le_rfl n K hK.le⟩
      isGE := fun K n hK ↦ ⟨i, le_rfl, hge le_rfl n K hK.ge⟩ }
  have := incl
  have pb : p.bounded = ⊤ := by
    ext X
    constructor
    · intro _; trivial
    · intro _
      have hX : (t X.stage).bounded X.obj := by rw [_hbounded]; trivial
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hX
      exact ⟨⟨a, Functor.IsTExact.isGE_obj (t X.stage) p (S.ι X.stage) X.obj a⟩,
        ⟨b, Functor.IsTExact.isLE_obj (t X.stage) p (S.ι X.stage) X.obj b⟩⟩
  refine ⟨p, pb, ?_, ?_, ?_⟩
  · intro n X
    constructor
    · rintro ⟨i, h, hX⟩
      exact ⟨i, X.toStage h, hX, ⟨S.isoToStage X h⟩⟩
    · rintro ⟨i, K, hK, ⟨e⟩⟩
      exact (p.le n).prop_of_iso e.symm ⟨i, le_rfl, hle le_rfl n K hK⟩
  · intro n X
    constructor
    · rintro ⟨i, h, hX⟩
      exact ⟨i, X.toStage h, hX, ⟨S.isoToStage X h⟩⟩
    · rintro ⟨i, K, hK, ⟨e⟩⟩
      exact (p.ge n).prop_of_iso e.symm ⟨i, le_rfl, hge le_rfl n K hK⟩
  · let cLE {i j : I} (h : i ≤ j) (m : ℤ) :
        (t i).truncLT (m + 1) ⋙ S.T h ≅ S.T h ⋙ (t j).truncLT (m + 1) :=
      (S.T h).eTruncLTIso (t i) (t j) (m + 1 : ℤ)
    let cGE {i j : I} (h : i ≤ j) (m : ℤ) :
        (t i).truncGE m ⋙ S.T h ≅ S.T h ⋙ (t j).truncGE m :=
      (S.T h).eTruncGEIso (t i) (t j) m
    have hcLE (i j : I) (h : i ≤ j) (m : ℤ) (K : C i) :
        (cLE h m).hom.app K ≫ ((t j).truncLTι (m + 1)).app ((S.T h).obj K) =
          (S.T h).map (((t i).truncLTι (m + 1)).app K) :=
      ((t i).texact_truncation_comparison.{u, v, u, v, u, v} (t j) (_hbounded i) (_hbounded j)
        (S.T h) m).1 K |>.1
    have hcGE (i j : I) (h : i ≤ j) (m : ℤ) (K : C i) :
        (S.T h).map (((t i).truncGEπ m).app K) ≫ (cGE h m).hom.app K =
          ((t j).truncGEπ m).app ((S.T h).obj K) :=
      ((t i).texact_truncation_comparison.{u, v, u, v, u, v} (t j) (_hbounded i) (_hbounded j)
        (S.T h) m).1 K |>.2
    have cohLE (i j k : I) (h : i ≤ j) (h' : j ≤ k) (m : ℤ) (K : C i) :
        (S.assoc h h').hom.app (((t i).truncLT (m + 1)).obj K) ≫
            (cLE (h.trans h') m).hom.app K =
          (S.T h').map ((cLE h m).hom.app K) ≫
            (cLE h' m).hom.app ((S.T h).obj K) ≫
              ((t k).truncLT (m + 1)).map ((S.assoc h h').hom.app K) := by
      have := Functor.IsTExact.isLE_obj (t i) (t j) (S.T h)
        (((t i).truncLT (m + 1)).obj K) (m + 1 - 1)
      have := Functor.IsTExact.isLE_obj (t j) (t k) (S.T h')
        ((S.T h).obj (((t i).truncLT (m + 1)).obj K)) (m + 1 - 1)
      have : (t k).IsLE ((S.T h ⋙ S.T h').obj
          (((t i).truncLT (m + 1)).obj K)) (m + 1 - 1) := by
        change (t k).IsLE ((S.T h').obj ((S.T h).obj
          (((t i).truncLT (m + 1)).obj K))) (m + 1 - 1)
        assumption
      apply (t k).to_truncLT_obj_ext
      simp only [Category.assoc]
      rw [hcLE, ((t k).truncLTι (m + 1)).naturality]
      rw [reassoc_of% (hcLE j k h' m ((S.T h).obj K)),
        ← Functor.map_comp_assoc, hcLE]
      exact ((S.assoc h h').hom.naturality (((t i).truncLTι (m + 1)).app K)).symm
    have cohGE (i j k : I) (h : i ≤ j) (h' : j ≤ k) (m : ℤ) (K : C i) :
        (S.assoc h h').hom.app (((t i).truncGE m).obj K) ≫
            (cGE (h.trans h') m).hom.app K =
          (S.T h').map ((cGE h m).hom.app K) ≫
            (cGE h' m).hom.app ((S.T h).obj K) ≫
              ((t k).truncGE m).map ((S.assoc h h').hom.app K) := by
      have : (S.T h ⋙ S.T h').IsTExact (t i) (t k) :=
        { isLE := fun X n _ ↦ by
            have := Functor.IsTExact.isLE_obj (t i) (t j) (S.T h) X n
            exact Functor.IsTExact.isLE_obj (t j) (t k) (S.T h') _ n
          isGE := fun X n _ ↦ by
            have := Functor.IsTExact.isGE_obj (t i) (t j) (S.T h) X n
            exact Functor.IsTExact.isGE_obj (t j) (t k) (S.T h') _ n }
      have : (t k).IsGE ((S.T (h.trans h') ⋙ (t k).truncGE m).obj K) m := by
        change (t k).IsGE (((t k).truncGE m).obj ((S.T (h.trans h')).obj K)) m
        infer_instance
      apply cancel_mapped_unit (t i) (t k) (S.T h ⋙ S.T h') m K
      have hn := (S.assoc h h').hom.naturality (((t i).truncGEπ m).app K)
      dsimp only [Functor.comp_map] at hn ⊢
      rw [← Category.assoc, hn, Category.assoc, hcGE]
      symm
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, hcGE,
        Category.assoc, reassoc_of% (hcGE j k h' m ((S.T h).obj K))]
      exact (((t k).truncGEπ m).naturality ((S.assoc h h').hom.app K)).symm
    refine ⟨cLE, cGE, hcLE, hcGE, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j h m b hb
      exact ((t i).texact_truncation_comparison.{u, v, u, v, u, v} (t j) (_hbounded i) (_hbounded j)
        (S.T h) m).2.1 b hb
    · intro i j h m b hb
      exact ((t i).texact_truncation_comparison.{u, v, u, v, u, v} (t j) (_hbounded i) (_hbounded j)
        (S.T h) m).2.2.1 b hb
    · intro i m K
      exact comparison_identity (t i) (S.T (le_refl i)) (_hidentity i) m
        (cLE (le_refl i) m) (cGE (le_refl i) m)
        (hcLE i i (le_refl i) m) (hcGE i i (le_refl i) m) K
    · exact cohLE
    · exact cohGE
    · let FLE (m : ℤ) : S.Morphism S :=
        { Φ := fun i ↦ (t i).truncLT (m + 1)
          β := fun h ↦ cLE h m
          coh := fun h h' K ↦ (cohLE _ _ _ h h' m K).symm }
      let FGE (m : ℤ) : S.Morphism S :=
        { Φ := fun i ↦ (t i).truncGE m
          β := fun h ↦ cGE h m
          coh := fun h h' K ↦ (cohGE _ _ _ h h' m K).symm }
      let QLE (m : ℤ) := (FLE m).functor
      let QGE (m : ℤ) := (FGE m).functor
      let uLE (m : ℤ) : (FLE m).Hom (Morphism.id S) :=
        { τ := fun i ↦ (t i).truncLTι (m + 1)
          comm := fun {i j} h K ↦ by
            dsimp only [FLE]
            erw [Morphism.id_β_hom_app, Category.comp_id]
            exact (hcLE i j h m K).symm }
      let uGE (m : ℤ) : (Morphism.id S).Hom (FGE m) :=
        { τ := fun i ↦ (t i).truncGEπ m
          comm := fun {i j} h K ↦ by
            dsimp only [FGE]
            erw [Morphism.id_β_hom_app, Category.id_comp]
            exact hcGE i j h m K }
      let etaLE (m : ℤ) : QLE m ⟶ 𝟭 _ :=
        Morphism.descNatTrans (uLE m) ≫ Morphism.functorIdIso.hom
      let etaGE (m : ℤ) : 𝟭 _ ⟶ QGE m :=
        Morphism.functorIdIso.inv ≫ Morphism.descNatTrans (uGE m)
      have hetaLE (m : ℤ) (X : S.PairCategory) : (etaLE m).app X =
          (S.ι X.stage).map (((t X.stage).truncLTι (m + 1)).app X.obj) := by
        simp [etaLE, Morphism.descNatTrans_app, uLE]
      have hetaGE (m : ℤ) (X : S.PairCategory) : (etaGE m).app X =
          (S.ι X.stage).map (((t X.stage).truncGEπ m).app X.obj) := by
        simp [etaGE, Morphism.descNatTrans_app, uGE]
      let dLE (m : ℤ) (X : S.PairCategory) : (QLE m).obj X ≅
          (p.truncLT (m + 1)).obj X :=
        ((S.ι X.stage).eTruncLTIso (t X.stage) p (m + 1 : ℤ)).app X.obj
      let dGE (m : ℤ) (X : S.PairCategory) : (QGE m).obj X ≅
          (p.truncGE m).obj X :=
        ((S.ι X.stage).eTruncGEIso (t X.stage) p m).app X.obj
      have hdLE (m : ℤ) (X : S.PairCategory) :
          (dLE m X).hom ≫ (p.truncLTι (m + 1)).app X = (etaLE m).app X := by
        rw [hetaLE]
        exact (S.ι X.stage).eTruncLTIsoApp_hom_eTruncLTι_app (t X.stage) p
          (m + 1 : ℤ) X.obj
      have hdGE (m : ℤ) (X : S.PairCategory) :
          (etaGE m).app X ≫ (dGE m X).hom = (p.truncGEπ m).app X := by
        rw [hetaGE]
        exact (S.ι X.stage).eTruncGEπ_app_eTruncGEIsoApp_hom (t X.stage) p m X.obj
      let bLE (m : ℤ) : QLE m ≅ p.truncLT (m + 1) :=
        NatIso.ofComponents (dLE m) (fun {X Y} f ↦ by
          have : p.IsLE ((QLE m).obj X) (m + 1 - 1) :=
            Functor.IsTExact.isLE_obj (t X.stage) p (S.ι X.stage) _ _
          apply p.to_truncLT_obj_ext
          rw [Category.assoc, hdLE, Category.assoc, (p.truncLTι (m + 1)).naturality,
            ← Category.assoc, hdLE]
          exact (etaLE m).naturality f)
      let bGE (m : ℤ) : QGE m ≅ p.truncGE m :=
        NatIso.ofComponents (dGE m) (fun {X Y} f ↦ by
          have : p.IsGE ((p.truncGE m).obj Y) m := inferInstance
          apply (cancel_epi (dGE m X).inv).1
          apply p.from_truncGE_obj_ext
          have he : (p.truncGEπ m).app X ≫ (dGE m X).inv = (etaGE m).app X := by
            rw [← hdGE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
          rw [← Category.assoc, ← Category.assoc, he,
            ← (etaGE m).naturality, Category.assoc, hdGE]
          simpa only [Iso.inv_hom_id_assoc] using (p.truncGEπ m).naturality f)
      refine ⟨QLE, QGE, bLE, bGE, ?_, ?_, ?_, ?_⟩
      · intro m X; exact ⟨rfl, rfl⟩
      · intro m X Y k hX hY f; exact ⟨HEq.rfl, HEq.rfl⟩
      · intro m X
        constructor
        · exact heq_of_eq ((hdLE m X).trans (hetaLE m X))
        · apply heq_of_eq
          change (p.truncGEπ m).app X ≫ (dGE m X).inv = _
          rw [← hdGE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
          exact hetaGE m X
      · intro i m K
        let T := (S.ι i).mapTriangle.obj (((t i).triangleLTGE (m + 1)).obj K)
        have hT : T ∈ distTriang S.PairCategory :=
          (S.ι i).map_distinguished _ ((t i).triangleLTGE_distinguished (m + 1) K)
        have h₁ : p.IsLE T.obj₁ (m + 1 - 1) :=
          Functor.IsTExact.isLE_obj (t i) p (S.ι i) _ _
        have h₃ : p.IsGE T.obj₃ (m + 1) :=
          Functor.IsTExact.isGE_obj (t i) p (S.ι i) _ _
        obtain ⟨e, he⟩ := p.triangle_iso_exists
          (p.triangleLTGE_distinguished (m + 1) ((S.ι i).obj K)) hT (Iso.refl _)
          (m + 1 - 1) (m + 1) inferInstance inferInstance h₁ h₃
        change e.hom.hom₂ = 𝟙 ((S.ι i).obj K) at he
        refine ⟨e, he, ?_, ?_⟩
        · apply heq_of_eq
          change e.hom.hom₁ = (dLE m ⟨i, K⟩).inv
          apply (cancel_mono (dLE m ⟨i, K⟩).hom).1
          have : p.IsLE (((p.triangleLTGE (m + 1)).obj ((S.ι i).obj K)).obj₁)
              (m + 1 - 1) := inferInstance
          apply p.to_truncLT_obj_ext
          rw [Category.assoc, hdLE, hetaLE]
          have hh := e.hom.comm₁
          change (p.truncLTι (m + 1)).app ((S.ι i).obj K) ≫ e.hom.hom₂ =
            e.hom.hom₁ ≫ (S.ι i).map (((t i).truncLTι (m + 1)).app K) at hh
          erw [he, Category.comp_id] at hh
          erw [Iso.inv_hom_id, Category.id_comp]
          exact hh.symm
        · apply heq_of_eq
          change e.hom.hom₃ = (dGE (m + 1) ⟨i, K⟩).inv
          apply (cancel_mono (dGE (m + 1) ⟨i, K⟩).hom).1
          have : p.IsGE ((p.truncGE (m + 1)).obj ((S.ι i).obj K)) (m + 1) :=
            inferInstance
          apply p.from_truncGE_obj_ext
          have hh := e.hom.comm₂
          change (p.truncGEπ (m + 1)).app ((S.ι i).obj K) ≫ e.hom.hom₃ =
            e.hom.hom₂ ≫ (S.ι i).map (((t i).truncGEπ (m + 1)).app K) at hh
          erw [he, Category.id_comp] at hh
          erw [← Category.assoc, hh, Iso.inv_hom_id, Category.comp_id]
          symm
          exact (hdGE (m + 1) ⟨i, K⟩).symm.trans
            (congrArg (fun f ↦ f ≫ (dGE (m + 1) ⟨i, K⟩).hom)
              (hetaGE (m + 1) ⟨i, K⟩))

end CategoryTheory.StageSystem
