module
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Topology.NoetherianSpace
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Finite-cover locality of bounded constructibility and a fixed Tor interval

Source: literature/stacks-project/etale-cohomology.tex, Tag 095F,
label `lemma-constructible-local` (blueprint: lem-sf-finite-cover-ctf-locality).
-/

@[expose] public section
set_option autoImplicit false
universe t

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem cover_isZero
    (X : Scheme.{t}) (hX : TopologicalSpace.NoetherianSpace X)
    (A : Type t) [CommRing A] [Finite A]
    (r : ℕ) (U : Fin r → Scheme.{t}) (j : ∀ i, U i ⟶ X)
    (hj : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ x : X, ∃ i : Fin r, ∃ y : U i, (j i).base y = x)
    (M : proEtaleRingModules X (proEtaleConstantRing X A))
    (hM : ∀ i, IsZero ((proEtaleConstantRingPullback A (j i)).obj M)) :
    IsZero M := by
  have := hX
  have : ∀ i, IsOpenImmersion (j i) := hj
  have : ∀ i, TopologicalSpace.NoetherianSpace (U i) := fun i ↦
    (j i).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : ∀ i, QuasiCompact (j i) := fun i ↦
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let E := proEtaleModuleRestriction X A
  have : E.IsEquivalence := proEtaleModuleRestriction_isEquivalence X A
  apply IsZero.of_full_of_faithful_of_isZero E M
  apply (IsZero.iff_id_eq_zero _).mpr
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero
    (ULift.{t + 1, t} A) j hcover
  intro i
  obtain ⟨e⟩ := proEtaleModuleRestriction_pullback (j i) A M
  have : (proEtaleModuleRestriction (U i) A).IsEquivalence :=
    proEtaleModuleRestriction_isEquivalence (U i) A
  have hz := ((proEtaleModuleRestriction (U i) A).map_isZero (hM i)).of_iso e.symm
  exact hz.eq_of_src _ _

private theorem cover_stratification
    (X : Scheme.{t}) (hX : TopologicalSpace.NoetherianSpace X)
    (n : ℕ) (U : Fin n → Scheme.{t}) (j : ∀ a, U a ⟶ X)
    (hj : ∀ a, IsOpenImmersion (j a))
    (hcover : ∀ x : X, ∃ a, ∃ y : U a, (j a).base y = x)
    (T : ∀ a, Stratification (U a)) :
    ∃ S : Stratification X, ∀ i, ∃ (a : Fin n) (b : Fin (T a).n)
      (q : S.domain i ⟶ (T a).domain b),
      q ≫ ((T a).immersion b ≫ j a) = S.immersion i := by
  classical
  have := hX
  have : ∀ a, IsOpenImmersion (j a) := hj
  let V (a : Fin n) : Set X := ⋃ b ∈ {b : Fin n | b < a}, Set.range (j b)
  have hVo (a : Fin n) : IsOpen (V a) :=
    isOpen_iUnion fun b ↦ isOpen_iUnion fun _ ↦ (j b).isOpenEmbedding.isOpen_range
  let I (a : Fin n) := IdealSheafData.vanishingIdeal (⟨(V a)ᶜ, (hVo a).isClosed_compl⟩)
  let c (a : Fin n) := (I a).subschemeι
  have hcr (a : Fin n) : Set.range (c a) = (V a)ᶜ := by
    simp [c, I, IdealSheafData.range_subschemeι]
  let Idx := (a : Fin n) × Fin (T a).n
  let e : Fin (Fintype.card Idx) ≃ Idx := (Fintype.equivFin Idx).symm
  let g (k : Idx) := (T k.1).immersion k.2 ≫ j k.1
  have hg (k : Idx) : IsImmersion (g k) := by
    have := (T k.1).isImmersion k.2
    dsimp [g]
    infer_instance
  let f (k : Idx) := pullback.fst (g k) (c k.1) ≫ g k
  have hf (k : Idx) : IsImmersion (f k) := by
    have := hg k
    dsimp [f, c]
    infer_instance
  have hgr (k : Idx) : Set.range (g k) = (j k.1) '' (T k.1).stratum k.2 := by
    rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, (T k.1).range_immersion]
  have hfr (k : Idx) : Set.range (f k) = Set.range (g k) ∩ (V k.1)ᶜ := by
    rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Pullback.range_fst, hcr,
      Set.image_preimage_eq_inter_range, Set.inter_comm]
  have hfc (k : Idx) : Topology.IsConstructible (Set.range (f k)) :=
    (f k).isLocallyClosed_range.isConstructible_of_noetherianSpace
  have hdis : Pairwise (fun k l : Idx ↦ Disjoint (Set.range (f k)) (Set.range (f l))) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    rw [hfr] at hx hy
    rw [hgr] at hx hy
    by_cases ha : k.1 = l.1
    · rcases k with ⟨a, b⟩
      rcases l with ⟨a', b'⟩
      dsimp at ha
      subst a'
      have hb : b ≠ b' := fun h ↦ hkl (by cases h; rfl)
      obtain ⟨z, hz, hzx⟩ := hx.1
      obtain ⟨w, hw, hwx⟩ := hy.1
      have hzw : z = w := (j a).isOpenEmbedding.injective (hzx.trans hwx.symm)
      exact Set.disjoint_left.mp ((T a).pairwise_disjoint_stratum hb) hz (hzw ▸ hw)
    · rcases lt_or_gt_of_ne ha with hal | hla
      · apply hy.2
        exact Set.mem_iUnion.mpr ⟨k.1, Set.mem_iUnion.mpr ⟨hal, by
          obtain ⟨z, _, rfl⟩ := hx.1
          exact ⟨z, rfl⟩⟩⟩
      · apply hx.2
        exact Set.mem_iUnion.mpr ⟨l.1, Set.mem_iUnion.mpr ⟨hla, by
          obtain ⟨z, _, rfl⟩ := hy.1
          exact ⟨z, rfl⟩⟩⟩
  have hcoverf : (⋃ k : Idx, Set.range (f k)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hex : ∃ a : Fin n, x ∈ Set.range (j a) := hcover x
    obtain ⟨a, hax, hmin⟩ := Set.exists_min_image {a : Fin n | x ∈ Set.range (j a)}
      (fun a ↦ a) (Set.toFinite _) hex
    obtain ⟨y, hy⟩ := hax
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp
      ((T a).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y)
    refine Set.mem_iUnion.mpr ⟨⟨a, b⟩, ?_⟩
    rw [hfr, hgr]
    refine ⟨⟨y, hb, hy⟩, ?_⟩
    intro hxV
    obtain ⟨a', hxV⟩ := Set.mem_iUnion.mp hxV
    obtain ⟨ha', hxa'⟩ := Set.mem_iUnion.mp hxV
    exact (not_lt_of_ge (hmin a' hxa')) ha'
  let S : Stratification X := {
    n := Fintype.card Idx
    stratum := fun i ↦ Set.range (f (e i))
    isLocallyClosed_stratum := fun i ↦ (f (e i)).isLocallyClosed_range
    isConstructible_stratum := fun i ↦ hfc (e i)
    iUnion_stratum_eq_univ := by
      rw [← hcoverf]
      exact e.surjective.iUnion_comp (fun k ↦ Set.range (f k))
    pairwise_disjoint_stratum := fun i k hik ↦ hdis (e.injective.ne hik)
    domain := fun i ↦ pullback (g (e i)) (c (e i).1)
    immersion := fun i ↦ f (e i)
    isImmersion := fun i ↦ hf (e i)
    range_immersion := fun i ↦ rfl }
  refine ⟨S, ?_⟩
  intro i
  exact ⟨(e i).1, (e i).2, pullback.fst _ _, rfl⟩

private theorem cover_fixedLocal_pullback {Y X : Scheme.{t}} (b : X ⟶ Y)
    (Λ : Type (t + 1)) [CommRing Λ]
    (G : Sheaf (ProEt.topology Y) (ModuleCat.{t + 1} Λ))
    (hG : ProEtale.IsFiniteLocallyConstant Λ G) :
    ProEtale.IsFiniteLocallyConstant Λ
      ((ProEtale.upperStar (ModuleCat.{t + 1} Λ) b).obj G) := by
  obtain ⟨I, W, g, hg, hm⟩ := hG
  refine ⟨I, fun i ↦ pullback (g i) b, fun i ↦ pullback.snd (g i) b, ?_, ?_⟩
  · exact Precoverage.mem_coverings_of_isPullback g hg b _ _
      (fun i ↦ (IsPullback.of_hasPullback (g i) b).flip)
  · intro i
    obtain ⟨M, hM, ⟨e⟩⟩ := hm i
    let p := pullback.fst (g i) b
    let q := pullback.snd (g i) b
    let E := ModuleCat.{t + 1} Λ
    have heq : q ≫ b = p ≫ g i := pullback.condition.symm
    exact ⟨M, hM, ⟨
      ((ProEtale.upperStarComp E q b).app G).symm ≪≫
      (eqToIso (congrArg (fun f ↦ (ProEtale.upperStar E f).obj G) heq)) ≪≫
      (ProEtale.upperStarComp E p (g i)).app G ≪≫
      (ProEtale.upperStar E p).mapIso e ≪≫
      (Functor.isoWhiskerLeft (constantSheaf (ProEt.topology (W i)) E)
        (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange p) E
          (ProEt.topology (W i)) (ProEt.topology (pullback (g i) b))).symm).app M ≪≫
      ((proEtaleBaseChange p).constantSheafsheafPullbackIso E
        (ProEt.topology (W i)) (ProEt.topology (pullback (g i) b))
        (ProEt.isTerminalMkId (W i))
        ((ProEt.isTerminalMkId (W i)).isTerminalObj (proEtaleBaseChange p) _)).app M⟩⟩

private theorem cover_constructible_iso (X : Scheme.{t}) (A : Type t)
    [CommRing A] [Finite A]
    {F G : proEtaleRingModules X (proEtaleConstantRing X A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf X A F) :
    IsConstructibleProEtaleModuleSheaf X A G := by
  apply (proEtaleModuleRestriction_constructible_iff X A G).mpr
  exact ProEtale.isConstructible_of_iso ((proEtaleModuleRestriction X A).mapIso e)
    ((proEtaleModuleRestriction_constructible_iff X A F).mp hF)

private theorem cover_constructible
    (X : Scheme.{t}) (hX : TopologicalSpace.NoetherianSpace X)
    (A : Type t) [CommRing A] [Finite A]
    (r : ℕ) (U : Fin r → Scheme.{t}) (j : ∀ i, U i ⟶ X)
    (hj : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ x : X, ∃ i : Fin r, ∃ y : U i, (j i).base y = x)
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hF : ∀ i, IsConstructibleProEtaleModuleSheaf (U i) A
      ((proEtaleConstantRingPullback A (j i)).obj F)) :
    IsConstructibleProEtaleModuleSheaf X A F := by
  let E := ModuleCat.{t + 1} (ULift.{t + 1, t} A)
  let G := (proEtaleModuleRestriction X A).obj F
  have hG (i : Fin r) : ProEtale.IsConstructible (ULift.{t + 1, t} A)
      ((ProEtale.upperStar E (j i)).obj G) := by
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback (j i) A F
    exact ProEtale.isConstructible_of_iso e
      ((proEtaleModuleRestriction_constructible_iff (U i) A _).mp (hF i))
  choose T hT using hG
  obtain ⟨S, hS⟩ := cover_stratification X hX r U j hj hcover T
  apply (proEtaleModuleRestriction_constructible_iff X A F).mpr
  refine ⟨S, fun i ↦ ?_⟩
  obtain ⟨a, b, q, hq⟩ := hS i
  let e : (ProEtale.upperStar E (S.immersion i)).obj G ≅
      (ProEtale.upperStar E q).obj
        ((ProEtale.upperStar E ((T a).immersion b)).obj
          ((ProEtale.upperStar E (j a)).obj G)) :=
    eqToIso (congrArg (fun f ↦ (ProEtale.upperStar E f).obj G) hq.symm) ≪≫
    (ProEtale.upperStarComp E q ((T a).immersion b ≫ j a)).app G ≪≫
    (ProEtale.upperStar E q).mapIso
      ((ProEtale.upperStarComp E ((T a).immersion b) (j a)).app G)
  exact ProEtale.isFiniteLocallyConstant_of_iso e.symm
    (cover_fixedLocal_pullback q _ _ (hT a b))

private noncomputable def cover_tensorModel (X : Scheme.{t})
    (A : Type t) [CommRing A] : ProEtaleTensorModel X (proEtaleConstantRing X A) where
  tensor := @MonoidalCategory.tensor (proEtaleDerivedCategory X A) _
    (RingedDerivedNative.monoidal.{t + 1, t, 0} (ProEt.topology X) (proEtaleConstantRing X A))
  representative := NatIso.ofComponents
    (fun P ↦ RingedDerivedNative.tensorIso.{t + 1, t, 0} (ProEt.topology X)
      (proEtaleConstantRing X A) P.1.obj P.2.obj (Or.inl P.1.property.1))
    (fun f ↦ RingedDerivedNative.tensorIso_naturality.{t + 1, t, 0} (ProEt.topology X)
      (proEtaleConstantRing X A) _ _ _ _ _ _ f.1.hom f.2.hom)

private theorem cover_tensor_iso (X : Scheme.{t}) (A : Type t) [CommRing A]
    (K L : proEtaleDerivedCategory X A) :
    Nonempty (proEtaleDerivedTensor X A K L ≅ (cover_tensorModel X A).tensor.obj (K, L)) := by
  let K₀ : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ :=
    DerivedCategory.Q.objPreimage K
  let L₀ : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ :=
    DerivedCategory.Q.objPreimage L
  let ex := CochainComplex.exists_isKFlatResolutionGeneral K₀
  let P := Classical.choose ex
  let f := Classical.choose (Classical.choose_spec ex)
  have hf := (Classical.choose_spec (Classical.choose_spec ex)).2.2.1
  have hP := (Classical.choose_spec (Classical.choose_spec ex)).1
  have : QuasiIso f := hf
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mpr hf
  let eK : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let eL : DerivedCategory.Q.obj L₀ ≅ L := DerivedCategory.Q.objObjPreimageIso L
  exact ⟨RingedDerivedNative.tensorIso.{t + 1, t, 0} (ProEt.topology X) (proEtaleConstantRing X A)
    P L₀ (Or.inl hP) ≪≫ (cover_tensorModel X A).tensor.mapIso (eK.prod eL)⟩

private theorem cover_tensor_single_pullback {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : Type t) [CommRing A]
    (K : proEtaleDerivedCategory Y A)
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    Nonempty ((proEtaleConstantRingDerivedPullback A f).obj
      (proEtaleDerivedTensor Y A K ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      proEtaleDerivedTensor X A ((proEtaleConstantRingDerivedPullback A f).obj K)
        ((DerivedCategory.singleFunctor _ 0).obj
          ((proEtaleConstantRingPullback A f).obj F))) := by
  let L := (DerivedCategory.singleFunctor _ 0).obj F
  let P := proEtaleConstantRingDerivedPullback A f
  obtain ⟨eY⟩ := cover_tensor_iso Y A K L
  obtain ⟨eX⟩ := cover_tensor_iso X A (P.obj K)
    ((DerivedCategory.singleFunctor _ 0).obj ((proEtaleConstantRingPullback A f).obj F))
  let alpha := proEtaleCanonicalTensorComparison f
    (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A) (cover_tensorModel Y A) (cover_tensorModel X A)
  let eS := ((proEtaleConstantRingPullback A f).mapDerivedCategorySingleFunctor 0).app F
  exact ⟨P.mapIso eY ≪≫ alpha.app (K, L) ≪≫
    (cover_tensorModel X A).tensor.mapIso ((Iso.refl (P.obj K)).prod eS) ≪≫ eX.symm⟩

/-- Finite-cover locality of bounded constructibility and a fixed Tor interval.
Source: Stacks Project, `etale-cohomology.tex`, Tag 095F, label
`lemma-constructible-local`; the finite-cover intrinsic pro-etale formulation and its
uniform Tor interval are the blueprint node
`lem-sf-finite-cover-ctf-locality` (blueprint: lem-sf-finite-cover-ctf-locality).
Proof: encode constant-ring module sheaves as sheaves of modules over the fixed
finite ring. The restriction equivalence and its pullback comparison reduce detection
of zero sheaves to the existing jointly-surjective quasi-compact pullback criterion.
Exact pullback commutes with homology, so the global cohomological support is contained
in the finite union of the local supports.
For constructibility, order the cover and intersect each local stratum with the closed
complement of the earlier opens. Pullback constructs the resulting immersed strata
and their factorization through the original local strata. Noetherianity makes their
locally closed images constructible. They are disjoint and cover X. Base-changing a
trivializing pro-etale family preserves finite local constancy: composition identifies
the pullbacks and inverse image preserves constant module sheaves. Transport back
through the encoding equivalence gives intrinsic constructibility.
Finally compare the resolution-chosen intrinsic tensor with the native localization
tensor using the K-flat representative isomorphism. The canonical pro-etale tensor
pullback comparison, together with exact pullback of degree-zero sheaves, identifies
its restriction with each local tensor. Local Tor vanishing and zero detection give
global vanishing outside the same interval. Empty covers and the zero ring require
no separate nonemptiness assumption.
-/
theorem finiteCoverCTFLocality
    (X : Scheme.{t})
    (hX : TopologicalSpace.NoetherianSpace X)
    (A : Type t) [CommRing A] [Finite A]
    (r : ℕ) (U : Fin r → Scheme.{t})
    (j : ∀ i : Fin r, U i ⟶ X)
    (hj : ∀ i : Fin r, IsOpenImmersion (j i))
    (hcover : ∀ x : X, ∃ i : Fin r, ∃ y : U i, (j i).base y = x)
    (K : proEtaleDerivedCategory X A)
    (a b : ℤ) (hab : a ≤ b)
    (hlocal : ∀ i : Fin r, Set.Finite {t : ℤ |
      ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) t).obj
          ((proEtaleConstantRingDerivedPullback A (j i)).obj K))})
    (hconstructible : ∀ (i : Fin r) (t : ℤ),
      IsConstructibleProEtaleModuleSheaf (U i) A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) t).obj
            ((proEtaleConstantRingDerivedPullback A (j i)).obj K)))
    (htor : ∀ (i : Fin r)
      (F : proEtaleRingModules (U i) (proEtaleConstantRing (U i) A))
      (t : ℤ), t < a ∨ b < t →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) t).obj
          (proEtaleDerivedTensor (U i) A
            ((proEtaleConstantRingDerivedPullback A (j i)).obj K)
            ((DerivedCategory.singleFunctor
              (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) 0).obj F)))) :
    Set.Finite {t : ℤ |
      ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) t).obj K)} ∧
    (∀ t : ℤ,
      IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X A)) t).obj K)) ∧
    (∀ (F : proEtaleRingModules X (proEtaleConstantRing X A)) (t : ℤ),
      t < a ∨ b < t →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) t).obj
          (proEtaleDerivedTensor X A K
            ((DerivedCategory.singleFunctor
              (proEtaleRingModules X (proEtaleConstantRing X A)) 0).obj F)))) := by
  have _ := hab
  have hzero (L : proEtaleDerivedCategory X A) (n : ℤ)
      (hL : ∀ i, IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((proEtaleConstantRingDerivedPullback A (j i)).obj L))) :
      IsZero ((DerivedCategory.homologyFunctor _ n).obj L) := by
    apply cover_isZero X hX A r U j hj hcover
    intro i
    exact (hL i).of_iso
      (((proEtaleConstantRingPullback A (j i)).mapDerivedCategoryHomologyFunctorIso n).app L)
  refine ⟨?_, ?_, ?_⟩
  · apply (Set.finite_iUnion hlocal).subset
    intro n hn
    by_contra h
    apply hn
    apply hzero K n
    intro i
    by_contra hi
    exact h (Set.mem_iUnion.mpr ⟨i, hi⟩)
  · intro n
    apply cover_constructible X hX A r U j hj hcover
    intro i
    exact cover_constructible_iso (U i) A
      (((proEtaleConstantRingPullback A (j i)).mapDerivedCategoryHomologyFunctorIso n).app K).symm
      (hconstructible i n)
  · intro F n hn
    apply hzero
    intro i
    obtain ⟨e⟩ := cover_tensor_single_pullback (j i) A K F
    exact (htor i ((proEtaleConstantRingPullback A (j i)).obj F) n hn).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e)

end AlgebraicGeometry.Scheme
