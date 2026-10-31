/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FilteredCondensedRepresentingPairData
import WeilConjectures.AlgebraicGeometry.FilteredCondensedCanonicalComparisons
import WeilConjectures.AlgebraicGeometry.FilteredCondensedCounitFiniteFormula
import WeilConjectures.AlgebraicGeometry.FilteredCondensedCounitBijective

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
attribute [local irreducible] CondensedRing.boundedConstructibleLowerShriekOfCompactification
  constructibleExtendScalars constructibleToPadicAlgCl
  constructibleToPadicAlgClCompIso
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

private theorem transpose_of_counit_bijections
    {A : Type*} {D : Type*} [Category A] [Category D]
    (P : A ⥤ D) (M : A) (L : D) (t : P.obj M ⟶ L)
    (B : ∀ C : A, (C ⟶ M) ≃ (P.obj C ⟶ L))
    (hf : ∀ (C : A) (u : C ⟶ M), B C u = P.map u ≫ t)
    (J : D ⥤ A) (adj : P ⊣ J) :
    IsIso (adj.homEquiv M L t) ∧
      P.map (adj.homEquiv M L t) ≫ adj.counit.app L = t ∧
      ∀ v : M ⟶ J.obj L,
        P.map v ≫ adj.counit.app L = t → v = adj.homEquiv M L t := by
  have hc : P.map (adj.homEquiv M L t) ≫ adj.counit.app L = t := by
    simpa only [Adjunction.homEquiv_counit] using (adj.homEquiv M L).symm_apply_apply t
  refine ⟨?_, hc, ?_⟩
  · apply isIso_of_yoneda_map_bijective
    intro C
    have heq : (fun u : C ⟶ M ↦ u ≫ adj.homEquiv M L t) =
        fun u ↦ adj.homEquiv C L (B C u) := by
      funext u
      rw [hf, adj.homEquiv_naturality_left]
    rw [heq]
    exact (adj.homEquiv C L).bijective.comp (B C).bijective
  · intro v hv
    apply (adj.homEquiv M L).symm.injective
    simpa only [Adjunction.homEquiv_counit, hc] using hv

private theorem transpose_data_square
    {A : Type*} {D : Type*} [Category A] [Category D]
    (P : A ⥤ D) {M M' : A} {L L' : D}
    (t : P.obj M ⟶ L) (t' : P.obj M' ⟶ L')
    (a : M ⟶ M') (b : L ⟶ L') (h : P.map a ≫ t' = t ≫ b)
    (J : D ⥤ A) (adj : P ⊣ J) :
    a ≫ adj.homEquiv M' L' t' = adj.homEquiv M L t ≫ J.map b := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right, h]

private theorem induced_natural_unique {s : ScalarComparisons l k c}
    {E : PadicAlgCl.FiniteIntermediateField l} (d : Pair l k c s E)
    (B B' : d.OmegaBijections l k c)
    (hi : d.IsInduced l k c B) (hn : d.IsNatural l k c B)
    (hi' : d.IsInduced l k c B') (hn' : d.IsNatural l k c B') : B' = B := by
  let h : E ≤ E := le_rfl
  let D := (constructibleExtendScalars X.left l h).obj d.M
  let e := (constructibleToPadicAlgClCompIso X.left l h).app d.M
  have he : B' _ e.hom = B _ e.hom := by
    have h1 := hi E h D (𝟙 D)
    have h2 := hi' E h D (𝟙 D)
    simp only [(constructibleToPadicAlgCl X.left l E).map_id, Category.id_comp] at h1 h2
    exact h2.trans h1.symm
  have hv : B' (d.omegaM l k c) (𝟙 _) = B (d.omegaM l k c) (𝟙 _) := by
    apply (cancel_epi ((omegaSupport l k c).map e.hom)).1
    have h1 := hn _ _ e.hom (𝟙 _)
    have h2 := hn' _ _ e.hom (𝟙 _)
    simp only [Category.comp_id] at h1 h2
    exact h2.symm.trans (he.trans h1)
  funext C
  apply Equiv.ext
  intro u
  calc
    B' C u = (omegaSupport l k c).map u ≫ B' (d.omegaM l k c) (𝟙 _) := by
      simpa only [Category.comp_id] using hn' _ _ u (𝟙 _)
    _ = (omegaSupport l k c).map u ≫ B (d.omegaM l k c) (𝟙 _) := by rw [hv]
    _ = B C u := by simpa only [Category.comp_id] using (hn _ _ u (𝟙 _)).symm

private theorem induced_data_naturality {s : ScalarComparisons l k c}
    {E F : PadicAlgCl.FiniteIntermediateField l}
    (d : Pair l k c s E) (d' : Pair l k c s F)
    (B : d.OmegaBijections l k c) (B' : d'.OmegaBijections l k c)
    (hi : d.IsInduced l k c B) (hn : d.IsNatural l k c B)
    (hi' : d'.IsInduced l k c B') (hn' : d'.IsNatural l k c B')
    (m : DataMap l k c d d')
    (C : PadicAlgClConstructible X.left l) (u : C ⟶ d.omegaM l k c) :
    B' C (u ≫ m.omegaA l k c) = B C u ≫ m.omegaB l k c := by
  let D := (constructibleExtendScalars X.left l m.hE).obj d.M
  let e := (constructibleToPadicAlgClCompIso X.left l m.hE).app d.M
  have he : B' _ (e.hom ≫ m.omegaA l k c) = B _ e.hom ≫ m.omegaB l k c := by
    have hm : e.hom ≫ m.omegaA l k c =
        (constructibleToPadicAlgCl X.left l m.H).map m.a ≫
          (constructibleToPadicAlgClCompIso X.left l m.hF).hom.app d'.M := by
      simp only [DataMap.omegaA, e, Iso.app_hom,
        Iso.hom_inv_id_app_assoc]
    rw [hm]
    trans (s.omega m.H).inv.app D ≫
      (constructibleToPadicAlgCl Y.left l m.H).map (d'.beta m.H m.hF D m.a) ≫
        (constructibleToPadicAlgClCompIso Y.left l m.hF).hom.app d'.L
    · exact hi' m.H m.hF D m.a
    · have h0 := hi m.H m.hE D (𝟙 D)
      simp only [(constructibleToPadicAlgCl X.left l m.H).map_id,
        Category.id_comp] at h0
      apply Eq.trans ?_ (congrArg (fun z ↦ z ≫ m.omegaB l k c) h0.symm)
      have hc := m.compatible D (𝟙 D)
      simp only [Category.id_comp] at hc
      have hcmap := congrArg (constructibleToPadicAlgCl Y.left l m.H).map hc
      have hcmap' := hcmap.trans
        ((constructibleToPadicAlgCl Y.left l m.H).map_comp _ _)
      apply (congrArg (fun z ↦ (s.omega m.H).inv.app D ≫ z ≫
        (constructibleToPadicAlgClCompIso Y.left l m.hF).hom.app d'.L) hcmap').trans
      simp only [DataMap.omegaB, Category.assoc, Iso.hom_inv_id_app_assoc]
  have hv : B' (d.omegaM l k c) (m.omegaA l k c) =
      B (d.omegaM l k c) (𝟙 _) ≫ m.omegaB l k c := by
    apply (cancel_epi ((omegaSupport l k c).map e.hom)).1
    have hb := hn _ _ e.hom (𝟙 _)
    simp only [Category.comp_id] at hb
    exact (hn' _ _ e.hom (m.omegaA l k c)).symm.trans
      (he.trans ((congrArg (fun z ↦ z ≫ m.omegaB l k c) hb).trans
        (Category.assoc _ _ _)))
  have hb := hn _ _ u (𝟙 _)
  simp only [Category.comp_id] at hb
  exact (hn' _ _ u (m.omegaA l k c)).trans
    ((congrArg (fun z ↦ (omegaSupport l k c).map u ≫ z) hv).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z ↦ z ≫ m.omegaB l k c) hb.symm)))

/-- Compatible finite-field representing bijections descend uniquely, and their counit
has an invertible transpose under every specified right adjoint.

Source: blueprint sk-thm-sp-qbar, filtered Hom-colimit display and model-independence
paragraph; sk-prop-sp-unique-adjoint-categorical, Transposes, Naturality, Inverse, Uniqueness.
(blueprint: lem-pur-filtered-condensed-representing-pair).

Proof:
1. canonical_scalar_comparisons restricts the original projection mates to the bounded
constructible categories. For each compatible pair, counit_map_bijective makes the
explicit map u ↦ P(u) followed by omegaCounit into an equivalence, with no chosen model.
2. counit_finite_formula gives the finite representative values. Functoriality gives
naturality and the counit identity. Naturality transports the finite formula through
any model isomorphism, so it is independent of every model and representative.
3. Any two induced natural bijections agree at the invertible transitivity map from
T_E,Omega(T_E,E M) to T_E,Omega M, by their finite formula at the identity. Cancel its
support image using naturality to get agreement at the identity of M_Omega. Naturality
then gives agreement at every u. No extra descent statement is needed for uniqueness.
4. For a pair map over its common finite field, the induced formulas at a and at the
identity, finite pair-map compatibility, and the transitivity inverse identities give
the comparison square at the transitivity map. Cancel its support image and use
naturality to obtain the square for every test object and arrow.
5. For the specified adjunction P adjoint J, postcomposition with the transpose of
the extended counit equals B followed by adj.homEquiv. This is bijective on every Hom
set, so isIso_of_yoneda_map_bijective gives invertibility. The inverse adjunction
bijection gives the counit equation and uniqueness. Its left and right naturality,
applied to the pair-map counit square, give transpose naturality. -/
public theorem filtered_condensed_representing_pair :
    ∃ s : ScalarComparisons l k c, s.IsCanonical l k c ∧
      ∀ (E : PadicAlgCl.FiniteIntermediateField l) (d : Pair l k c s E),
        d.IsCompatible l k c → ∃! B : d.OmegaBijections l k c, d.IsDescent l k c B := by
  classical
  obtain ⟨s, hs⟩ := canonical_scalar_comparisons l k c
  refine ⟨s, hs, ?_⟩
  intro E d hd
  let B : d.OmegaBijections l k c := fun C ↦ Equiv.ofBijective
    (fun u ↦ (omegaSupport l k c).map u ≫ d.omegaCounit l k c)
    (counit_map_bijective l k c hs d hd C)
  have hf (C : PadicAlgClConstructible X.left l) (u : C ⟶ d.omegaM l k c) :
      B C u = (omegaSupport l k c).map u ≫ d.omegaCounit l k c := rfl
  have hi : d.IsInduced l k c B := by
    intro H h C a
    exact counit_finite_formula l k c hs d hd H h C a
  have hn : d.IsNatural l k c B := by
    intro C D h a
    simp only [hf, Functor.map_comp, Category.assoc]
  have hid : B (d.omegaM l k c) (𝟙 _) = d.omegaCounit l k c := by
    rw [hf, (omegaSupport l k c).map_id, Category.id_comp]
  have hu : ∀ B' : d.OmegaBijections l k c,
      d.IsInduced l k c B' → d.IsNatural l k c B' → B' = B := by
    intro B' hi' hn'
    exact induced_natural_unique l k c d B B' hi hn hi' hn'
  refine ⟨B, ?_, ?_⟩
  · refine ⟨hi, hn, hf, hid, hu, ?_, ?_, ?_⟩
    · intro H h D C e u v he
      calc
        B C u = (omegaSupport l k c).map e.inv ≫ B _ (e.hom ≫ u) := by
          rw [hn]
          rw [← Category.assoc, ← (omegaSupport l k c).map_comp,
            e.inv_hom_id, (omegaSupport l k c).map_id, Category.id_comp]
        _ = _ := by
          rw [he]
          exact congrArg (fun z ↦ (omegaSupport l k c).map e.inv ≫ z) (hi H h D v)
    · intro J adj
      exact transpose_of_counit_bijections (omegaSupport l k c) _ _ _ B hf J adj
    · intro F d' hd' B' hi' hn' m
      have hm := induced_data_naturality l k c d d' B B' hi hn hi' hn' m
      refine ⟨hm, ?_⟩
      intro J adj
      have hsq : (omegaSupport l k c).map (m.omegaA l k c) ≫
          d'.omegaCounit l k c = d.omegaCounit l k c ≫ m.omegaB l k c := by
        let B0 : d'.OmegaBijections l k c := fun C ↦ Equiv.ofBijective
          (fun u ↦ (omegaSupport l k c).map u ≫ d'.omegaCounit l k c)
          (counit_map_bijective l k c hs d' hd' C)
        have hi0 : d'.IsInduced l k c B0 := by
          intro H h C a
          exact counit_finite_formula l k c hs d' hd' H h C a
        have hn0 : d'.IsNatural l k c B0 := by
          intro C D h a
          change (omegaSupport l k c).map (h ≫ a) ≫ d'.omegaCounit l k c =
            (omegaSupport l k c).map h ≫
              ((omegaSupport l k c).map a ≫ d'.omegaCounit l k c)
          simp only [Functor.map_comp, Category.assoc]
        have heq := induced_natural_unique l k c d' B0 B' hi0 hn0 hi' hn'
        have h := hm (d.omegaM l k c) (𝟙 _)
        rw [heq, Category.id_comp, hid] at h
        exact h
      exact transpose_data_square (omegaSupport l k c) _ _
        (m.omegaA l k c) (m.omegaB l k c) hsq J adj
  · intro B' hB'
    exact hu B' hB'.1 hB'.2.1

end WeilConjectures.FilteredCondensedRepresentingPair
