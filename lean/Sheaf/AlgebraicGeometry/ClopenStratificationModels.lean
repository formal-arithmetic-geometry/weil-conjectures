/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback

/-!
# Constructible strata and finite module models across a clopen partition

Source: Stacks Project, topology.tex, Tags 005J and 09YD; sites-modules.tex,
Tags 03D8 and 093R; blueprint main-20261015, def-weil-finite-torsion-constructibility
(blueprint: lem-pur-clopen-stratification-models).

## Main statements

* `clopenStratification_pullback`: the actual fibre-product strata partition each component.
* `clopenStratification_union`: the original stratum schemes partition the whole scheme.
* `clopenStratification_pullback_models`: the base-changed covers retain the same modules.
* `clopenStratification_union_models`: the original covers and modules remain unchanged.
* `isConstructibleProEtaleModuleSheaf_iff_clopen`: constructibility is detected componentwise.

The geometric conclusions list the defining stratification conditions on the indicated
finite index sets directly. Thus they specify the exact fibre-product schemes and exact
sigma-indexed union, without choosing substitute scheme structures or reindexing them.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem constantPullbackComp
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) :
    Nonempty (proEtaleConstantModulePullback (f ≫ g) A F ≅
      proEtaleConstantModulePullback f A (proEtaleConstantModulePullback g A F)) := by
  let D := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  obtain ⟨e₁⟩ := proEtaleModuleRestriction_pullback (f ≫ g) A F
  obtain ⟨e₂⟩ := proEtaleModuleRestriction_pullback f A
    (proEtaleConstantModulePullback g A F)
  obtain ⟨e₃⟩ := proEtaleModuleRestriction_pullback g A F
  exact ⟨(proEtaleModuleEncoding Z A).fullyFaithfulFunctor.preimageIso
    (e₁ ≪≫ (ProEtale.upperStarComp D f g).app _ ≪≫
      (ProEtale.upperStar D f).mapIso e₃.symm ≪≫ e₂.symm)⟩

/-- Restrict a constructible immersed stratification to each member of a finite clopen
partition, retaining its actual fibre products, including empty ones.
Source: Stacks Project, Tags 005J and 09XZ
(blueprint: lem-pur-clopen-stratification-models).

Proof: put U_i = range j_i and identify X_i with its open subscheme. Apply
lemma-constructible-pullback-stratification to the immersed strata: base change preserves
immersions, the images are inverse images of the original strata, and inverse image preserves
local closedness, disjointness and the covering equality. Tag 005J, recorded as
lem-weil-pbc-constructible-open-restriction, preserves constructibility in U_i.
Neither this argument nor the finite indexing requires nonempty strata or components. -/
theorem clopenStratification_pullback
    (X : Scheme.{u}) (I : Type v) [Finite I] (Xi : I → Scheme.{u})
    (j : ∀ i, Xi i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : (⋃ i, Set.range (j i)) = Set.univ)
    (S : FiniteLocallyClosedStratification X)
    (hS : ∀ n, Topology.IsConstructible (S.stratum n)) (i : I) :
    (∀ n : Fin S.n, IsImmersion (pullback.snd (S.immersion n) (j i))) ∧
    (∀ n : Fin S.n, IsLocallyClosed (Set.range (pullback.snd (S.immersion n) (j i)))) ∧
    (∀ n : Fin S.n,
      Topology.IsConstructible (Set.range (pullback.snd (S.immersion n) (j i)))) ∧
    Pairwise (fun n m : Fin S.n ↦
      Disjoint (Set.range (pullback.snd (S.immersion n) (j i)))
        (Set.range (pullback.snd (S.immersion m) (j i)))) ∧
    (⋃ n : Fin S.n, Set.range (pullback.snd (S.immersion n) (j i))) = Set.univ := by
  let T : Stratification X := { S with isConstructible_stratum := hS }
  let U := T.pullback (j i)
  have hr (n : Fin S.n) :
      Set.range (pullback.snd (S.immersion n) (j i)) = U.stratum n :=
    U.range_immersion n
  refine ⟨fun n ↦ U.isImmersion n, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hr]
    exact U.isLocallyClosed_stratum n
  · intro n
    rw [hr]
    exact U.isConstructible_stratum n
  · intro n m hnm
    rw [hr, hr]
    exact U.pairwise_disjoint_stratum hnm
  · simp_rw [hr]
    exact U.iUnion_stratum_eq_univ

/-- Combine component stratifications, retaining every original stratum scheme and using
the finite sigma type as index set. Only the immersion into the ambient scheme changes.
Source: Stacks Project, Tags 09YD and 09XZ
(blueprint: lem-pur-clopen-stratification-models).

Proof: factor each immersion into a closed immersion into an open subscheme of X_i.
That open subscheme is also open in X, with the identical structure sheaf, so composition
with j_i is an immersion. Its image is locally closed. Disjointness follows within each
component from its stratification, and between components from hdisjoint; hcover gives
coverage. Each clopen image U_i is retrocompact: its intersection with a quasi-compact open
is closed there, hence quasi-compact. Apply lem-weil-pbc-constructible-image-retrocompact-open
(Tag 09YD). Finiteness of I and of every Fin (S i).n gives finiteness of the sigma type.
No underlying stratum scheme or trivializing cover is replaced. -/
theorem clopenStratification_union
    (X : Scheme.{u}) (I : Type v) [Finite I] (Xi : I → Scheme.{u})
    (j : ∀ i, Xi i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : (⋃ i, Set.range (j i)) = Set.univ)
    (S : ∀ i, FiniteLocallyClosedStratification (Xi i))
    (hS : ∀ i n, Topology.IsConstructible ((S i).stratum n)) :
    (∀ p : (Σ i, Fin (S i).n), IsImmersion ((S p.1).immersion p.2 ≫ j p.1)) ∧
    (∀ p : (Σ i, Fin (S i).n),
      IsLocallyClosed (Set.range ((S p.1).immersion p.2 ≫ j p.1))) ∧
    (∀ p : (Σ i, Fin (S i).n),
      Topology.IsConstructible (Set.range ((S p.1).immersion p.2 ≫ j p.1))) ∧
    Pairwise (fun p q : (Σ i, Fin (S i).n) ↦
      Disjoint (Set.range ((S p.1).immersion p.2 ≫ j p.1))
        (Set.range ((S q.1).immersion q.2 ≫ j q.1))) ∧
    (⋃ p : (Σ i, Fin (S i).n), Set.range ((S p.1).immersion p.2 ≫ j p.1)) =
      Set.univ := by
  classical
  have hi (p : Σ i, Fin (S i).n) :
      IsImmersion ((S p.1).immersion p.2 ≫ j p.1) := by
    have := (S p.1).isImmersion p.2
    infer_instance
  have hr (p : Σ i, Fin (S i).n) :
      Set.range ((S p.1).immersion p.2 ≫ j p.1) =
        j p.1 '' (S p.1).stratum p.2 := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (S p.1).range_immersion]
  refine ⟨hi, fun p ↦ ?_, ?_, ?_, ?_⟩
  · have := hi p
    exact Scheme.Hom.isLocallyClosed_range _
  · intro p
    rw [hr]
    apply (hS p.1 p.2).image_of_isOpenEmbedding (j p.1).isOpenEmbedding
    intro V hV _
    exact hV.inter_left (j p.1).isClosedEmbedding.isClosed_range
  · intro p q hpq
    rw [hr, hr]
    by_cases h : p.1 = q.1
    · obtain ⟨i, n⟩ := p
      obtain ⟨k, m⟩ := q
      dsimp at h
      subst k
      have hnm : n ≠ m := fun h ↦ hpq (congrArg (Sigma.mk i) h)
      exact ((S i).pairwise_disjoint_stratum hnm).image
        (j i).isOpenEmbedding.injective.injOn
        (Set.subset_univ _) (Set.subset_univ _)
    · exact (hdisjoint h).mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, Set.range (j i) := hcover.symm ▸ Set.mem_univ x
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
    have hy : y ∈ ⋃ n, (S i).stratum n :=
      (S i).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨⟨i, n⟩, (hr ⟨i, n⟩).symm ▸ ⟨y, hn, rfl⟩⟩

/-- The restricted stratification trivializes the restricted sheaf on the exact
base-changed covers with the exact original finite modules.
Source: Stacks Project, Tags 03D8 and 093R
(blueprint: lem-pur-clopen-stratification-models).

Proof: for T = S_n ×_X X_i write a and b for its projections. Restriction to
constant scalars commutes with the specified intrinsic pullbacks. Lift the fixed-module
compositor through the fully faithful encoding to identify a^*s_n^*F with b^*j_i^*F,
using the pullback-square equation. Apply lem-exc-proetale-pullback-locally-constant
to a and the supplied models. It retains the exact base-changed cover and each module M.
Restrict the comparison isomorphism to each cover member and compose it with that model.
No point or nonemptiness assumption is introduced. -/
theorem clopenStratification_pullback_models
    (X : Scheme.{u}) (I : Type v) [Finite I] (Xi : I → Scheme.{u})
    (j : ∀ i, Xi i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : (⋃ i, Set.range (j i)) = Set.univ)
    (S : FiniteLocallyClosedStratification X)
    (hS : ∀ n, Topology.IsConstructible (S.stratum n))
    (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (R : Fin S.n → Type (u + 1)) (W : ∀ n, R n → (S.domain n).ProEt)
    (a : ∀ n r, W n r ⟶ ProEt.mk (𝟙 (S.domain n)))
    (hc : ∀ n, Presieve.ofArrows (W n) (a n) ∈
      (ProEt.precoverage (S.domain n)).coverings _)
    (M : ∀ n, R n → ModuleCat.{u + 1} (ULift.{u + 1, u} A))
    (hfinite : ∀ n r, Finite (M n r))
    (he : ∀ n r, Nonempty
      ((proEtaleConstantModulePullback (S.immersion n) A F).over (W n r) ≅
        proEtaleConstantModuleSheafOver (S.domain n) A (W n r) (M n r))) :
    ∀ (i : I) (n : Fin S.n),
      ∃ b : ∀ r, (proEtaleBaseChange (pullback.fst (S.immersion n) (j i))).obj (W n r) ⟶
          ProEt.mk (𝟙 (pullback (S.immersion n) (j i))),
        Presieve.ofArrows
            (fun r ↦ (proEtaleBaseChange (pullback.fst (S.immersion n) (j i))).obj (W n r))
            b ∈ (ProEt.precoverage (pullback (S.immersion n) (j i))).coverings _ ∧
          ∀ r, Nonempty
            ((proEtaleConstantModulePullback (pullback.snd (S.immersion n) (j i)) A
                (proEtaleConstantModulePullback (j i) A F)).over
                  ((proEtaleBaseChange (pullback.fst (S.immersion n) (j i))).obj (W n r)) ≅
              proEtaleConstantModuleSheafOver (pullback (S.immersion n) (j i)) A
                ((proEtaleBaseChange (pullback.fst (S.immersion n) (j i))).obj (W n r))
                (M n r)) := by
  intro i n
  obtain ⟨b, hb, hm, _⟩ := proEtaleConstantModulePullback_locallyConstant
    (pullback.fst (S.immersion n) (j i)) A
    (proEtaleConstantModulePullback (S.immersion n) A F)
    (R n) (W n) (a n) (hc n) (M n) (hfinite n) (he n)
  refine ⟨b, hb, fun r ↦ ?_⟩
  obtain ⟨c₁⟩ := constantPullbackComp (pullback.snd (S.immersion n) (j i)) (j i) A F
  obtain ⟨c₂⟩ := constantPullbackComp
    (pullback.fst (S.immersion n) (j i)) (S.immersion n) A F
  let e := c₁.symm
    ≪≫ eqToIso (congrArg (fun f ↦ proEtaleConstantModulePullback f A F)
      pullback.condition.symm)
    ≪≫ c₂
  obtain ⟨er⟩ := hm r
  exact ⟨(SheafOfModules.overFunctor _ _).mapIso e ≪≫ er⟩

/-- Union of component strata retains the exact supplied local covers and finite modules.
Source: Stacks Project, Tag 03D8, and blueprint finite-torsion constructibility
(blueprint: lem-pur-clopen-stratification-models).

Proof: restrict to constant scalars using the published module encoding equivalence.
Its pullback comparison identifies the specified intrinsic tensor pullbacks with the fixed
module inverse images. The fixed-module compositor gives the composite comparison, which
lifts through the fully faithful encoding. Restrict this module isomorphism to each given
cover member and compose with the supplied model isomorphism. Thus every stratum scheme,
cover object, covering arrow and finite module remains the original one. -/
theorem clopenStratification_union_models
    (X : Scheme.{u}) (I : Type v) [Finite I] (Xi : I → Scheme.{u})
    (j : ∀ i, Xi i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : (⋃ i, Set.range (j i)) = Set.univ)
    (S : ∀ i, FiniteLocallyClosedStratification (Xi i))
    (hS : ∀ i n, Topology.IsConstructible ((S i).stratum n))
    (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (R : ∀ i, Fin (S i).n → Type (u + 1))
    (W : ∀ i n, R i n → ((S i).domain n).ProEt)
    (a : ∀ i n r, W i n r ⟶ ProEt.mk (𝟙 ((S i).domain n)))
    (hc : ∀ i n, Presieve.ofArrows (W i n) (a i n) ∈
      (ProEt.precoverage ((S i).domain n)).coverings _)
    (M : ∀ i n, R i n → ModuleCat.{u + 1} (ULift.{u + 1, u} A))
    (hfinite : ∀ i n r, Finite (M i n r))
    (he : ∀ i n r, Nonempty
      ((proEtaleConstantModulePullback ((S i).immersion n) A
          (proEtaleConstantModulePullback (j i) A F)).over (W i n r) ≅
        proEtaleConstantModuleSheafOver ((S i).domain n) A (W i n r) (M i n r))) :
    ∀ i n r, Nonempty
      ((proEtaleConstantModulePullback ((S i).immersion n ≫ j i) A F).over (W i n r) ≅
        proEtaleConstantModuleSheafOver ((S i).domain n) A (W i n r) (M i n r)) := by
  intro i n r
  obtain ⟨e⟩ := he i n r
  obtain ⟨c⟩ := constantPullbackComp ((S i).immersion n) (j i) A F
  exact ⟨(SheafOfModules.overFunctor _ _).mapIso c ≪≫ e⟩

private theorem fixedFinitePullback {Y X : Scheme.{u}} (b : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (G : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (hG : ProEtale.IsFiniteLocallyConstant (ULift.{u + 1, u} A) G) :
    ProEtale.IsFiniteLocallyConstant (ULift.{u + 1, u} A)
      ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) b).obj G) := by
  let E := proEtaleModuleEncoding Y A
  let F := E.inverse.obj G
  have hF := (finiteLocal_iff Y A F).mp
    (ProEtale.isFiniteLocallyConstant_of_iso (E.counitIso.app G).symm hG)
  have hp := proEtale_finiteLocalConstancy_pullback b A F hF
  obtain ⟨e⟩ := proEtaleModuleRestriction_pullback b A F
  exact ProEtale.isFiniteLocallyConstant_of_iso
    (e ≪≫ (ProEtale.upperStar _ b).mapIso (E.counitIso.app G))
    ((finiteLocal_iff X A _).mpr hp)

/-- Constructibility of an intrinsic constant-ring module sheaf is equivalent to
constructibility on every piece of a finite clopen partition, including an empty partition
of the empty scheme. Source: blueprint main-20261015, finite-torsion constructibility,
and Stacks Project, Tags 005J, 09YD, 03D8 and 093R
(blueprint: lem-pur-clopen-stratification-models).

Proof: use proEtaleModuleRestriction_constructible_iff to express the intrinsic
predicate by finite constant models in the fixed-module encoding. The published pullback
comparison identifies the encoded component restriction with fixed-module inverse image.
For the forward direction pull the stratification back and apply finite local constancy
under inverse image on every stratum. The pullback-square equation and the fixed-module
compositors identify the two iterated restrictions. For the converse choose component
stratifications and apply clopenStratification_union to their underlying finite locally
closed stratifications. Reindex the finite sigma type by Fin of its cardinality, keeping
every stratum scheme. The compositor transports each component model to its composite
immersion. The encoding comparison converts this stratification back to intrinsic
constructibility. Zero strata are allowed in the fixed-module predicate; its comparison
already supplies a positive intrinsic stratification on the empty scheme. The argument
therefore includes empty partitions, components and strata, and the zero ring. -/
theorem isConstructibleProEtaleModuleSheaf_iff_clopen
    (X : Scheme.{u}) (I : Type v) [Finite I] (Xi : I → Scheme.{u})
    (j : ∀ i, Xi i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : (⋃ i, Set.range (j i)) = Set.univ)
    (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) :
    IsConstructibleProEtaleModuleSheaf X A F ↔
      ∀ i, IsConstructibleProEtaleModuleSheaf (Xi i) A
        (proEtaleConstantModulePullback (j i) A F) := by
  classical
  let D := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let G := (proEtaleModuleRestriction X A).obj F
  rw [proEtaleModuleRestriction_constructible_iff]
  constructor
  · rintro ⟨S, hS⟩ i
    apply (proEtaleModuleRestriction_constructible_iff _ _ _).mpr
    obtain ⟨e⟩ := proEtaleModuleRestriction_pullback (j i) A F
    apply ProEtale.isConstructible_of_iso e.symm
    refine ⟨S.pullback (j i), fun n ↦ ?_⟩
    let a := pullback.fst (S.immersion n) (j i)
    let b := pullback.snd (S.immersion n) (j i)
    have heq : a ≫ S.immersion n = b ≫ j i := pullback.condition
    exact ProEtale.isFiniteLocallyConstant_of_iso
      (((ProEtale.upperStarComp D a (S.immersion n)).app G).symm ≪≫
        eqToIso (congrArg (fun f ↦ (ProEtale.upperStar D f).obj G) heq) ≪≫
        (ProEtale.upperStarComp D b (j i)).app G)
      (fixedFinitePullback a A _ (hS n))
  · intro h
    have hs (i : I) : ProEtale.IsConstructible (ULift.{u + 1, u} A)
        ((ProEtale.upperStar D (j i)).obj G) := by
      obtain ⟨e⟩ := proEtaleModuleRestriction_pullback (j i) A F
      exact ProEtale.isConstructible_of_iso e
        ((proEtaleModuleRestriction_constructible_iff _ _ _).mp (h i))
    choose S hS using hs
    let T (i : I) : FiniteLocallyClosedStratification (Xi i) :=
      { S i with }
    obtain ⟨hi, hl, hc, hd, hu⟩ := clopenStratification_union X I Xi j hdisjoint hcover T
      (fun i ↦ (S i).isConstructible_stratum)
    let J := Σ i, Fin (S i).n
    let : Fintype J := Fintype.ofFinite J
    let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    let m (k : Fin (Fintype.card J)) := (S (e k).1).immersion (e k).2 ≫ j (e k).1
    let U : Stratification X :=
      { n := Fintype.card J
        stratum := fun k ↦ Set.range (m k)
        isLocallyClosed_stratum := fun k ↦ hl (e k)
        isConstructible_stratum := fun k ↦ hc (e k)
        pairwise_disjoint_stratum := fun k l hkl ↦ hd (e.injective.ne hkl)
        iUnion_stratum_eq_univ := by
          change (⋃ k, Set.range ((S (e k).1).immersion (e k).2 ≫ j (e k).1)) = _
          exact (e.surjective.iUnion_comp
            (fun p : J ↦ Set.range ((S p.1).immersion p.2 ≫ j p.1))).trans hu
        domain := fun k ↦ (S (e k).1).domain (e k).2
        immersion := m
        isImmersion := fun k ↦ hi (e k)
        range_immersion := fun _ ↦ rfl }
    refine ⟨U, fun k ↦ ?_⟩
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((ProEtale.upperStarComp D ((S (e k).1).immersion (e k).2) (j (e k).1)).app G).symm
      (hS (e k).1 (e k).2)

end AlgebraicGeometry.Scheme
