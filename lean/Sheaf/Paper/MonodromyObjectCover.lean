/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.Paper.MonodromySingleObjectCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-! # An etale cover with monodromy object models

Source: Bhatt--Scholze, Proposition 6.8.4 and Corollary 6.8.5.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

private theorem common_cover (S : Scheme.{u}) (A : Type (u + 1)) [Finite A]
    (I : A → Type (u + 1)) (Y : ∀ a, I a → S.Etale)
    (hY : ∀ a, S.smallEtaleTopology.CoversTop (Y a)) :
    ∃ (K : Type (u + 1)) (Z : K → S.Etale)
      (i : ∀ (_k : K) (a : A), I a)
      (_f : ∀ (k : K) (a : A), Z k ⟶ Y a (i k a)),
      S.smallEtaleTopology.CoversTop Z := by
  classical
  let := Fintype.ofFinite A
  let K := Σ U : S.Etale, ∀ a : A, Σ i : I a, U ⟶ Y a i
  let Z : K → S.Etale := Sigma.fst
  refine ⟨K, Z, (fun k a ↦ (k.2 a).1), (fun k a ↦ (k.2 a).2), ?_⟩
  intro X
  have H (s : Finset A) : (s.inf (fun a ↦ Sieve.ofObjects (Y a) X)) ∈
      S.smallEtaleTopology X := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simpa [Finset.inf_insert, ha] using
        S.smallEtaleTopology.intersection_covering (hY a X) ih
  apply S.smallEtaleTopology.superset_covering ?_ (H Finset.univ)
  intro W f hf
  have hh : ∀ a : A, ∃ i : I a, Nonempty (W ⟶ Y a i) := by
    intro a
    have hle : Finset.univ.inf (fun a ↦ Sieve.ofObjects (Y a) X) ≤
        Sieve.ofObjects (Y a) X := Finset.inf_le (Finset.mem_univ a)
    exact hle f hf
  choose i hi using hh
  let q : K := ⟨W, fun a ↦ ⟨i a, Classical.choice (hi a)⟩⟩
  exact ⟨q, ⟨𝟙 _⟩⟩

private theorem restriction_congr (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {S T : Scheme.{u}} (f g : T ⟶ S)
    [Etale f] [Etale g] (h : f = g) :
    PresheafOfModules.pushforward
        (ProEtale.lisseEtaleCoefficientIdentificationSized l E f) =
      PresheafOfModules.pushforward
        (ProEtale.lisseEtaleCoefficientIdentificationSized l E g) := by
  subst g
  rfl

/-- A finite family of lisse objects has an etale cover on which its restrictions
to every pointed connected open chart are in the normalized monodromy essential image.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Corollary 6.8.5, pp. 59--60.
(blueprint: lem-sfb-monodromy-object-cover)

Proof: for each object choose an etale-local integral lattice by Proposition 6.8.4(6).
Successively refine the finitely many covers by fibre products, retaining previous lattices
by restriction. For an empty family start with the identity cover. Restriction to any open
chart preserves integral finite local freeness and its rationalization isomorphism, since
slice coefficients are the same continuous functions. On a connected pointed qcqs
Noetherian chart reduce each integral lattice to its normalized tower. Finite monodromy
identifies its fibres with compatible finite free continuous representations of one rank.
Recursively lift bases to identify their limit with a finite free module over the complete
valuation ring. The limit action is continuous, being so on every finite projection.
Tensor the representation with E; its finite-dimensional action remains continuous.
Its limit lattice is stable and spans. Finite-monodromy full faithfulness identifies its
finite-level local systems with the original reductions, compatibly with all transitions.
The limit universal properties, including constant integral scalars, identify the original
integral module with the normalization of this lattice. Rationalizing and composing with
the chosen lattice isomorphism gives the displayed object isomorphism. This holds for any
normalized realization because its normalization is prescribed on every invariant lattice.
The coefficient-universe lift uses exactly the same construction, with ULift on values;
finite extension coefficients have the same spectral topology. No arrow needs an integral
model, and no simultaneous preservation of the chosen lattices by arrows is asserted. -/
theorem exists_sf_monodromy_object_cover (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (S : Scheme.{u})
    (A : Type (u + 1)) [Finite A] (L : A → SfRationalModules l E S)
    (hL : ∀ a : A, (L a).IsFiniteLocallyFree) :
    ∃ (I : Type (u + 1)) (Y : I → S.Etale), S.smallEtaleTopology.CoversTop Y ∧
      ∀ (i : I) (T : Scheme.{u}) (g : T ⟶ (Y i).left) [IsOpenImmersion g]
        (p : SfMonodromyPoint T) (R : SfMonodromyRealization l E p),
        ∃ V : A → SfContinuousRepresentations l E p,
          ∀ a : A, Nonempty ((R.functor.obj (V a)).val ≅
            (PresheafOfModules.pushforward
              (ProEtale.lisseEtaleCoefficientIdentificationSized l E (g ≫ (Y i).hom))).obj
                (L a).val) := by
  classical
  have H := fun a : A ↦ exists_sf_monodromy_single_object_cover l E S (L a) (hL a)
  choose I Y hY hmodel using H
  obtain ⟨K, Z, j, q, hZ⟩ := common_cover S A I Y hY
  refine ⟨K, Z, hZ, ?_⟩
  intro k T g _ p R
  have hm (a : A) : ∃ V : SfContinuousRepresentations l E p,
      Nonempty ((R.functor.obj V).val ≅
        (PresheafOfModules.pushforward
          (ProEtale.lisseEtaleCoefficientIdentificationSized l E (g ≫ (Z k).hom))).obj
            (L a).val) := by
    have Hk := hmodel a (j k a) T (g ≫ (q k a).left) p R
    have hcomp : (g ≫ (q k a).left) ≫ (Y a (j k a)).hom = g ≫ (Z k).hom := by
      have hq : (q k a).left ≫ (Y a (j k a)).hom = (Z k).hom := (q k a).w
      exact (Category.assoc _ _ _).trans (congrArg (g ≫ ·) hq)
    change ∃ V : SfContinuousRepresentations l E p,
      Nonempty ((R.functor.obj V).val ≅
        (PresheafOfModules.pushforward
          (ProEtale.lisseEtaleCoefficientIdentificationSized l E
            ((g ≫ (q k a).left) ≫ (Y a (j k a)).hom))).obj (L a).val) at Hk
    rw [restriction_congr l E _ _ hcomp] at Hk
    exact Hk
  choose V hV using hm
  exact ⟨V, hV⟩

end AlgebraicGeometry.Scheme
