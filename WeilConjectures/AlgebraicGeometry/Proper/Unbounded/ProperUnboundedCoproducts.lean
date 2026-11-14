/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedWindow
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedCoproductComparison
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTruncationCoproducts
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientIndDerivedSums
import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedWindowBounded
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-!
# Proper direct image preserves arbitrary small direct sums

Source: blueprint main-20261015, chap-Construction-of-f,
sk-lem-proper-unbounded-window-ii, statement and its bounded/general proof details
(blueprint: sk-lem-proper-unbounded-window-ii).

The standing setting of sk-def-sfb-dc-setting is inherited through the proper window
and heart-bound lemmas: separated finite-type schemes over k, with positive characteristic
different from ell, and morphisms over k.

Coproducts are given by colimit cofans, including their existence. The comparison is
induced by the images of the source coprojections. Membership of both coproducts in
Dic makes this precisely the comparison in that full subcategory. No choice of an
ambient coproduct or additional coproduct-existence hypothesis is imposed on callers.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The two conclusions of the node: total module pushforward preserves Dic, and its
canonical coproduct comparison is invertible in Dic. IndCons is the small filtered-colimit
closure of the recorded finite constant-model constructible modules. The cofans specify
ambient coproducts; their cohomology conditions put them in the full subcategories Dic.
The last arrow has component `Rp_*(c.inj i)` on the i-th summand, by `IsColimit.fac`.
Any other coproducts yield the same assertion by their unique compatible isomorphisms.
Source: blueprint sk-lem-proper-unbounded-window-ii, statement and proof steps 1 and 6
(blueprint: sk-lem-proper-unbounded-window-ii). -/
def ProperUnboundedCoproductAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  (∀ K : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) →
    ∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj K))) ∧
  (∀ (I : Type (u + 1))
      (K : I → DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
    (∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
    ∃ (c : Cofan K) (_ : IsColimit c)
      (c' : Cofan (fun i ↦ (CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj (K i)))
      (hc' : IsColimit c'),
      (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj c.pt)) ∧
      (∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj c'.pt)) ∧
      IsIso (hc'.desc (Cofan.mk
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar Λ p).rightDerivedFunctor.map (c.inj i)))))

/-- Proper direct image preserves arbitrary small sums of unbounded ind-constructible
complexes in the standing scheme setting, with finite-extension condensed coefficients
and a uniform geometric-fibre bound.
Source: blueprint main-20261015, lemma-proper-direct-image-unbounded-complexes--3, statement and
proof (blueprint: lemma-proper-direct-image-unbounded-complexes--3).

Proof plan, the six steps of the DAG:
1. corollary-ambient-ind-derived puts S = sum K_i in Dic. The proper window lemma puts
   Rp_*K_i and Rp_*S in Dic. Define the comparison by its coprojection equations.
2. For q in Z put r = q-2d-1, A_i = tau_le(q) K_i, W_i = tau_ge(r) A_i, and similarly
   A_S and W_S. corollary-ambient-ind-derived and proposition-open-direct-image-preserves-finite
   keep these in Dic. The maps sum A_i -> A_S and sum W_i -> W_S come from truncated coprojections.
   Their cohomologies are the cohomology-of-sums isomorphisms in the retained ranges,
   and zero-to-zero elsewhere. lemma-proper-direct-image-unbounded-complexes--3 makes both
   maps invertible. Naturality makes them compatible with K <- A -> W.
3. lemma-proper-direct-image-unbounded-complexes--3 applies to W_i in the common interval [r,q].
   Its comparison is invertible, and step 2 identifies its target with Rp_*W_S.
4. Apply H^q Rp_* to the canonical zigzags. The squares comparing sums commute on
   each coprojection by functoriality. lemma-proper-direct-image-unbounded-complexes makes the two
   cohomology arrows invertible for each K_i and for S, with the same bound d.
5. Conjugating the bounded-family comparison along these invertible arrows gives
   invertibility of H^q of the original comparison. The cohomology-of-sums formula
   identifies its source. The cohomological isomorphism criterion gives an ambient iso.
6. corollary-ambient-ind-derived gives closure of Dic under ambient sums. The ambient
   universal property restricts to the full subcategory, and the ambient inverse is
   a morphism there. This gives exactly the canonical comparison in Dic. -/
theorem properUnbounded_preservesCoproducts
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    ProperUnboundedCoproductAssertions (Profinite.continuousMapRingObj.{u} E) p := by
  have hdim : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ (d : ℤ) := by
    intro y n hn
    have hnd : (n : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := hn.trans (hd y)
    exact_mod_cast hnd
  have hw := properUnboundedWindow ℓ E k p₀ hp₀ hpℓ X Y p d hdim
  refine ⟨?_, ?_⟩
  · intro K hK n
    exact (hw K hK).1 n
  · have sx := indConstructibleDerived_sums_and_truncations ℓ E k p₀ hp₀ hpℓ X
    have sy := indConstructibleDerived_sums_and_truncations ℓ E k p₀ hp₀ hpℓ Y
    apply properUnbounded_coproductComparison (Profinite.continuousMapRingObj E) p d hw
      sx.2.1 sy.2.1 sx.2.2.1
    · intro I D c hc q
      let B := pulledBackModuleObjects (Profinite.continuousMapRingObj E) Y
      let : HasColimitsOfShape (Discrete I) B :=
        IsGrothendieckAbelian.hasColimitsOfShape_discrete B I
      let : HasExactColimitsOfShape (Discrete I) B :=
        IsGrothendieckAbelian.hasExactColimitsOfShape_discrete B I
      exact ⟨isColimitOfPreserves (DerivedCategory.homologyFunctor B q) hc⟩
    · intro I K c hc q r
      have := derivedTruncation_preservesCoproducts (Profinite.continuousMapRingObj E) X I q r
      exact ⟨isColimitOfPreserves _ hc⟩
    · intro a b I M hM hb
      obtain ⟨c, hc, c', hc', hi⟩ := properUnboundedWindowBounded ℓ E p a b I M hM hb
      refine ⟨c, hc, ?_⟩
      have := hi
      exact ⟨(Cofan.isColimitMapCoconeEquiv _ M c).2 hc'.ofPointIso⟩

/-- The arbitrary-sum theorem for the condensed algebraic closure, whose sections have
values in a finite subextension, in the standing scheme setting with the same fibre bound.
Source: blueprint main-20261015, lemma-proper-direct-image-unbounded-complexes--3, both coefficient
cases (blueprint: lemma-proper-direct-image-unbounded-complexes--3).

Proof plan: as in the six DAG steps, form the ambient sum using corollary-ambient-ind-derived
and use lemma-proper-direct-image-unbounded-complexes for its image and the images of all summands.
Fix q and r=q-2d-1. By proposition-open-direct-image-preserves-finite and the cohomology-of-sums
formula, the sums of tau_le(q) K_i and tau_ge(r) tau_le(q) K_i are their corresponding truncations
of S: the canonical maps induce cohomology isomorphisms and hence are invertible by
lemma-proper-direct-image-unbounded-complexes--3. They commute with both truncation arrows.
Apply lemma-proper-direct-image-unbounded-complexes--3 to the window family in [r,q]. Its comparison
is invertible. Functoriality on each coprojection makes the cohomology comparison squares
for K <- A -> W commute. The proper window lemma makes every vertical arrow invertible,
both for the family and for S. Conjugate to obtain invertibility of H^q of the original
comparison, and use the cohomological isomorphism criterion in every degree. Finally
ambient-sum closure from corollary-ambient-ind-derived and fullness put both coproducts,
the comparison and its inverse in Dic. -/
theorem properUnbounded_preservesCoproducts_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    ProperUnboundedCoproductAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p := by
  have hdim : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ (d : ℤ) := by
    intro y n hn
    have hnd : (n : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := hn.trans (hd y)
    exact_mod_cast hnd
  have hw := properUnboundedWindow_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hdim
  refine ⟨?_, ?_⟩
  · intro K hK n
    exact (hw K hK).1 n
  · have sx := indConstructibleDerived_sums_and_truncations_padicAlgCl ℓ k p₀ hp₀ hpℓ X
    have sy := indConstructibleDerived_sums_and_truncations_padicAlgCl ℓ k p₀ hp₀ hpℓ Y
    apply properUnbounded_coproductComparison (Profinite.padicAlgClRingObj ℓ) p d hw
      sx.2.1 sy.2.1 sx.2.2.1
    · intro I D c hc q
      let B := pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) Y
      let : HasColimitsOfShape (Discrete I) B :=
        IsGrothendieckAbelian.hasColimitsOfShape_discrete B I
      let : HasExactColimitsOfShape (Discrete I) B :=
        IsGrothendieckAbelian.hasExactColimitsOfShape_discrete B I
      exact ⟨isColimitOfPreserves (DerivedCategory.homologyFunctor B q) hc⟩
    · intro I K c hc q r
      have := derivedTruncation_preservesCoproducts (Profinite.padicAlgClRingObj ℓ) X I q r
      exact ⟨isColimitOfPreserves _ hc⟩
    · intro a b I M hM hb
      obtain ⟨c, hc, c', hc', hi⟩ := properUnboundedWindowBounded_padicAlgCl ℓ p a b I M hM hb
      refine ⟨c, hc, ?_⟩
      have := hi
      exact ⟨(Cofan.isColimitMapCoconeEquiv _ M c).2 hc'.ofPointIso⟩

end AlgebraicGeometry.ProEtale
