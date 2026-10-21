/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Topology.Constructible

/-! # Finite-clopen constructibility and fixed interval bounds

Source: main-20261015 blueprint, sec-six-functors-basics/sk-def-purity-conv,
def-pur-section-invariant, final invertibility assertion; Stacks Tags 005J and 09YD
(blueprint: lem-pur-clopen-finite-constructibility-bounds).

All restrictions are the published ordinary inverse images with their canonical
constant-section coefficient comparison. The derived functors descend exact termwise
restriction. Stratification comparisons retain the immersed subschemes, not just their images.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The existing positive-level coefficient quotient is finite. This instance only
exposes its recorded finiteness proof for the constructibility predicates.
Source: blueprint def-pur-section-invariant, finite coefficient paragraph
(blueprint: lem-pur-clopen-finite-constructibility-bounds). -/
instance finiteClopenCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- Constructibility and the same prescribed cohomological and Tor intervals are
componentwise on a finite clopen partition. The last two equivalences are required
to induce the actual derived restriction after forgetting full-subcategory membership.
The strata comparisons identify immersions, hence retain the same locally constant
module models and their restricted trivializations.

Source: main-20261015 blueprint, def-pur-section-invariant, final invertibility assertion
(blueprint: lem-pur-clopen-finite-constructibility-bounds).

Proof:
1. A clopen component is retrocompact: its intersection with a quasi-compact open is
closed in that open. Restrict constructible strata by Stacks 005J and base change
open and closed immersions. Conversely compose their immersions with the clopen
inclusion and apply Stacks 09YD. The displayed isomorphisms preserve scheme structures.
2. Restrict a constructibility stratification and its trivializing covers by base change
on the small pro-etale site; the finite module models stay the same.
3. Conversely unite the finitely many component stratifications. Their disjointness
and covering properties give a stratification of X with the original finite models.
4. Use lem-pur-clopen-ringed-module-gluing and
lem-pur-finite-product-derived-tensor-calculus: exact restriction commutes with each
cohomology sheaf and jointly detects zero. Apply the sheaf criterion in every degree.
This detects unbounded constructible cohomology and any fixed cohomological interval.
5. For any degree-zero global module M, restrict K tensor M and use the component
Tor hypotheses and tensor comparison. Joint detection of zero gives global Tor bounds.
6. For the converse, insert an arbitrary degree-zero module from one component,
using zero insertion from lem-pur-clopen-ringed-module-gluing. Restrict its tensor
with K. The result is the component tensor, so every component test is covered.
7. Restrict the unbounded equivalence to bounded constructible and finite-Tor objects.
For finitely many different intervals take their minimum lower and maximum upper
endpoints. Any already common interval is preserved by the fixed-interval clauses.
8. Empty components have zero module and derived categories. An empty index type
forces X empty. Use the empty stratification, or one empty stratum for the positive
stratum convention. The zero module is finite and locally constant; all its cohomology
and all its derived tensors vanish, for every ordered interval. No minimum is needed.
-/
theorem finite_clopen_constructibility_bounds
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    {I : Type w} [Finite I] (Xi : I → Scheme.{u}) (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i)) (Set.range (j i')))
    (hcover : (⋃ i, Set.range (j i)) = Set.univ) :
    (∀ (S : Stratification X) (i : I),
      ∃ (T : Stratification (Xi i)) (e : Fin T.n ≃ Fin S.n),
        ∀ t : Fin T.n, ∃ d : T.domain t ≅ pullback (S.immersion (e t)) (j i),
          d.hom ≫ pullback.snd (S.immersion (e t)) (j i) = T.immersion t) ∧
    (∀ S : ∀ i, Stratification (Xi i),
      ∃ (T : Stratification X) (e : Fin T.n ≃ Σ i, Fin (S i).n),
        ∀ t : Fin T.n,
          ∃ d : T.domain t ≅ (S (e t).1).domain (e t).2,
            d.hom ≫ (S (e t).1).immersion (e t).2 ≫ j (e t).1 = T.immersion t) ∧
    (∀ F : proEtaleRingModules X (proEtaleConstantRing X P.Ring),
      IsConstructibleProEtaleModuleSheaf X P.Ring F ↔
        ∀ i, IsConstructibleProEtaleModuleSheaf (Xi i) P.Ring
          ((proEtaleConstantRingPullback P.Ring (j i)).obj F)) ∧
    (∀ K : proEtaleDerivedCategory X P.Ring,
      (∀ m : ℤ, IsConstructibleProEtaleModuleSheaf X P.Ring
        ((DerivedCategory.homologyFunctor _ m).obj K)) ↔
      ∀ (i : I) (m : ℤ), IsConstructibleProEtaleModuleSheaf (Xi i) P.Ring
        ((DerivedCategory.homologyFunctor _ m).obj
          ((proEtaleConstantRingDerivedPullback P.Ring (j i)).obj K))) ∧
    (∀ (K : proEtaleDerivedCategory X P.Ring) (a b : ℤ), a ≤ b →
      (proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
        ∀ i, proEtaleCohomologicalSupport
          ((proEtaleConstantRingDerivedPullback P.Ring (j i)).obj K) ⊆ Set.Icc a b)) ∧
    (∀ (K : proEtaleDerivedCategory X P.Ring) (a b : ℤ), a ≤ b →
      (HasProEtaleTorAmplitude X P.Ring K a b ↔
        ∀ i, HasProEtaleTorAmplitude (Xi i) P.Ring
          ((proEtaleConstantRingDerivedPullback P.Ring (j i)).obj K) a b)) ∧
    (∃ e : (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos X).FullSubcategory ≌
        (∀ i, (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos (Xi i)).FullSubcategory),
      Nonempty (e.functor ⋙ Functor.pi (fun i ↦
          (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
            P.level P.level_pos (Xi i)).ι) ≅
        (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level P.level_pos X).ι ⋙
          Functor.pi' (fun i ↦ proEtaleConstantRingDerivedPullback P.Ring (j i)))) ∧
    (∃ e : (finiteTorConstructible P.coefficients.l P.extension P.level
        P.level_pos X).FullSubcategory ≌
        (∀ i, (finiteTorConstructible P.coefficients.l P.extension P.level
          P.level_pos (Xi i)).FullSubcategory),
      Nonempty (e.functor ⋙ Functor.pi (fun i ↦
          (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos (Xi i)).ι) ≅
        (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X).ι ⋙
          Functor.pi' (fun i ↦ proEtaleConstantRingDerivedPullback P.Ring (j i)))) ∧
    (∀ (K : proEtaleDerivedCategory X P.Ring), IsZero K →
      ∀ a b : ℤ, a ≤ b →
        proEtaleCohomologicalSupport K ⊆ Set.Icc a b ∧
        HasProEtaleTorAmplitude X P.Ring K a b) := by
  sorry

end WeilConjectures.PurityFiniteSetting
