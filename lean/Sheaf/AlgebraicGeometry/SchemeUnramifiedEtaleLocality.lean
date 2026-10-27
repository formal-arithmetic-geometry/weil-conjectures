/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-! # Étale source-and-target locality of unramified scheme morphisms

Source: Stacks Project, Descent, Tag 04R3, item (9), and Definition 04QZ;
source locality is Tag 03YV, target locality is Tag 02VM, combined in Tag 04R2
(blueprint: lem-sfb-scheme-unramified-etale-locality).

The three explicit clauses cover precomposition, base change, and pointwise compatible
étale charts. Empty schemes are allowed, with no quasi-compactness or separation condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem formallyUnramified_of_faithfullyFlat_formallySmooth
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FormallySmooth A B]
    [Algebra.FormallyUnramified R B] : Algebra.FormallyUnramified R A := by
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B z).mp hz
    rw [Subsingleton.elim w 0, map_zero]
  have : Subsingleton (TensorProduct A B (KaehlerDifferential R A)) := hinj.subsingleton
  exact ⟨(Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := A) (B := B) (KaehlerDifferential R A)).subsingleton⟩

private theorem formallyUnramified_stalk_of_etale_source
    {U X Y : Scheme.{u}} (a : U ⟶ X) (f : X ⟶ Y)
    [Etale a] [FormallyUnramified (a ≫ f)] (u : U) :
    (f.stalkMap (a u)).hom.FormallyUnramified := by
  have hflat := Flat.stalkMap a u
  have hsmooth : (a.stalkMap u).hom.FormallySmooth :=
    a.smoothLocus_eq_top.ge (show u ∈ (⊤ : U.Opens) from trivial)
  have hunram := FormallyUnramified.stalkMap (a ≫ f) u
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at hunram
  algebraize [(f.stalkMap (a u)).hom, (a.stalkMap u).hom,
    (a.stalkMap u).hom.comp (f.stalkMap (a u)).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (a u)) (U.presheaf.stalk u)) :=
    inferInstanceAs (IsLocalHom (a.stalkMap u).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (a u)) (U.presheaf.stalk u) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Algebra.FormallyUnramified
      (Y.presheaf.stalk (f (a u))) (U.presheaf.stalk u) := hunram
  exact formallyUnramified_of_faithfullyFlat_formallySmooth
    (Y.presheaf.stalk (f (a u))) (X.presheaf.stalk (a u)) (U.presheaf.stalk u)

/-- Unramified morphisms are étale local on source-and-target, in the three explicit
clauses of Stacks Project, Descent, Definition 04QZ and Remark 04R3, item (9).
(blueprint: lem-sfb-scheme-unramified-etale-locality).

Proof, following the accepted DAG split:
1. For the first clause, an étale map is unramified by def-weil-etale-morphism.
   Compose it with the given unramified map using
   lem-sfb-scheme-unramified-composition-cancellation. The second clause is clause (1) of
   lem-weil-pbc-unramified-base-change-open, which permits arbitrary base change.
2. In the forward direction of the third clause, take U = X, V = Y, both chart maps
   identities, h = f, and the point u = x. Identities are étale, including on empty schemes.
3. Conversely, unramifiedness of each chart h includes local finite type by
   def-weil-unramified-morphism. Pointwise locality for local finite type in
   lem-sfb-scheme-etale-source-target-properties implies that f is locally of finite type.
   Since b is étale, hence unramified, the composition-cancellation node makes
   g = a ≫ f = h ≫ b unramified for every chosen chart.
4. Fix x and a chart point u above it, and use the actual stalk tower
   R = O(Y,f(x)) → A = O(X,x) → B = O(U,u).
   Functoriality of stalk maps (def-weil-locally-ringed-space-morphism) identifies R → B
   with the stalk map of g. By lem-weil-pbc-unramified-formally-unramified and
   lem-sfb-formally-unramified-stalk-map it is formally unramified. Therefore Ω(B/R) = 0
   by lem-weil-pbc-formally-unramified-ring-iff-kahler-zero. The map A → B is flat and
   local by def-weil-etale-morphism and def-weil-flat-morphism, so it is faithfully flat
   by lem-weil-pbc-flat-local-hom-faithfully-flat.
5. The map a is smooth by lem-weil-pbc-etale-smooth-zero-dimensional-fibres, so A → B
   is formally smooth by lem-sfb-smooth-stalk-formally-smooth. Apply
   lem-weil-pbc-formally-smooth-differentials-injective to obtain an injection
   B ⊗[A] Ω(A/R) → Ω(B/R) = 0. Thus its source is zero. By
   lem-weil-pbc-faithfully-flat-universally-injective and the tensor-factor interchange
   from def-weil-pbc-module-tensor-product, Ω(A/R) embeds into this zero module.
   Hence Ω(A/R) = 0, and the same differentials criterion makes R → A formally unramified.
6. Apply lem-trf-formally-unramified-from-all-stalks at every x. Together with the
   local finite type from step 3, lem-weil-pbc-lft-formally-unramified-unramified implies
   that f is unramified. For empty X both pointwise criteria are vacuous, so the same
   argument works without choosing any chart. No finite subcover, quasi-compactness,
   separation, or Noetherian assumption is used. -/
theorem scheme_unramified_etale_locality :
    (∀ (U X Y : Scheme.{u}) (e : U ⟶ X) (f : X ⟶ Y),
      Etale e → IsUnramified f → IsUnramified (e ≫ f)) ∧
    (∀ (X Y V : Scheme.{u}) (f : X ⟶ Y) (b : V ⟶ Y),
      IsUnramified f → Etale b → IsUnramified (pullback.snd f b)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsUnramified f ↔ ∀ x : X,
        ∃ (U V : Scheme.{u}) (a : U ⟶ X) (b : V ⟶ Y) (u : U) (h : U ⟶ V),
          Etale a ∧ Etale b ∧ a.base u = x ∧ a ≫ f = h ≫ b ∧ IsUnramified h) := by
  have hcomp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
      (ha : IsUnramified a) (hb : IsUnramified b) : IsUnramified (a ≫ b) := by
    have := ha.1
    have := ha.2
    have := hb.1
    have := hb.2
    have : FormallyUnramified (a ≫ b) :=
      MorphismProperty.comp_mem _ a b inferInstance inferInstance
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨?_, ?_, ?_⟩
  · intro U X Y e f he hf
    have := he
    exact hcomp e f ⟨inferInstance, inferInstance⟩ hf
  · intro X Y V f b hf _
    have := hf.1
    have := hf.2
    have : FormallyUnramified (pullback.snd f b) :=
      MorphismProperty.pullback_snd f b inferInstance
    exact ⟨inferInstance, inferInstance⟩
  · intro X Y f
    constructor
    · intro hf x
      exact ⟨X, Y, 𝟙 X, 𝟙 Y, x, f, inferInstance, inferInstance, rfl,
        by simp, hf⟩
    · intro hcharts
      have : LocallyOfFiniteType f := by
        apply (scheme_etale_source_target_properties.{u, u} (@LocallyOfFiniteType)
          (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).1.2.2 X Y f |>.mpr
        intro x
        obtain ⟨U, V, a, b, u, h, ha, hb, hx, hcomm, hh⟩ := hcharts x
        exact ⟨U, V, a, b, h, u, ha, hb, hx, hcomm, hh.1⟩
      have : FormallyUnramified f := by
        apply HasRingHomProperty.of_stalkMap (P := @FormallyUnramified)
          RingHom.FormallyUnramified.ofLocalizationPrime
        intro x
        obtain ⟨U, V, a, b, u, h, ha, hb, hx, hcomm, hh⟩ := hcharts x
        have := ha
        have := hb
        have hg := hcomp h b hh ⟨inferInstance, inferInstance⟩
        rw [← hcomm] at hg
        have := hg.2
        rw [← hx]
        exact formallyUnramified_stalk_of_etale_source a f u
      exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
