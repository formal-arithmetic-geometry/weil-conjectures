/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# Existence and uniqueness of K-injective resolutions on the small étale site

Source: blueprint `sec-curve-estimates/sk-prop-cd`,
proposition `prop-weil-pbc-kinjective-resolutions-exist`; Stacks Project, Tags 079P and 070I
(blueprint: prop-weil-pbc-kinjective-resolutions-exist).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CochainComplex

/-- Every complex of étale `R`-module sheaves has a K-injective resolution, functorially up
 to chain homotopy. Any two such resolutions are homotopy equivalent. Bounded-below
 complexes of injectives are K-injective.

Source: blueprint `sec-curve-estimates/sk-prop-cd`, proposition on K-injective resolutions;
Stacks Project, Tags 079P and 070I
(blueprint: prop-weil-pbc-kinjective-resolutions-exist).

Proof:
1. The module-sheaf category is Grothendieck abelian by
   `lem-weil-pbc-module-sheaves-grothendieck-abelian`. Apply
   `lem-weil-pbc-kinjective-functorial-existence` (Stacks 079P). The resulting replacement
   functor and natural quasi-isomorphism give the object and map assignments below.
   Strict functor laws imply their homotopy versions. Homotopic input maps induce homotopic
   output maps by the bijection on homotopy classes into a K-injective target (070I).
2. For two resolutions `s : K ⟶ I`, `t : K ⟶ J`, both images in the derived category are
   invertible. Lift their comparison isomorphism and its inverse using
   `lem-weil-pbc-kinjective-hom-derived`. Injectivity on homotopy classes says the composites
   are homotopic to the identities, giving a chain-homotopy equivalence.
   The comparison carries `s` to `t` up to homotopy: both composites lift the same derived
   morphism `Qt`, so injectivity on homotopy classes gives their equality.
3. Apply `lem-weil-pbc-bounded-below-injectives-kinjective`, i.e. Mathlib's
   `CochainComplex.isKInjective_of_injective`, to the given lower bound and injective terms. -/
theorem etale_kinjective_resolutions_exist (T : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    (∃ (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ →
          CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
       (s : ∀ K, K ⟶ I K)
       (φ : ∀ {K L}, (K ⟶ L) → (I K ⟶ I L)),
       (∀ K, IsKInjectiveResolution T R (s K)) ∧
       (∀ K, Nonempty (Homotopy (φ (𝟙 K)) (𝟙 (I K)))) ∧
       (∀ {K L M} (f : K ⟶ L) (g : L ⟶ M),
         Nonempty (Homotopy (φ (f ≫ g)) (φ f ≫ φ g))) ∧
       (∀ {K L} (f g : K ⟶ L),
         Nonempty (Homotopy f g) → Nonempty (Homotopy (φ f) (φ g))) ∧
       (∀ {K L} (f : K ⟶ L), Nonempty (Homotopy (s K ≫ φ f) (f ≫ s L)))) ∧
    (∀ (K I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
       (s : K ⟶ I) (t : K ⟶ J),
       IsKInjectiveResolution T R s → IsKInjectiveResolution T R t →
       Nonempty (HomotopyEquiv I J)) ∧
    (∀ (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
       (d : ℤ), I.IsStrictlyGE d → (∀ n : ℤ, Injective (I.X n)) → I.IsKInjective) := by
  classical
  let C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)
  let F := kInjectiveResolutionFunctor.{u + 1} C
  let η := toKInjectiveResolution.{u + 1} C
  let q := HomotopyCategory.quotient C (.up ℤ)
  let := HasDerivedCategory.standard C
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨F.obj, η.app, fun f ↦ F.map f, ?_, ?_, ?_, ?_, ?_⟩
    · intro K
      exact ⟨(monoQuasiIso_toKInjectiveResolution_app C K).2, inferInstance⟩
    · intro K
      exact ⟨Homotopy.ofEq (F.map_id K)⟩
    · intro K L M f g
      exact ⟨Homotopy.ofEq (F.map_comp f g)⟩
    · intro K L f g h
      apply Nonempty.intro
      apply HomotopyCategory.homotopyOfEq
      apply (IsKInjective.Qh_map_bijective (q.obj (F.obj K)) (F.obj L)).injective
      have : QuasiIso (η.app K) := (monoQuasiIso_toKInjectiveResolution_app C K).2
      apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app (F.obj L))).1
      rw [DerivedCategory.quotientCompQhIso_hom_naturality,
        DerivedCategory.quotientCompQhIso_hom_naturality]
      congr 1
      apply (cancel_epi (DerivedCategory.Q.map (η.app K))).1
      rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
        ← η.naturality f, ← η.naturality g]
      simpa only [Functor.id_map, Functor.map_comp] using
        congrArg (fun a ↦ a ≫ DerivedCategory.Q.map (η.app L))
          (DerivedCategory.Q_map_eq_of_homotopy C h.some)
    · intro K L f
      exact ⟨Homotopy.ofEq (η.naturality f).symm⟩
  · intro K I J s t hs ht
    have : QuasiIso s := hs.1
    have : QuasiIso t := ht.1
    have : I.IsKInjective := hs.2
    have : J.IsKInjective := ht.2
    obtain ⟨e⟩ := IsKInjective.nonempty_iso_quotient_obj s t
    exact ⟨HomotopyCategory.homotopyEquivOfIso e⟩
  · intro I d hGE hInj
    have : I.IsStrictlyGE d := hGE
    have : ∀ n : ℤ, Injective (I.X n) := hInj
    exact isKInjective_of_injective I d

end CochainComplex
