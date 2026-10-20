/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.FiniteSchemeCohomologyTensor
import Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison

/-! # Euler characteristic of modules with zero-dimensional support

Source: Stacks Project, Varieties, Tag 0AYT, parts (3)--(5), with rank one
(blueprint: lem-pc-chi-zero-dim-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module with zero-dimensional support on a proper scheme over a field has
no positive cohomology. Its Euler characteristic is the dimension of its global sections.
Tensoring with an invertible module preserves coherence, support and Euler characteristic.
Source: Stacks Project, Varieties, Tag 0AYT, parts (3)--(5), with rank one
(blueprint: lem-pc-chi-zero-dim-support).

Proof:
1. Properness implies finite type (`def-weil-proper-morphism`). Coherence
   (`pqf-def-coherent`) makes the support closed. The dimension hypothesis and
   `lem-sc-dim0-finite` make it a finite set of closed points.
2. By `lem-pc-zero-support-finite-scheme`, write the module as the pushforward of a
   coherent module on a finite affine closed subscheme Spec A. The projection formula
   identifies its tensor with an invertible module with the corresponding pushforward
   on Spec A; coherence and support are preserved.
3. The algebra A is finite dimensional. By `lem-pc-finite-scheme-cohomology-tensor`,
   positive cohomology vanishes, global sections are finite dimensional, and tensoring
   with the restricted invertible module preserves their dimension. Transport these
   facts using the cohomology identifications of `lem-pc-zero-support-finite-scheme`.
4. In the sum of `def-pc-euler-characteristic`, only degree zero survives, and degree-zero
   cohomology is global sections. The dimension equality from step 3 gives tensor
   invariance of the Euler characteristic. -/
theorem eulerChar_zero_dim_support (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hdim : topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ≤ 0) :
    (∀ i : ℕ, 0 < i → Subsingleton (F.H i)) ∧
    F.eulerChar k = (Module.finrank k (F.H 0) : ℤ) ∧
    Module.finrank k (F.H 0) =
      @Module.finrank k Γ(F, ⊤) _ _ (Module.compHom Γ(F, ⊤) (globalSectionsRingHom k (X := X))) ∧
    (∀ (N : X.Modules) [N.IsInvertible],
      RingedSpace.IsCoherent X.toRingedSpace (F ⊗ N : X.Modules) ∧
      {x : X | ¬ Subsingleton ((F ⊗ N).presheaf.stalk x)} =
        {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (F ⊗ N).eulerChar k = F.eulerChar k) := by
  have key (N : X.Modules) [N.IsInvertible] :
      (∀ q : ℕ, 0 < q → Subsingleton (F.H q)) ∧
      RingedSpace.IsCoherent X.toRingedSpace (F ⊗ N : X.Modules) ∧
      {x : X | ¬ Subsingleton ((F ⊗ N).presheaf.stalk x)} =
        {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (F ⊗ N).eulerChar k = F.eulerChar k := by
    obtain ⟨A, hA, hAlg, hfd, i, hi, G, hover, _, hG, ⟨e⟩, ⟨t⟩, hFt, hs, hc, _⟩ :=
      coherent_zero_support_finite_scheme (k := k) X F hF hdim N
    let := hA
    let := hAlg
    let := hfd
    let := hi
    let : (Spec (.of A)).Over (Spec (.of k)) :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩
    have : i.IsOver (Spec (.of k)) := ⟨hover⟩
    have : IsNoetherianRing A := IsNoetherianRing.of_finite k A
    have : G.IsQuasicoherent :=
      ((isCoherent_iff_isQuasicoherent_and_isFiniteType _ G).mp hG).1
    let L := (tensorPullback i).obj N
    let c : tensorPullback i ≅ Scheme.Modules.pullback i :=
      (Classical.choose (exists_tensorPullbackAdjunction i)).leftAdjointUniq
        (pullbackPushforwardAdjunction i)
    have : L.IsInvertible := IsInvertible.of_iso (c.app N).symm
    have : (G ⊗ L).IsQuasicoherent := isQuasicoherent_tensorObj G L
    obtain ⟨hv, _, _, _, _, _, he⟩ := finiteSchemeCohomologyTensor (k := k) G L hG inferInstance
    refine ⟨?_, hFt, hs, ?_⟩
    · intro q hq
      obtain ⟨a⟩ := hc q
      have hz := (ModuleCat.restrictScalars i.appTop.hom).map_isZero (hv q hq)
      have hzF := hz.of_iso a
      have := ModuleCat.subsingleton_of_isZero hzF
      obtain ⟨b, _⟩ := exists_moduleCohomology_source_comparison X q
      exact (b F).symm.injective.subsingleton
    · calc
        (F ⊗ N).eulerChar k = ((pushforward i).obj (G ⊗ L)).eulerChar k :=
          eulerChar_congr k t
        _ = (G ⊗ L).eulerChar k := eulerChar_pushforward_of_isAffineHom k i _
        _ = G.eulerChar k := he
        _ = ((pushforward i).obj G).eulerChar k :=
          (eulerChar_pushforward_of_isAffineHom k i G).symm
        _ = F.eulerChar k := (eulerChar_congr k e).symm
  have hv := (key (𝟙_ X.Modules)).1
  refine ⟨hv, ?_, ?_, fun N _ ↦ (key N).2⟩
  · rw [eulerChar_eq_sum_range_of_subsingleton k F (D := 0) hv]
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, finrankH]
  · let := Module.compHom Γ(F, ⊤) (globalSectionsRingHom k (X := X))
    let e : F.H 0 ≃ₗ[k] Γ(F, ⊤) :=
      { (H.zeroLinearEquiv F).toAddEquiv with
        map_smul' c x := (H.zeroLinearEquiv F).map_smul (globalSectionsRingHom k c) x }
    exact e.finrank_eq

end AlgebraicGeometry.Scheme.Modules
