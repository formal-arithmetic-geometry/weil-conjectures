/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.GroupoidSourcePullbackTranslation
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import WeilConjectures.AlgebraicGeometry.FiniteAffineFibreSections
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.IsFiniteLocallyFreeOfDegreeOfEtaleCover

/-!
# Invariant closed rank filtration of a finite groupoid

Source: Stacks Project, More on Groupoids, Tag 0AB9, lemma-finite-stratify
(blueprint: lem-sfb-finite-groupoid-invariant-rank-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite groupoid admits an invariant descending closed rank filtration.
The closed subscheme `Z n` is represented by the ideal sheaf `J n`: `J 0 = ⊥`
means `Z 0 = U`, and `Monotone J` gives the closed inclusions `Z (n + 1) ⊆ Z n`.
The last clause restricts the source to the open complement of `Z (n + 1)` in `Z n`.
Equality of pulled-back ideal sheaves expresses scheme-theoretic invariance.
Source: Stacks Project, More on Groupoids, Tag 0AB9, lemma-finite-stratify
(blueprint: lem-sfb-finite-groupoid-invariant-rank-filtration).

Proof plan, following the node's six steps:
1. For `E = s_* O_R`, let `J n = Fit_n(E)` using
   `lem-trf-fitting-ideal-sheaf-pullback`. Laplace expansion makes these ideals
   increasing. By `lem-weil-pbc-quasi-coherent-finite-type-affine`, locally `E` has
   finitely many generators, say `m`, and `J m` is the unit ideal. The intersection
   of the supports is therefore empty; no global generator bound is required.
2. The identity section splits each affine structure map `A → B`. For any square
   matrix of kernel rows of a generating presentation of `B`, the adjugate shows
   that its determinant kills all generators, hence `1`. Injectivity of `A → B`
   makes every such determinant zero. Thus `Fit_0(E) = 0`, including on empty opens,
   by the affine formula in `lem-trf-fitting-ideal-sheaf-pullback`.
3. Use `lem-a1-groupoid-source-pullback-translation` to identify
   `R ×[s,U,t] R` and `R ×[s,U,s] R` over their second factors. The algebra clause
   of `lem-weil-pbc-affine-pushforward-base-change` then identifies `t^*E` and `s^*E`.
4. Apply `lem-trf-fitting-ideal-sheaf-pullback` to these two pullbacks. Transporting
   generating presentations through this module isomorphism preserves their kernels
   and minors. Hence their ideal sheaves agree, giving invariance as closed subschemes.
5. On `W_r = U ∖ |Z_r|`, `lem-trf-fitting-ideal-generate-locally` gives at most `r`
   generators. Its preceding Fitting ideal cuts out `D_r` in `W_r` and has zero image
   on `D_r`, by `lem-trf-fitting-ideal-sheaf-pullback`. Apply
   `lem-sfb-bounded-generators-fitting-pullback-criterion` to obtain rank `r` there.
6. `lem-weil-pbc-affine-morphism-permanence` gives affineness of the restricted source;
   `lem-weil-pbc-affine-pushforward-base-change` identifies its algebra with that
   rank-`r` module. Trivialize on affine opens and apply
   `lem-weil-pbc-finite-free-algebra-spectrum` and `lem-pc-finite-affine-fibre-sections`
   to get finite local freeness and degree `r`. Open immersions are etale by
   `lem-weil-pbc-open-immersion-etale`; use
   `lem-weil-pbc-finite-locally-free-degree-etale-descent` to conclude, also for empty
   strata with their empty cover.
-/
theorem groupoid_exists_rank_filtration
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) (hG : IsGroupoidScheme s t e i c)
    [IsFinite s] [IsFinite t] :
    ∃ J : ℕ → U.IdealSheafData,
      J 0 = ⊥ ∧ Monotone J ∧
      (⋂ n : ℕ, ((J n).support : Set U)) = ∅ ∧
      (∀ n : ℕ, (J n).comap s = (J n).comap t) ∧
      ∀ n : ℕ,
        (pullback.snd s
          (Scheme.Opens.ι ((J n).subschemeι ⁻¹ᵁ (J (n + 1)).support.compl) ≫
            (J n).subschemeι)).IsFiniteLocallyFreeOfDegree (n + 1) := by
  sorry

end AlgebraicGeometry
