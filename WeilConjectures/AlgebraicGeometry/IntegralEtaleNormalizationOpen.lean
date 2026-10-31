/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-!
# An integral étale scheme embeds in its finite generic normalization

An integral separated étale scheme `E` over a normal integral Noetherian scheme `X` embeds as an
open subscheme of the normalization of `X` in the finite separable generic-fibre field `L`,
provided that normalization is finite. No quasi-compactness of `E` or `f` is assumed. The
generic-fibre equation in the statement records the specified identification with `Spec L`
using the canonical map from `Spec L` to the normalization.

Source: Stacks Project, more-morphisms.tex, Tag 05K0
(lemma-quasi-finite-separated-pass-through-finite), applied on affine source and target
neighbourhoods; morphisms.tex, Tag 0AB1 (lemma-finite-birational-over-normal); separated
uniqueness as in Tag 01RH (blueprint: lem-sf-integral-etale-normalization-open).

## Main statements

* `AlgebraicGeometry.integral_etale_normalization_open`
-/
/-- **An integral étale scheme embeds in its finite generic normalization.** Let `X` be a
normal integral Noetherian scheme with function field `K`, `f : E ⟶ X` separated étale with
`E` normal integral, `L / K` finite separable with `e : E ×_X Spec K ≅ Spec L` over `K`, and
assume `ν : X^L ⟶ X` finite. Then there is an open immersion `j : E ⟶ X^L` with `j ≫ ν = f`
whose generic-fibre map is `e` followed by the canonical map `Spec L ⟶ X^L ×_X Spec K`.

Source: Stacks Project, Tags 05K0, 0AB1 and 01RH
(blueprint: lem-sf-integral-etale-normalization-open).

Proof (from the node):
1. Let `ξ` be the generic point of `E`; the nonempty generic fibre gives a point over `η`, so
   `f ξ = η`. Choose affine charts `V = Spec B ⊆ E`, `U = Spec A ⊆ X`, `f V ⊆ U`, of an affine
   étale presentation (`def-weil-etale-morphism`). By
   `lem-sc-integral-function-field-affine-fraction`, `A, B` are domains, `K = Frac A`, `ξ ∈ V`.
   `V ×_X Spec K` is the whole one-point fibre `Spec L`; by
   `lem-weil-pbc-fibre-product-affine-spectra` its ring is `B ⊗_A K = S⁻¹B`, `S = A \ {0}`.
   So `A → B` is injective and `B ⊆ S⁻¹B = L = Frac B`, compatibly with restriction.
2. `lem-weil-pbc-affine-open-stalk-localization` identifies `B_𝔭` with the normal stalks of
   `E`; `lem-weil-pbc-normal-domain-of-local-normal` makes `B` integrally closed in `L`.
3. `g : V ⟶ U` is étale and separated (`def-weil-proper-morphism`), finite type and
   quasi-finite (`lem-weil-pbc-etale-ring-map-quasi-finite`, `pqf-def-quasifinite`).
   `pqf-lem-normalization-open` gives an open immersion `V ⟶ R_V` into the relative
   normalization, which is `Spec C'_U`, `C'_U` the integral closure of `A` in `B`
   (`lem-weil-pbc-relative-normalization` (iii)). Only the affine `g` is quasi-compact.
4. With `C_U` the integral closure of `A` in `L`, step 2 gives `C_U = C'_U` inside `L`. By
   `def-fin-normalization-extension`, `ν⁻¹ U = Spec C_U`, so step 3 gives an open immersion
   `j_V : V ⟶ ν⁻¹ U` over `X` with ring map `C_U ⊆ B`.
5. For each nonempty affine `U`, `C_U` is a domain with fraction field `L`
   (`lem-weil-pbc-integral-closure-finite-extension-normal`), and the generic points of the
   charts agree, so `X^L` is integral (`def-pc-integral-scheme`) with function field `L`, and
   each `j_V` sends `ξ` to its generic point inducing the identity of `L`.
6. The `j_V` agree on overlaps: on affine `W ⊆ V ∩ V'` over `H ⊆ U ∩ U'` both pull `c ∈ C_H`
   back to `c`, by injectivity of germs into `L`
   (`lem-sc-integral-function-field-affine-fraction`) and `def-weil-affine-spectrum`; they
   glue to `j : E ⟶ X^L` over `X`.
7. On `O = j_V(V) ∩ j_{V'}(V')` the two inverses `O ⟶ E` agree after the scheme-theoretically
   dominant `Spec L ⟶ O`; `lemma-nagata-ext-scheme-theoretically-dominant-separated` with the
   separated `f` makes them equal, so `j` is injective.
8. The inverses glue, so `j` is an open immersion (`def-weil-open-immersion`) and `j ≫ ν = f`.
   Clearing denominators gives `S⁻¹C_U = L`, so `X^L ×_X Spec K = Spec L`, and the generic-fibre
   map of `j` is the given identification (`lem-weil-pbc-fibre-product-affine-spectra`).
-/
theorem integral_etale_normalization_open
    {X E : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    (hX : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (f : E ⟶ X) [IsSeparated f] [Etale f] [IsIntegral E]
    (hE : ∀ x : E,
      IsDomain (E.presheaf.stalk x) ∧ IsIntegrallyClosed (E.presheaf.stalk x))
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L]
    (e : pullback f X.fromSpecFunctionField ≅ Spec (.of L))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) =
      pullback.snd f X.fromSpecFunctionField)
    [IsFinite (X.fromNormalizationIn L)] :
    ∃ (j : E ⟶ X.normalizationIn L) (hj : j ≫ X.fromNormalizationIn L = f),
      IsOpenImmersion j ∧
      (pullback.map f X.fromSpecFunctionField (X.fromNormalizationIn L)
        X.fromSpecFunctionField j (𝟙 _) (𝟙 _) (by simp [hj]) (by simp)) =
        e.hom ≫ pullback.lift
          ((X.fromSpecOfAlgebraFunctionField L).toNormalization)
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))) (by
            rw [Scheme.Hom.toNormalization_fromNormalization]) := by
  sorry

end AlgebraicGeometry
