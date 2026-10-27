/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Ideal.Prime
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Module surjectivity near the image of a field-extension point

Source: Stacks Project, Varieties, Tag 0C4Y, assertion (1), and Morphisms, Tag 0383;
this is their auxiliary module consequence, not a verbatim Stacks statement
(blueprint: lem-sc-module-surjectivity-field-extension-neighbourhood).

For `S = C ⊗[k] K`, the scalar extension of a `C`-module `M` is represented by
`S ⊗[C] M`. Its canonical identification with `M ⊗[k] K` sends
`(c ⊗ₜ λ) ⊗ₜ m` to `(c • m) ⊗ₜ λ`, with inverse `m ⊗ₜ λ ↦ (1 ⊗ₜ λ) ⊗ₜ m`.
Under this identification, `φ.baseChange S` is exactly `φ ⊗ id_K`.
-/

@[expose] public section

universe u v w x y

namespace LinearMap

open scoped TensorProduct

/-- Surjectivity on a principal open after field extension descends to a principal
neighbourhood of the image prime. Source: Stacks Project, Varieties, Tag 0C4Y (1),
and Morphisms, Tag 0383, auxiliary module consequence
(blueprint: lem-sc-module-surjectivity-field-extension-neighbourhood).

Proof:
1. Put S = C tensor_k K. By `lem-weil-pbc-fibre-product-affine-spectra`, the contraction
   Spec S → Spec C is a base change of Spec K → Spec k. It is open by
   `lem-sc-scheme-over-field-universally-open`. Thus the image of D(v) is an open
   neighbourhood of the contraction of P. The basic-open basis from
   `lem-weil-pbc-spec-localization-away-basic-open` gives c outside that contraction
   with D(c) contained in this image.
2. For q in D(c), choose Q in D(v) above q. The field-extension map C → S is flat
   by `lem-weil-pbc-field-extension-base-change-faithfully-flat`. The induced local
   map C_q → S_Q is flat by `lem-weil-pbc-flat-local-ring-maps`, hence faithfully
   flat by `lem-pc-local-flat-faithful-flat-reflects-surjective`.
3. For every C-module E, identify (E tensor_k K)_Q with E_q tensor_{C_q} S_Q.
   The map sends (e tensor λ)/t to (e/1) tensor ((1 tensor λ)/t); its inverse sends
   (e/s) tensor b to b (e tensor 1)/(s tensor 1). Contraction of Q ensures that
   the denominators are invertible. The fraction relations and tensor balancing
   show that the formulas are well defined and inverse. They commute with φ.
4. Surjectivity at v gives surjectivity at Q: represent a preimage of y/1 at v by
   z/v^a. Clearing denominators gives v^b (v^a y - φ_K(z)) = 0. Since v is outside
   Q, the fraction z/(v^a t) maps to y/t at Q. Faithfully flat reflection from
   `lem-pc-local-flat-faithful-flat-reflects-surjective` gives surjectivity at q.
5. Let T be the cokernel of φ. Exact localization
   (`lem-weil-pbc-localization-module-exact`) gives T_q = 0 for every q in D(c).
   A maximal ideal n of C_c contracts to such a q by
   `lem-weil-pbc-spec-localization-away-basic-open`. The identification
   (T_c)_n ≅ T_q sends (e/c^a)/(r/c^b) to c^b e/(c^a r), with inverse
   e/s ↦ (e/1)/(s/1). Apply
   `lem-weil-pbc-linear-map-bijective-at-maximal-localizations` to 0 → T_c to get
   T_c = 0. Exact localization then gives surjectivity of φ_c. No finite
   generation is needed in any step. -/
theorem exists_localizedMap_away_surjective_of_fieldExtension
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {C : Type w} [CommRing C] [Algebra k C]
    {M : Type x} {N : Type y} [AddCommGroup M] [AddCommGroup N]
    [Module C M] [Module C N] (φ : M →ₗ[C] N)
    (v : C ⊗[k] K) (P : Ideal (C ⊗[k] K)) [P.IsPrime] (hv : v ∉ P)
    (hφ : Function.Surjective
      (LocalizedModule.map (Submonoid.powers v) (φ.baseChange (C ⊗[k] K)))) :
    ∃ c : C, algebraMap C (C ⊗[k] K) c ∉ P ∧
      Function.Surjective (LocalizedModule.map (Submonoid.powers c) φ) := by
  sorry

end LinearMap
