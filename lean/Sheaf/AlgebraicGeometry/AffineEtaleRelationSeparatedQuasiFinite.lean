/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Separated locally quasi-finite morphisms of an affine étale relation

Source: Stacks Project, Spaces, Tag 0265, the opening two proof paragraphs and the
first representability step (blueprint: lem-trf-affine-etale-relation-separated-lqf).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For an étale equivalence relation on an affine `S`-scheme, both projections and
its monomorphism into the relative square are separated and locally quasi-finite.
Here local quasi-finiteness includes the finite-type requirement of Stacks Tag 01TD.
The schemes and morphisms over `S` are bundled in `Over S`; `hrel` states the
relation condition on every `S`-scheme's points. The relation map is the canonical
`pullback.lift` into `U.left ×[S] U.left`. No separatedness of `S` or quasi-compactness
of `R.left` is assumed.

Source: Stacks Project, Spaces, Tag 0265, opening two proof paragraphs and the first
representability step (blueprint: lem-trf-affine-etale-relation-separated-lqf).

Proof:
1. Put `V = U ×[S] U` and let `P` be the absolute product `U × U` over `Spec ℤ`.
   The affine fibre-product formula (lem-weil-pbc-fibre-product-affine-spectra)
   makes `P` affine. The map `V → P` is monic: equality after it gives equality of
   both projections, hence equality by the pullback universal property
   (def-pc-fibre-product). Its composite `q : R → P` with the given monic `j` is monic.
2. For either `j` or `q`, monicity makes the two projections of its self-pullback
   equal. Its diagonal is inverse to the first projection, by the pullback universal
   property. Thus its diagonal is an isomorphism, hence a closed and open immersion
   (def-weil-closed-immersion, def-weil-open-immersion). Both maps are separated,
   and the diagonal of `j` is open (def-weil-proper-morphism).
3. The separated map `q` to the affine `P` makes `R` absolutely separated by
   lem-sc-separated-over-affine-scheme-separated. Factor its absolute structure map
   through `s` and through `t`. Separated cancellation, clause (b) of
   lem-weil-pbc-separated-cancellation, makes both projections separated.
4. Étaleness makes both projections unramified (def-weil-etale-morphism and
   def-weil-unramified-morphism). Apply lem-weil-pbc-unramified-quasi-finite-at-points
   to obtain their local quasi-finiteness. It also makes `s` locally of finite type.
5. Since `j` followed by the first projection is `s`, clause (f) of
   lem-weil-pbc-proper-fp-permanence makes `j` locally of finite type. Its open
   diagonal from step 2 makes it unramified. Apply
   lem-weil-pbc-unramified-quasi-finite-at-points again and combine all six conclusions. -/
theorem affine_etale_relation_separated_locally_quasi_finite
    {S : Scheme.{u}} (R U : Over S) [IsAffine U.left] (s t : R ⟶ U)
    [Mono (pullback.lift s.left t.left (s.w.trans t.w.symm))]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Etale s.left] [Etale t.left] :
    (IsSeparated s.left ∧ Scheme.Hom.IsLocallyQuasiFinite s.left) ∧
    (IsSeparated t.left ∧ Scheme.Hom.IsLocallyQuasiFinite t.left) ∧
    (IsSeparated (pullback.lift s.left t.left (s.w.trans t.w.symm)) ∧
      Scheme.Hom.IsLocallyQuasiFinite (pullback.lift s.left t.left (s.w.trans t.w.symm))) := by
  sorry

end AlgebraicGeometry
