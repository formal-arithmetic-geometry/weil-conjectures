module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Gluing quasi-affine principal neighbourhoods of a quasi-compact subset

Source: Raynaud, *Un critère d'effectivité de descente*, Lemma 3.7,
printed p. 14, equivalence (i)--(ii)
(blueprint: lem-sfb-quasiaffine-principal-neighbourhood-criterion).

## Main statements

* `quasiAffinePrincipalNeighbourhoodCriterion` states the equivalence between a
  quasi-affine open neighbourhood of a quasi-compact subset and the corresponding
  principal-neighbourhood condition.
-/

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact subset of a scheme has a quasi-affine open neighbourhood exactly when
all its points lie in quasi-affine principal opens on quasi-separated neighbourhoods of the
whole subset.

Source: Raynaud, *Un critère d'effectivité de descente*, Lemma 3.7, printed p. 14,
equivalence (i)--(ii) (blueprint: lem-sfb-quasiaffine-principal-neighbourhood-criterion).

Proof:
1. If E is empty, take the empty affine scheme; the principal-neighbourhood condition
   is vacuous. In general, a quasi-affine U is quasi-separated by
   lem-trf-quasi-affine-canonical-affine-embedding, so V = U and g = 1 prove necessity.
2. Conversely, choose finitely many principal opens covering E by its quasi-compactness.
   Intersect their ambient neighbourhoods V_i. Using lem-weil-pbc-affine-opens-basis
   and lem-weil-pbc-affine-scheme-qcqs, take a finite union W of affine opens inside
   this intersection containing E. Then W is quasi-compact.
3. Restrict g_i to f_i on W and put B_i = W_{f_i}. These opens cover E. By
   lem-pqf-finite-affine-cover-qc-open, W has a finite affine open cover. On each affine
   chart its intersection with B_i is affine by
   lem-weil-pbc-affine-open-section-vanishing-prime, hence quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs. Thus B_i is quasi-compact.
4. Each B_i is an open subscheme of the quasi-affine (V_i)_{g_i}, so its composite
   embedding into an affine scheme, together with its quasi-compactness, makes B_i
   quasi-affine. Their finite union U is quasi-compact and contains E.
5. U is an open subscheme of a quasi-separated V_i, hence is quasi-separated. The
   restrictions h_i of f_i to U satisfy U_{h_i} = B_i, by equality of germs. Apply
   lem-sfb-qcqs-quasiaffine-basic-open-cover to obtain that U is quasi-affine.
-/
theorem quasiAffinePrincipalNeighbourhoodCriterion {Y : Scheme.{u}} {E : Set Y}
    (hE : IsCompact E) :
    (∃ U : Y.Opens, E ⊆ U ∧ U.toScheme.IsQuasiAffine) ↔
      (∀ e : E, ∃ V : Y.Opens, E ⊆ V ∧ QuasiSeparatedSpace V.toScheme ∧
        ∃ g : Γ(Y, V), (Y.basicOpen g).toScheme.IsQuasiAffine ∧
          (e : Y) ∈ Y.basicOpen g) := by
  sorry

end AlgebraicGeometry.Scheme
