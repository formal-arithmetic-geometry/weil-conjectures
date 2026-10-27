/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.QuasiAffine

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Quasi-affine principal neighbourhoods

Source: Raynaud, Un critère d'effectivité de descente, Lemma 3.7, printed p.14
(blueprint: lem-sfb-quasiaffine-principal-neighbourhood-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact subset has a quasi-affine open neighbourhood if and only if each of its
points lies in a quasi-affine basic open on a quasi-separated open neighbourhood of the
whole subset. Here `IsQuasiAffine` includes quasi-compactness. A section over the open
subscheme `V` is written as a section `g : Γ(Y, V)` of the restricted structure sheaf;
`Y.basicOpen g` is its unit-germ locus, regarded as an open of `Y`.

Source: Raynaud, Un critère d'effectivité de descente, Lemma 3.7, printed p.14
(blueprint: lem-sfb-quasiaffine-principal-neighbourhood-criterion).

Proof plan:
1. If `E` is empty, use the empty affine open. Otherwise a quasi-affine neighbourhood `U`
   supplies all the neighbourhoods `V` with section `1`. Quasi-affine schemes are
   quasi-separated by lem-trf-quasi-affine-canonical-affine-embedding.
2. Conversely, compactness of `E` gives finitely many of the basic opens covering it.
   Intersect their ambient neighbourhoods. Inside this intersection choose a finite union
   `W` of affine opens containing `E`, using lem-weil-pbc-affine-opens-basis and
   lem-weil-pbc-affine-scheme-qcqs. Thus `W` is quasi-compact.
3. Restrict the chosen sections to `W`. Their basic opens `B_i` are quasi-compact:
   take a finite affine cover of `W` by lem-pqf-finite-affine-cover-qc-open, and use
   lem-weil-pbc-affine-open-section-vanishing-prime to see that the intersections with
   `B_i` are affine, hence quasi-compact by lem-weil-pbc-affine-scheme-qcqs.
4. Each `B_i` is an open in one of the original quasi-affine basic opens, so its
   quasi-compactness makes it quasi-affine. Their finite union `U` contains `E` and is
   quasi-compact.
5. The open `U` lies in any one of the finitely many quasi-separated neighbourhoods,
   so it is quasi-separated. Restricting the sections again gives quasi-affine basic opens
   covering `U`. Apply lem-sfb-qcqs-quasiaffine-basic-open-cover, represented by
   `IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen`, to conclude.
-/
theorem exists_isQuasiAffine_open_iff (Y : Scheme.{u}) (E : Set Y) (hE : IsCompact E) :
    (∃ U : Y.Opens, E ⊆ (U : Set Y) ∧ U.toScheme.IsQuasiAffine) ↔
      ∀ (e : Y), e ∈ E → ∃ V : Y.Opens, E ⊆ (V : Set Y) ∧
        QuasiSeparatedSpace V.toScheme ∧
        ∃ g : Γ(Y, V), (Y.basicOpen g).toScheme.IsQuasiAffine ∧ e ∈ Y.basicOpen g :=
  sorry

end AlgebraicGeometry.Scheme
