/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Stratifying flat quasi-finite separated morphisms by degree

Source: Stacks Project, More on Morphisms, Tag 07RZ
(blueprint: lem-weil-pbc-flat-fp-qf-stratification).

We index the closed filtration starting at zero: `Z 0` denotes the paper's `Z_{-1}`,
so the degree-`r` stratum is `Z (r + 1) \ Z r`, written out in place.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat, locally finitely presented, separated quasi-finite morphism admits a closed
filtration whose successive differences universally characterize finite local freeness
of each degree, and these strata meet every quasi-compact open in a quasi-compact subset.
Source: Stacks Project, More on Morphisms, Tag 07RZ
(blueprint: lem-weil-pbc-flat-fp-qf-stratification).

Proof (the node's ten steps):
1. Restrict to an affine open `W` of the target using
`lem-weil-pbc-open-preimage-fibre-product`. Flatness and local finite presentation survive
base change (`lem-weil-pbc-flat-morphism-base-change`,
`lem-weil-pbc-qcqs-morphism-permanence`). Separatedness and finite type survive too
(`lem-pod-separated-finite-type-base-change`), and isolation in the fibres survives
(`lem-weil-pbc-isolated-fibre-point-base-change`). Thus the restriction is quasi-finite
(`pqf-def-quasifinite`) and locally quasi-finite (`pqf-lem-qf-locqf-qc`), with quasi-compact
source (`def-weil-finite-type-morphism`). Its fibre degrees have a bound by
`lem-weil-pbc-lqf-qc-source-bounded-fibres`.
2. Apply `lem-weil-pbc-flat-fp-lqf-bounded-stratification` over `W`. Extend its closed
filtration by `W` beyond the bound; the remaining strata are empty.
3. Define the global degree-`r` set by the fibre degree over each residue field
(`def-weil-residue-field`, `def-pc-finite-locally-free`). The universal property tested
on `Spec κ(s)` identifies this set on every affine open with that open's stratum;
use `lem-weil-pbc-morphism-factors-through-open-subscheme` and pullback pasting
(`def-pc-fibre-product`).
4. The affine-local strata are disjoint and cover, so the global strata do too. Their
partial unions are closed on every affine open, hence closed globally (`def-pc-scheme`).
5. Finite local freeness of fixed degree is local on the target: finiteness by
`lem-weil-pbc-finite-local-on-target`, flatness by the stalk condition
(`def-weil-flat-morphism`), local finite presentation by its affine neighbourhood condition
(`def-sbc-locally-finite-presentation`), and degree by equality of the residue-field fibres.
6. For any `g : T ⟶ S`, cover `T` by the inverse images of the affine opens of `S`.
Pullback pasting identifies the restrictions of its base change with the base changes in
step 2 (`lem-weil-pbc-open-preimage-fibre-product`, `def-pc-fibre-product`). Step 5 and the
local universal properties give the global universal property.
7. Put `U_r = S \ Z_r`. On an affine `W' = Spec A` inside `U_{r-1}`, the stratum is closed,
of the form `V(I)`. The map `Spec (A/I) ⟶ S` has image in it, so step 6 makes the base
change finite locally free of degree `r` (`def-weil-affine-spectrum`,
`lem-weil-pbc-closed-immersion-affine-cover-criterion`, `def-weil-closed-immersion`).
8. Express `A/I` as the filtered colimit of the quotients by finitely generated subideals
(`lem-weil-pbc-spec-colimit-limit`). Descend the finite locally free base change to one
such quotient using `lem-weil-pbc-descend-finite-locally-free`, with the qcqs hypothesis
from `lem-weil-pbc-qcqs-over-affine`. The universal property gives equality of the two
vanishing sets. Hence `U_r ∩ W'` is a finite union of basic opens and is quasi-compact
(`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`).
9. Inductively, `U_{r-1} ∩ W` is quasi-compact for affine `W`; cover it by finitely many
affine `W'` as in step 8 (`def-pc-scheme`). Their intersections with `U_r` cover
`U_r ∩ W`, so that set is quasi-compact too.
10. Each stratum intersected with an affine open is closed inside the corresponding
quasi-compact `U_{r-1} ∩ W`. A quasi-compact open is a finite union of affine opens
(`def-pc-scheme`), giving the asserted quasi-compactness for every such open. -/
theorem exists_closed_stratification_of_flat_quasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated f] (hf : f.IsQuasiFinite) :
    ∃ Z : ℕ → Set S,
      Z 0 = ∅ ∧ (∀ n : ℕ, IsClosed (Z n)) ∧ Monotone Z ∧
      Pairwise (fun r t : ℕ => Disjoint (Z (r + 1) \ Z r) (Z (t + 1) \ Z t)) ∧
      (⋃ r : ℕ, Z (r + 1) \ Z r) = Set.univ ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S) (r : ℕ),
        (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔ Set.range g ⊆ Z (r + 1) \ Z r) ∧
      (∀ (r : ℕ) (W : S.Opens), IsCompact (W : Set S) →
        IsCompact ((Z (r + 1) \ Z r) ∩ (W : Set S))) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
