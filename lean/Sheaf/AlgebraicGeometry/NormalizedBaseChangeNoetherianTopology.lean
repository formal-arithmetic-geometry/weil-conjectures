/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial

import Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum

/-!
# Noetherianity of a normalized base change

Source: Orgogozo, *Modifications et cycles proches sur une base générale*, final sentences
of Lemma 8.3.2, p. 18 (blueprint: lem-trf-normalized-base-change-noetherian-topology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- The normalization of the reduced closed subscheme on `closure {s}`.
Source: Orgogozo, Lemma 8.3.2, proof, printed p. 18; the reduced closure is constructed
by the vanishing ideal and normalized in its function field (`def-sc-normalization`).
(blueprint: lem-trf-normalized-base-change-noetherian-topology) -/
noncomputable def normalizedClosure {S : Scheme.{u}} (s : S) : Scheme.{u} := by
  let J : S.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨closure ({s} : Set S), isClosed_closure⟩
  letI : IsIntegral J.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  exact J.subscheme.normalization

/-- The canonical map from the normalized reduced closure to `S`.
Source: Orgogozo, Lemma 8.3.2, proof, printed p. 18. This is the normalization map
followed by the closed immersion of the reduced point closure into `S`.
(blueprint: lem-trf-normalized-base-change-noetherian-topology) -/
noncomputable def normalizedClosureMap {S : Scheme.{u}} (s : S) :
    normalizedClosure s ⟶ S := by
  let J : S.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨closure ({s} : Set S), isClosed_closure⟩
  letI : IsIntegral J.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  change J.subscheme.normalization ⟶ S
  exact J.subscheme.fromNormalization ≫ J.subschemeι

/-- The finite-type base change to the normalized reduced closure of a point has
Noetherian underlying topology, equivalently every nonempty family of closed subsets has
an inclusion-minimal member.

Source: Orgogozo, *Modifications et cycles proches sur une base générale*, proof of
Lemma 8.3.2, printed p. 18, finite-type alternative; Heinzer, *Minimal primes of ideals
and integral ring extensions*, Theorem 2 and Corollary, pp. 371–372; Ohm–Pendleton,
*Rings with Noetherian spectrum*, Theorem 2.5 and Corollary 2.6.

1. By `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, the base has Noetherian
   topology. Local Noetherianity (`pqf-def-locnoeth`) and quasi-compactness give a finite
   affine cover `Spec Rᵢ` with `Rᵢ` Noetherian. Its nonempty intersections with the
   reduced closure are `Spec Aᵢ`, where `Aᵢ = Rᵢ / pᵢ` is a Noetherian domain:
   `def-weil-closed-immersion` gives the quotient, `def-pc-integral-scheme` makes its
   ideal prime, and images of generators of inverse-image ideals prove Noetherianity.
2. The point is generic in its reduced closure. By
   `lem-sc-integral-function-field-affine-fraction`, each `Aᵢ` has fraction field the
   generic stalk. The closed-immersion stalk map is surjective onto this field, so its
   kernel is the ambient stalk's maximal ideal; `def-weil-residue-field` identifies the
   field with κ(s). By `def-sc-normalization`, the normalization above `Spec Aᵢ` is
   `Spec Bᵢ`, with `Bᵢ` the integral closure in that field. The map is integral by
   `lem-weil-pbc-spec-integral-ring-map-integral`. Apply
   `lem-trf-integral-extension-noetherian-spectrum` to the degree-one field extension:
   each `Spec Bᵢ` has Noetherian topology. No finiteness or Noetherian-ring claim is used.
3. By `def-weil-finite-type-morphism`, each inverse image of `Spec Rᵢ` has a finite
   affine cover `Spec Dᵢⱼ` of finite type over `Rᵢ`. First base change to the reduced
   closure, obtaining `Cᵢⱼ = Dᵢⱼ ⊗[Rᵢ] Aᵢ`, and then to its normalization. The tensor
   universal property (`def-pc-fibre-product`) identifies the resulting charts with
   `Spec (Cᵢⱼ ⊗[Aᵢ] Bᵢ)`. Images of the finitely many algebra generators show these
   are finite type over `Bᵢ`; there are finitely many such charts and they cover.
4. Apply `lem-sfb-finite-type-noetherian-spectrum` to these chart algebras. A descending
   chain of closed subsets stabilizes on each chart; the maximum of the finitely many
   stabilization indices proves that it stabilizes globally.
5. Taking complements identifies descending closed chains with ascending open chains.
   Equivalently, the inclusion order on closed subsets is well-founded, so every
   nonempty collection has a minimal member. This is `TopologicalSpace.NoetherianSpace`.
(blueprint: lem-trf-normalized-base-change-noetherian-topology)
-/
theorem noetherianSpace_normalized_baseChange
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    [IsLocallyNoetherian S] [CompactSpace S]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    TopologicalSpace.NoetherianSpace
      (CategoryTheory.Limits.pullback (C := Scheme) f (normalizedClosureMap s)) := by
  sorry

end AlgebraicGeometry
