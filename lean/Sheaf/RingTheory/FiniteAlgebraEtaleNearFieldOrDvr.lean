/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.FlatModuleAtPrime
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# An etale base neighbourhood from a field or DVR stalk

Source: Stacks Project, Morphisms, Tag 02GU (2), (4), (5), and Algebra, Tag 00U3;
finite torsion-free modules over a DVR are free (Tag 0AUW).
(blueprint: lem-per-finite-algebra-etale-near-field-or-dvr)
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite torsion-free algebra over a Noetherian domain is etale on a principal base
neighbourhood of a prime whose local ring is a field or DVR, if its fibre has zero
Kahler differentials or is a finite product of finite separable field extensions.

Source: Stacks Project, Tags 02GU (2), (4), (5), 00U3, 0AUW, 0GWM and 01WN.
(blueprint: lem-per-finite-algebra-etale-near-field-or-dvr)

Proof:
1. Localize the finite module at `p`. It remains torsion-free: clearing a fraction
relation gives `u * a * b = 0`, with `u` and `a` nonzero in the domain. It is finite
free over the field, or by `lem-sc-dvr-fg-torsionfree-free` over the DVR.
2. Noetherian finiteness gives finite presentation of the module. Spread its free
localization using `lem-weil-pbc-finitely-presented-free-at-prime-spreads` to find
`g` outside `p` with `B_g` finite free over `R_g`.
3. Localization preserves Noetherianity. Module generators also generate the algebra,
so the Noetherian finite-type algebra is finitely presented. Finite freeness gives
flatness, including on stalks by `lem-pc-affine-flat-module-local-criterion`.
The affine map `Spec B_g` to `Spec R_g` is finite.
4. The residue field at the image of `p` is `p.ResidueField`. The affine fibre-product
formula identifies the fibre algebra with `p.Fiber B`; generators of `B` span it over
the residue field. Either fibre hypothesis makes it etale by
`lem-sc-finite-etale-algebra-criterion` (Tag 00U3).
5. Apply `lem-sbc-flat-fibre-etale-neighbourhoods` to obtain etale source opens covering
the entire fibre. Their union `U` also handles the empty fibre.
6. The finite map is closed by `lem-weil-pbc-finite-closed-map-finite-fibres`. The image
of the closed complement of `U` misses the base point. Refine its open complement
by `D(f)` with `f` outside `p`. The preimage lies in `U`, so its map to `D(f)` is
etale. Since `D(f)` lies in `D(g)`, inverting `f` already inverts `g`; its rings are
exactly `R[1/f]` and `B[1/f]`, with the canonical localized structure map below. -/
theorem exists_etale_away_of_finite_torsionFree_of_field_or_dvr
    (R : Type u) (B : Type v) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B]
    (htorsion : ∀ (r : R) (b : B), r ≠ 0 → r • b = 0 → b = 0)
    (p : Ideal R) [p.IsPrime]
    (hbase : IsField (Localization.AtPrime p) ∨ IsDiscreteValuationRing (Localization.AtPrime p))
    (hfibre : Subsingleton (KaehlerDifferential p.ResidueField (p.Fiber B)) ∨
      ∃ (I : Type (max u v)) (_ : Finite I) (L : I → Type (max u v))
        (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra p.ResidueField (L i))
        (_ : p.Fiber B ≃ₐ[p.ResidueField] Π i, L i),
        ∀ i, Module.Finite p.ResidueField (L i) ∧ Algebra.IsSeparable p.ResidueField (L i)) :
    ∃ f : R, f ∉ p ∧
      (IsLocalization.Away.map (S := Localization.Away f)
        (Q := Localization.Away (algebraMap R B f)) (algebraMap R B) f).Etale := by
  sorry

end Algebra
