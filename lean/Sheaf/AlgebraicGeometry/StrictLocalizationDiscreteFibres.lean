/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.FilteredEtaleFiberStructure
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.StrictHenselization

/-!
# Discrete fibres of strict localization

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV, Proposition 2.1.4,
proof, printed page 210 (blueprint: lem-per-strict-localization-discrete-fibres).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The canonical strict-localization morphism of a Noetherian scheme has discrete
fibres, and its fibre at every generization of its centre is nonempty.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV, Proposition 2.1.4,
proof, printed page 210 (blueprint: lem-per-strict-localization-discrete-fibres).

Proof:
1. Choose a Noetherian affine open `U = Spec A` containing `x`, with prime `p`.
   By `lem-weil-pbc-etale-local-ring-triples`, the strict-localization ring `H` is
   the filtered colimit of the etale residue triples for `A`, `p`, and the separable
   closure of the residue field inside the field of the geometric point. Use the
   small representatives of `def-weil-pbc-strict-henselization-limit`. Cocone
   compatibility identifies the structural map over `U` with `Spec (A → H)`;
   consequently its fibres outside `U` are empty.
2. By `lem-sbc-etale-triples-localized-strict-henselization`, `H` is the strict
   henselization of `A_p`, with its prescribed `A`-algebra map. At the maximal
   ideal of `A_p`, the pair category of `def-sc-ring-strict-henselization` and
   the triple category of `lem-weil-pbc-strict-henselization-triples` are
   isomorphic: a map into the separable closure has prime kernel over the
   maximal ideal and induces its residue-field embedding; conversely compose
   the residue map with the embedding. These operations preserve and invert
   the morphism conditions. Thus their colimits are `A_p`-isomorphic.
   Localization preserves Noetherianity (`lem-weil-pbc-localization-noetherian`),
   and `lem-sc-strict-henselization-noetherian` implies that `H` is Noetherian.
3. For a prime `r` of `A`, `lem-weil-pbc-filtered-etale-fiber-structure` shows
   that every prime of `C = κ(r) ⊗[A] H` is maximal, so its dimension is at most zero.
4. Write `C` as the localization of `H / rH` at the image of `A \ r`.
   The mutually inverse maps send `h/s` to `s⁻¹ ⊗ h` and `a/t ⊗ h` to
   `b(a)h/b(t)`. They respect the fraction and tensor relations and fix the
   generators. Quotients of Noetherian rings are Noetherian by lifting ideals
   and taking images of finite generating sets; localization preserves this
   property by `lem-weil-pbc-localization-noetherian`. Thus `C` is Noetherian,
   including when it is the zero ring.
5. Apply `lem-sc-zero-dim-noetherian-finite-discrete` to `Spec C`.
   Tensor-factor exchange and `lem-weil-pbc-fibre-spec-homeomorphism`
   identify it with the topological fibre of `Spec (A → H)`. This proves
   discreteness over `U`; the empty fibres outside `U` are also discrete.
6. Since `x ∈ closure {y}`, the open `U` contains `y`. Its prime `r` satisfies
   `r ⊆ p`, so `lem-weil-pbc-localization-spectrum-embedding` lifts it to `A_p`.
   The identification in Step 2 and `lem-sc-strict-henselization-faithfully-flat`
   make `A_p → H` faithfully flat. By
   `lem-weil-pbc-faithfully-flat-surjective-spectrum`, a prime of `H` lies
   over this prime of `A_p`. Compatibility with `A → H` puts it in the
   fibre over `y`, also when `y = x`.
-/
theorem strictHenselizationStructuralMap_discrete_fibres
    {X : Scheme.{u}} [IsNoetherian X] (x y : X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : (SpecToEquivOfField Ω X s).1 = x) (hxy : x ∈ closure ({y} : Set X)) :
    (∀ z : X, DiscreteTopology {t : strictHenselizationScheme s |
      strictHenselizationStructuralMap s t = z}) ∧
    Nonempty {t : strictHenselizationScheme s | strictHenselizationStructuralMap s t = y} := by
  sorry

end AlgebraicGeometry.Scheme
