/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.Equalizer
import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType

/-! # Generic spreading of fibre-assassin containment

Source: Stacks Project, More on Morphisms, Tag 05KP, `lemma-good-case`
(blueprint: lem-sfb-generic-fibre-assassin-containment-spreads).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Containment of the associated points of the generic fibre in an open spreads to a
nonempty open of an irreducible base. The open need not be quasi-compact, and the base
need not be Noetherian.
Source: Stacks Project, More on Morphisms, Tag 05KP, `lemma-good-case`
(blueprint: lem-sfb-generic-fibre-assassin-containment-spreads).

Proof:
1. Use [lem-trf-generic-flat-reduced-base-model] to replace the base by a reduced integral
   affine neighbourhood of its generic point, homeomorphic onto a nonempty base open.
   Pullback preserves quasi-coherence and finite type by
   [lem-weil-pbc-module-pullback-quasi-coherent] and
   [lem-weil-pbc-module-pullback-finite-type]. Transfer containment in both directions by
   [lem-sfb-fibre-assassin-containment-base-change]. Write the base as Spec A, with A a
   domain and fraction field K. No flatness of the original morphism is assumed.
2. Finite type [def-weil-finite-type-morphism] gives a finite affine cover of X.
   Associatedness is stalk-local [def-trf-relative-assassin], so it suffices to handle
   each chart and intersect the resulting nonempty base opens. Every such open contains
   the generic point. For the empty cover take the entire base.
3. On X = Spec B, write F as the sheaf of the finite module N = Gamma(X,F), using
   [lem-weil-pbc-affine-finite-type-generating-sections] and
   [lem-weil-pbc-affine-tilde-gamma-adjunction]. The fibre module is N tensor_A kappa(y)
   by [lem-weil-pbc-module-pullback-affine-sections]. Its ring B tensor_A kappa(y) is
   Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]. Apply
   [lem-sfb-affine-associated-points-primes] on these fibres.
4. Principal opens D(g) contained in U cover U by
   [lem-weil-pbc-spec-localization-away-basic-open]. The generic fibre U_K is compact
   by [lem-sfb-noetherian-space-compact-subsets]. Choose finitely many such g_j whose
   generic principal opens cover U_K. The list can be empty; U itself need not be compact.
5. The map mu : N -> N^m, n |-> (g_j n)_j, is injective over K: each associated prime
   of N_K avoids some g_j. A vector killed by every g_j vanishes at every associated
   prime, hence vanishes by [lem-weil-pbc-module-injects-localizations-associated-primes].
6. Its cokernel C is finite. Apply [lem-trf-algebra-module-simultaneous-generic-flatness]
   to N plus C. After inverting a nonzero h in A, both N_h and C_h are A-flat, since
   direct summands inherit the tensor-injectivity definition [def-weil-pbc-flat-ring-map].
7. Flatness makes N_h torsion-free over the domain A, hence N_h -> N_K is injective
   by the fraction-zero criterion [def-weil-pbc-module-localization]. Consequently mu_h
   is injective, as mu_K is injective.
8. Localizing the cokernel sequence gives 0 -> N_h -> N_h^m -> C_h -> 0. For exactness,
   lift a fraction in C_h to N_h^m; a fraction mapping to zero has a power of h times
   its numerator in mu(N), by [def-weil-pbc-module-localization].
9. For y in D(h), tensor this short exact sequence with kappa(y). Flatness of C_h and
   [lem-weil-pbc-flat-quotient-tensor-injective] preserve injectivity. Since h is a unit
   in kappa(y), this identifies with the multiplication map on the fibre module N_y.
10. An associated prime of N_y is Ann(z) for nonzero z by
    [def-weil-pbc-annihilator-associated-primes]. If it contained every g_j, then mu_y
    would kill z, contradicting injectivity. The associated fibre point therefore lies
    in some D(g_j), hence in U_y, by [lem-sfb-affine-associated-points-primes].
11. Intersect the finitely many opens from the affine charts, all containing the generic
    point. Stalk locality gives containment on X_y. Transfer back from the reduced
    affine base by [lem-sfb-fibre-assassin-containment-base-change] to obtain V. -/
theorem genericFibreAssassinContainment_spreads {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    (hF : F.IsQuasiCoherentFiniteType) (U : X.Opens) [IrreducibleSpace Y]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (hU : associatedPoints ((tensorPullback (f.fiberι η)).obj F) ⊆
      (f.fiberι η) ⁻¹' (U : Set X)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∀ (y : Y), y ∈ V →
        associatedPoints ((tensorPullback (f.fiberι y)).obj F) ⊆
          (f.fiberι y) ⁻¹' (U : Set X) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
