/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Sheaf.TraceFormula.CompleteAlgebraDevissage
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation
import Sheaf.RingTheory.AffineGeometricallyIntegralProjective
import Sheaf.TraceFormula.LocalUIFlatCokernel
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Projectivity after base localization from a complete dévissage

Source: Stacks Project, More on Flatness, Tag 05IB,
lemma-complete-devissage-flat-finitely-presented-module, projectivity conclusion
(blueprint: lem-trf-complete-algebra-devissage-projective-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

/-- A finitely presented module over a finitely presented algebra, flat over the base,
becomes projective after inverting a base element outside the given prime if it admits
complete dévissage there. The localized module is the canonical fraction module `m/f^k`,
equivalently `N ⊗[R] Localization.Away f`. The scalar tower records restriction along
`R → S`; no finiteness of `N` as an `R`-module is required.

Source: Stacks Project, Tag 05IB, projectivity conclusion
(blueprint: lem-trf-complete-algebra-devissage-projective-localization).

Proof plan:
1. Induct on the length of a complete dévissage, quantifying over every base ring and
   prime so that induction remains applicable after localization. At length zero `N = 0`;
   take `f = 1`. At positive length the first module is `R`-linearly isomorphic to `N`.
2. Each `B_i` is smooth over `R`, hence finitely presented and flat, by
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine, def-weil-pbc-smooth-ring-map, and
   lem-weil-pbc-smooth-ring-map-flat. Its fibres are geometrically reduced by
   sbc-lem-smooth-geometrically-reduced and geometrically irreducible by the dévissage,
   hence geometrically integral (def-pc-integral-scheme).
3. The surjection `S → A_1` is finite and finitely presented. Transfer finite presentation
   of `M_1` to `A_1` using lem-trf-finite-extension-module-finite-presentation. Composition
   makes `A_1` finitely presented over `R`. If `A_1 = R[x]/(F)` and `B_1 = R[y]/(G)`,
   represent the images of `y` by polynomials `P(x)`. Then
   `A_1 = B_1[x]/(F, y - P(x))`, since `G(P(x))` already vanishes modulo `F`.
   Thus `B_1 → A_1` is finitely presented and finite; the same transfer makes `M_1`
   finitely presented over `B_1`.
4. Apply lem-trf-generic-basis-base-open-universal-injectivity to the first map.
   The dévissage supplies its generic-fibre isomorphism and the prime `r B_1`.
   This prime contracts to `r`, since the nonzero fibre algebra receives an injective
   map from the residue field. Obtain `f_1 ∉ r` making the map universally injective.
5. Localize the whole dévissage at `f_1`. Smoothness persists by base change
   (lem-pc-proper-base-change), and the fibres are unchanged at corresponding primes.
   Finite algebra generators and finite presentations localize. Localization is exact:
   a numerator whose image vanishes can be multiplied by a power of `f_1` to lie in
   the original kernel. Thus all surjections, cokernels and specified isomorphisms
   persist. The residue-field condition is unchanged since `f_1 ∉ r`. Flatness of the
   localized module follows from the tensor identification over the localized base.
6. Let `C` be the cokernel of the first map. Universal injectivity and right exactness
   of tensor give a universally exact sequence from the finite free `B_1`-module through
   `M_1` onto `C`. By lem-trf-local-ui-flat-cokernel, `C` is flat over the current base.
   Append lifts of the finitely many images of the free basis to a presentation matrix
   of `M_1`; this presents `C` over `B_1`. The remaining dévissage is a complete
   dévissage of `C/B_1/R`; if the original length is one, `C = 0`.
7. Induction on that tail gives `h` outside the current prime such that `C_h` is
   projective; when `C = 0`, take `h = 1`. Exactness persists under this localization.
8. By lem-trf-local-fibres-integral-projective, the localized `B_1` is projective over
   the localized base. Its finite free module is therefore projective, including rank
   zero: lift a map on each summand along a surjection and add the finitely many lifts.
9. Lift the identity of `C_h` through the quotient map using its projectivity. The
   resulting section splits the sequence, identifying the localization of `M_1` with
   the direct sum of that finite free module and `C_h`; hence it is projective.
   Write `h = a/f_1^k`. Since `h` is outside the extended prime, `a ∉ r`.
   Set `f = f_1*a ∉ r`. The successive localization and `R_f` both invert exactly
   `f_1` and `a`, so the localization universal property identifies their rings.
   The maps `m/(f_1^i*h^j) ↦ f_1^(k*j)*m/(f_1^i*a^j)` identify the modules.
   Transport the obtained projectivity to `N_f`.
-/
theorem exists_projective_localization_of_completeDevissage
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (N : Type v) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    (r : Ideal R) [r.IsPrime]
    (hdev : Nonempty (CompleteAlgebraDevissage R S r N)) :
    ∃ f : R, f ∉ r ∧
      Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) N) := by
  sorry

end AlgebraicGeometry
