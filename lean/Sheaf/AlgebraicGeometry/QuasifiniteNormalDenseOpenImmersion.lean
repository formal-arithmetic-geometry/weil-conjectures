/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite
import WeilConjectures.AlgebraicGeometry.UnramifiedFibrePointIsolated
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.IntegralBirationalNormalIsomorphism

/-!
# A dense-open criterion for an open immersion into a normal scheme

Source: Stacks Project, More on Morphisms, Tag 02LR; Morphisms, Tags 0CT8 and 0AB1;
Bosch--Lütkebohmert--Raynaud, Néron Models, 2.3 Theorem 2′, as used in 5.3 Lemma 3
(blueprint: lem-sfb-quasifinite-normal-dense-open-immersion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite-type monomorphism from a reduced scheme to a normal Noetherian scheme is an
open immersion if it is an isomorphism over a dense open whose inverse image is dense.

Source: Stacks Project, More on Morphisms, Tag 02LR; Morphisms, Tags 0CT8 and 0AB1;
Bosch--Lütkebohmert--Raynaud, Néron Models, 2.3 Theorem 2′ and 5.3 Lemma 3
(blueprint: lem-sfb-quasifinite-normal-dense-open-immersion).

Proof:
1. By clause (2) of [rem-pc-regular-normal], the normal Noetherian target is a finite
   disjoint union of normal integral open components. Cover each by nonempty affine
   opens V using [lem-weil-pbc-affine-opens-basis]. It suffices to treat the restrictions
   f_V : W = f⁻¹(V) → V. The empty target requires no choice of component.
2. Put H_V = H ∩ V. Since V is integral and H is dense, H_V is nonempty and irreducible.
   Its inverse image is isomorphic to H_V and is dense in W: it is the intersection of
   the open W with the dense open f⁻¹(H) of X. Thus W is irreducible. It is reduced
   since X is reduced, by [def-pc-reduced-scheme], hence W and V are integral by
   [def-pc-integral-scheme].
3. Finite type and monicity restrict to f_V. Apply
   [lem-trf-monomorphism-finite-type-composite-lqf] with the identity on V to obtain
   separatedness and unramifiedness. By [lem-weil-pbc-unramified-fibre-point-isolated],
   every point is isolated in its fibre. Together with finite type this is
   quasi-finiteness in [pqf-def-quasifinite].
4. The affine V is qcqs by [lem-weil-pbc-affine-scheme-qcqs]. By
   [pqf-lem-normalization-open], factor f_V as W → N → V, the first arrow an open
   immersion and the second integral, using the relative normalization of V in W.
   The map f_V is quasi-compact and quasi-separated, so clause (iv) of
   [lem-weil-pbc-relative-normalization] makes N integral since W is integral.
5. By [lem-sc-scheme-sober], W, N and V have unique generic points. The open immersion
   W → N identifies generic points and their local rings. The given isomorphism over
   H_V likewise identifies those of W and V. Since W → N → V is f_V, the second map
   sends the generic point to the generic point and induces an isomorphism of their
   local rings. These are their function fields by
   [lem-sc-integral-function-field-affine-fraction].
6. Apply [lem-trf-integral-birational-normal-isomorphism] to N → V: both schemes are
   integral, the map is integral and birational by steps 4--5, and V has normal local
   rings. Hence N → V is an isomorphism, and f_V is an open immersion by
   [def-weil-open-immersion].
7. The open images in the V agree on overlaps, since both are the image of the same
   restriction of f. Their inverses agree as inverses of that restriction and glue
   by the sheaf axiom to an inverse X ≅ O over Z, for the union O of those open images.
   Thus f is an open immersion by [def-weil-open-immersion]. If Z is empty, X is empty
   and the same empty gluing applies.
-/
theorem isOpenImmersion_of_mono_dense_open_isIso
    {X Z : Scheme.{u}} (f : X ⟶ Z)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [IsLocallyNoetherian Z] [CompactSpace Z] [IsReduced X] [Mono f]
    (hnormal : ∀ z : Z,
      IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z))
    (hdense : ∃ H : Z.Opens,
      Dense (H : Set Z) ∧ Dense (f ⁻¹ᵁ H : Set X) ∧ IsIso (f ∣_ H)) :
    IsOpenImmersion f := by
  sorry

end AlgebraicGeometry
