/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Sheaf.FieldTheory.PurelyTranscendentalExtension
public import WeilConjectures.ZetaSeries
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!
# Geometrically integral component at a purely transcendental point

Source: literature/stacks-project/more-morphisms.tex, Tag 057K, proof paragraph beginning
`Let T be the connected component` (blueprint: lem-trf-smooth-component-pure-transcendental).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Let `C` be a finite type smooth scheme over a field `k`, and let `c` be a point whose
residue field is purely transcendental over `k`. The connected component of `c` is an
open quasi-compact subscheme and is geometrically integral over `k`.

Source: literature/stacks-project/more-morphisms.tex, Tag 057K, proof paragraph beginning
`Let T be the connected component`; the proof uses Tags 04KV, 056T, and 033M.
(blueprint: lem-trf-smooth-component-pure-transcendental).

Proof:
1. Finite type gives finitely many affine charts with finitely generated coordinate
   algebras. By `lem-wf-affine-noetherian-components` and
   `lem-kun-finite-union-noetherian`, the underlying space is Noetherian.
   The component containing `c` is open by
   `lem-sfb-noetherian-connected-components-open`, and quasi-compact by
   `lem-sfb-noetherian-space-compact-subsets`. Its open subscheme is finite type over `k`.
2. Pure transcendence makes `k` algebraically closed in the residue field: write a
   nonzero algebraic element as coprime polynomials `p/q` in a finite set of variables.
   Its monic minimal-polynomial relation gives `q` dividing a power of `p`, hence `q`
   is a unit; its nonzero constant term then makes `p` a unit. The empty-variable case
   is the trivial extension. Open restriction preserves the residue field, so
   `lem-trf-connected-point-geometrically-connected` applied at `c` makes the component
   geometrically connected.
3. Smoothness restricts to the open subscheme. By `lem-trf-smooth-geometrically-normal`,
   all local rings after every field extension are normal domains.
4. After any field extension, the finite affine cover remains finite type, hence
   Noetherian by `lem-wf-affine-noetherian-components`. Clause (2) of
   `rem-pc-regular-normal` decomposes this normal scheme into disjoint clopen integral
   components. Geometric connectedness, including nonemptiness, forces exactly one
   component, so the base change is integral. This proves geometric integrality.
-/
theorem exists_geometricallyIntegral_connectedComponent
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    [Smooth (C ↘ Spec (.of k))]
    (c : C)
    (htrans : @Algebra.IsPurelyTranscendentalExtension k (C.residueField c) _ _
      ((C ↘ Spec (.of k)).residueFieldAlgebraMap c).toAlgebra) :
    ∃ T : C.Opens,
      (T : Set C) = connectedComponent c ∧
        QuasiCompact T.ι ∧
          GeometricallyIntegral (T.ι ≫ C ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry
