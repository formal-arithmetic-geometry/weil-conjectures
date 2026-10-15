/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
public import WeilConjectures.AlgebraicGeometry.Curve
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.Variety

/-!
# Smooth projective curves are smooth connected curves

Source: the blueprint of the Weil conjectures, chapter `sec-abelian-varieties`, unit
`sk-def-av-jacobian`, node order 455 (blueprint: lem-pc-curves-are-sc).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: lem-pc-curves-are-sc) A smooth projective curve over an algebraically closed
field is a smooth connected curve in the sense of the blueprint's file 06.
Source: blueprint `sec-abelian-varieties/sk-def-av-jacobian/lem-pc-curves-are-sc.md`.

Proof:
1. Unfold `Scheme.Hom.IsSmoothProjectiveCurve` (def-pc-smooth-projective-curve) and
   `Scheme.Hom.IsCurveOverField` (def-pc-curve). The scheme is integral, separated and of
   finite type over the field, with `Scheme.dim X = 1` (def-pc-dimension); its structure
   morphism is smooth. Projectivity is not needed in the remaining steps.
2. An integral scheme is nonempty and irreducible (def-pc-integral-scheme and
   lem-pc-integral-scheme-irreducible; Stacks, Tag 01ON).
3. Irreducibility implies connectedness (lem-pc-irreducible-space-connected; Stacks,
   Topology, after Tag 004V), giving ConnectedSpace X (def-weil-connected-scheme).
4. The supremum of the dimensions of the local rings equals the topological Krull
   dimension (lem-pc-scheme-dimension-local-rings; Stacks, Tag 04MU). Thus
   `topologicalKrullDim X = 1`, in particular it is at most one.
5. Assemble separatedness, finite type, connectedness and dimension one into
   `IsConnectedCurve f` (def-sc-curves). Together with smoothness
   (def-sbc-smooth-morphisms), this is the required conclusion. -/
theorem Scheme.Hom.isConnectedCurve_of_isSmoothProjectiveCurve
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [f.IsSmoothProjectiveCurve] :
    IsConnectedCurve f ∧ Smooth f := by
  sorry

end AlgebraicGeometry
