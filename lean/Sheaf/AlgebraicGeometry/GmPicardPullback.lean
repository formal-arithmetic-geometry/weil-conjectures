/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero

/-!
# Naturality of the Picard identification with étale cohomology

Source: Stacks Project, Cohomology on Sites, Tag 040E, Lemma 21.6.1, and functoriality
of cohomology under pullback (blueprint: lem-sc-h1-gm-pic-pullback).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The canonical Picard identification intertwines tensor pullback with cohomology
pullback followed by the adjoint comparison `u⁻¹ Gₘ → Gₘ`. In degree zero this composite
is pullback of global units. The existential invertibility witness makes the class of
`u*L` well typed without adding an invertibility assumption on the pullback.
The Picard equivalence sends `L` to the class of its étale torsor `Isom(O,L)`, so the
first clause is also precisely the asserted equality of torsor classes.

Source: Stacks Project, Tag 040E (blueprint: lem-sc-h1-gm-pic-pullback).

Proof:
1. By lem-sc-h1-gm-pic and lem-sc-torsor-h1, the class of `L` is represented by
   the étale torsor `T_L = Isom(O_X,L)`.
2. Pullback sends a local generator `s` to `1 ⊗ s`. This is equivariant for the
   comparison of units, since `1 ⊗ fs = c_u(f)(1 ⊗ s)` (def-pc-module-pullback,
   def-weil-pbc-inverse-image). On a trivializing cover this identifies the
   contracted product of `u⁻¹T_L` with `Gₘ,Y` with `T_{u*L}` (Stacks Tag 03AH).
3. The two clauses of lem-sc-etale-torsor-h1-functoriality send torsor classes
   first to inverse-image torsors and then to their contracted products.
   Naturality of cohomology (lem-weil-pbc-cohomology-pullback-functorial) and
   lem-sc-h1-gm-pic therefore identify the composite with `[L] ↦ [u*L]`.
4. By lem-weil-pbc-cohomology-pullback-degree-zero, the degree-zero pullback is
   the adjunction unit on global sections. Composing with the adjoint comparison
   of units gives the map on units induced by `u.appTop`. -/
theorem picard_cohomology_pullback
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [IsCurve (X ↘ Spec (.of k))] [IsCurve (Y ↘ Spec (.of k'))] (u : Y ⟶ X) :
    (∀ (L : X.Modules) [L.IsInvertible],
      ∃ h : ((Modules.tensorPullback u).obj L).IsInvertible,
        Sheaf.H.map (upperStarGmSheafToGmSheaf u) 1
          (Etale.cohomologyMap u X.gmSheaf 1
            (Pic.toCohomologicalPicardGroup X (Pic.ofIsInvertible L))) =
        Pic.toCohomologicalPicardGroup Y
          (@Pic.ofIsInvertible Y ((Modules.tensorPullback u).obj L) h)) ∧
    (∀ a : Γ(X, ⊤)ˣ,
      Sheaf.H.equiv₀ Y.gmSheaf (MorphismProperty.Over.mkIdTerminal @Etale Y)
        (Sheaf.H.map (upperStarGmSheafToGmSheaf u) 0
          (Etale.cohomologyMap u X.gmSheaf 0
            ((Sheaf.H.equiv₀ X.gmSheaf
              (MorphismProperty.Over.mkIdTerminal @Etale X)).symm
                (ULift.up (Additive.ofMul a))))) =
        ULift.up (Additive.ofMul (Units.map u.appTop.hom.toMonoidHom a))) := by
  sorry

end AlgebraicGeometry.Scheme
