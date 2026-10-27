/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale

/-! # Étale trivialization of relative tori

Source: Conrad, Reductive group schemes, Proposition B.3.4, printed pp.291--292,
and the proof of Lemma 5.1.3, printed p.137
(blueprint: lem-sfb-torus-etale-trivialization).

For any scheme U, the diagonalizable group D_U(M) is constructed by pulling back
Spec Gamma(U, O_U)[M] along U.toSpecΓ. Over an affine open Spec C this is Spec C[M]:
base change sends the group algebra to C[M] and preserves its three Hopf operations.
Consequently this construction is precisely the gluing of the affine groups in the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every relative torus splits as a diagonalizable group of a finite free lattice on
an étale covering. The base is arbitrary, the covering can be empty, and rank zero is
allowed. `Module.Free ℤ` and `Module.Finite ℤ` express finite-rank free abelian groups.
The displayed isomorphisms live in the category of group objects over each cover member.
Source: Conrad, Reductive group schemes, Proposition B.3.4, printed pp.291--292,
and Lemma 5.1.3, printed p.137 (blueprint: lem-sfb-torus-etale-trivialization).

Proof, following the six steps of the node:
1. For P_r = D_S(Z^r), the group algebra's monomials identify its functor of points
with r-tuples of units by the affine adjunction. The Hopf operations give the group
operations. These formulas respect restrictions and base change, so scheme-morphism
gluing and def-sfb-relative-torus give an fppf cover V_i with P_(r_i) = T over V_i.
Uses def-sfb-ring-diagonalizable-group, lem-a1-locally-ringed-space-affine-adjunction,
lem-weil-pbc-scheme-morphism-gluing and def-sfb-relative-torus.
2. The splitting-isomorphism functor F_r(W) = Isom_(W-gp)(P_r x W, T x W) is an fppf
sheaf. Base-change an fppf cover to both sources; fpqc descent glues the maps and their
inverses. Uniqueness descends the group identities. Uses
lem-trf-fppf-covering-base-change, lem-trf-fppf-covering-is-fpqc and
lem-weil-pbc-fpqc-representable-descent.
3. On V_i, character duality identifies F_r with the functor represented by the
coproduct L_(r,i) of copies of V_i indexed by Isom_Z(Z^(r_i), Z^r). Isomorphisms give
locally constant lattice isomorphisms; conversely their clopen fibres carry maps D(a)
which glue together with their inverses. Empty affine opens cause no restriction.
Uses lem-sfb-relative-diagonalizable-character-duality,
lem-weil-pbc-scheme-coproduct-family and lem-weil-pbc-scheme-morphism-gluing.
4. The map from the coproduct of the L_(r,i) to F_r has scheme-test pullbacks equal
to the coproducts of Z x_S V_i. These projections are surjective, flat and locally
finitely presented. The fppf atlas bootstrap makes F_r an algebraic space. Uses
lem-weil-pbc-scheme-coproduct-family, lem-trf-fppf-covering-base-change,
lem-weil-pbc-etale-composition-cancellation, lem-sfb-scheme-etale-source-target-properties,
lem-sfb-fppf-space-atlas-bootstrap and def-weil-size-convention.
5. Choose a surjective étale scheme atlas W_r of F_r. Over V_i its map factors through
L_(r,i), étale over V_i by source locality. Hence W_r x_S V_i is étale over V_i.
Fpqc descent for scheme morphisms makes W_r étale over S. Uses def-trf-algebraic-space,
lem-sfb-scheme-etale-source-target-properties, lem-weil-pbc-etale-composition-cancellation,
lem-trf-fppf-covering-is-fpqc and lem-galois-fpqc-descend-etale.
6. Every s lifts to a V_i and thus to F_(r_i); atlas surjectivity gives a lift to W_(r_i).
The atlas section of F_r supplies the tautological group-scheme isomorphism, whose
inverse is the required splitting. Take M_r = Z^r. For the empty base use the empty
family; r = 0 gives the trivial group. Uses def-trf-algebraic-space. -/
theorem torus_etale_trivialization (S : Scheme.{u})
    (T : Over S) [GrpObj T] (hT : IsRelativeTorus T) :
    ∃ (J : Type u) (U : J → Over S) (M : J → AddCommGrpCat.{u}),
      (∀ j : J, Etale (U j).hom) ∧
      (∀ s : S, ∃ (j : J) (x : (U j).left), (U j).hom x = s) ∧
      (∀ j : J, Module.Free ℤ (M j) ∧ Module.Finite ℤ (M j)) ∧
      ∀ j : J, Nonempty
        ((Over.pullback (U j).hom).mapGrp.obj (Grp.mk T) ≅
          (Over.pullback (U j).left.toSpecΓ).mapGrp.obj
            (ringDiagonalizableGroup Γ((U j).left, ⊤) (M j))) := by
  sorry

end AlgebraicGeometry
