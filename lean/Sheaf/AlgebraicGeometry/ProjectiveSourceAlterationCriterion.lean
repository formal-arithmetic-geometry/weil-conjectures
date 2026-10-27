module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Projective sources with finite function-field extension give alterations

Source: Stacks Project, Morphisms, Tags 01WC and 02NW; Varieties, Tag 0B1C;
More on Morphisms, Tag 02UP. The H-projectivity assertion uses the closed-graph argument
of Morphisms, Tag 0C4Q.
(blueprint: lem-sfb-projective-source-alteration-criterion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism from an integral projective finite-type scheme to an integral separated
finite-type scheme over a field is H-projective and proper. If it is dominant and its
induced function-field extension is finite, it is surjective and finite over a dense
open, hence an alteration. Its generic fibre is integral of dimension zero, with one
point and residue field the function field of the source.

The generic fibre is written as the pullback along `Y.fromSpecStalk (genericPoint Y)`:
its base is exactly `Spec Y.functionField`. The finite-extension hypothesis uses the
canonical map on generic stalks, not an independently supplied field embedding.
The residue-field clause is canonical: the unique point of the generic fibre lies over the
generic point of `X` under the first projection, and the induced map of residue fields
`κ(genericPoint X) ⟶ κ(x)` is an isomorphism; `κ(genericPoint X)` is the function field
of the integral scheme `X` (its stalk at the generic point is already a field).

Source: Stacks Project, Morphisms, Tags 0C4Q, 01WC, 01RV and 02NW; Varieties, Tag 0B1C;
More on Morphisms, Tag 02UP.
(blueprint: lem-sfb-projective-source-alteration-criterion).

Proof:
1. Write a : X -> Spec k and b : Y -> Spec k for the structure maps. The map f is
   over k. Apply lem-sfb-finite-constant-projective-graph with the trivial finite
   extension k/k. The chosen closed embedding of X in projective space over k and
   separatedness of Y/k give a closed graph embedding into projective space over Y.
   Its projection is f, so f is H-projective (def-kun-projective).
2. By lem-kun-projective-implies-proper, f is proper. In particular it is universally
   closed and of finite type (def-weil-proper-morphism).
3. Under dominance, the image of f is dense. Properness makes that image closed.
   Thus it is all of Y, giving def-weil-surjective-morphism.
4. Dominance sends the generic point xi of X to the generic point eta of Y. On a
   nonempty affine V = Spec R of Y and nonempty affine W = Spec C in its inverse
   image, lem-sc-integral-function-field-affine-fraction identifies k(Y) and k(X)
   with Frac R and Frac C. The map R -> C is injective, since its composite into
   k(X) factors through the induced embedding k(Y) -> k(X). The singleton case of
   lem-sbc-finite-affine-tensor-base-change identifies the generic-fibre chart with
   Spec (C tensor_R k(Y)); lem-weil-pbc-open-immersion-base-change gives the open
   charts covering the fibre. The pullback of c is c tensor 1 by
   lem-sbc-affine-fibre-sections-tensor. By
   lem-weil-pbc-generic-fibre-localization-domain-irreducible, this chart algebra is
   the domain B = (R minus {0})^{-1}C, after exchanging tensor factors.
5. The injective K-linear map B -> L, where K = k(Y) and L = k(X), makes B a
   finite-dimensional K-vector subspace of L. By
   lem-weil-pbc-finite-dimensional-domain-is-field, B is a field. Its image contains
   C and thus all its fractions, so B is L. Its unique point maps to xi: its prime
   contracts to zero in C. By def-pc-scheme-fibre the first projection identifies
   the points of the fibre with f^{-1}({eta}), so all the one-point charts have the
   same point. A chart exists since xi lies over eta. Any nonempty chart is the
   whole fibre, identifying it with Spec L. This is integral, has dimension zero,
   and its one point has residue field L (def-weil-affine-spectrum,
   def-pc-integral-scheme).
6. Apply lem-trf-proper-finite-fibre-finite-near at eta: properness and the singleton
   fibre give a neighbourhood U on which f is finite. Since eta is generic, U is
   dense. Properness, surjectivity, integrality of X and Y, and finiteness over U
   are precisely the alteration conditions in the statement.
-/
theorem projective_source_alteration_criterion
    (k : Type u) [Field k]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsIntegral X] [IsIntegral Y]
    [IsHProjective (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    IsHProjective f ∧ IsProper f ∧
      (∀ [IsDominant f],
        (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.Finite →
        Surjective f ∧
          (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (f ∣_ U)) ∧
          IsIntegral (pullback f (Y.fromSpecStalk (genericPoint Y))) ∧
          topologicalKrullDim ↥(pullback f (Y.fromSpecStalk (genericPoint Y))) = 0 ∧
          ∃ x : ↥(pullback f (Y.fromSpecStalk (genericPoint Y))),
            (∀ z : ↥(pullback f (Y.fromSpecStalk (genericPoint Y))), z = x) ∧
            (pullback.fst f (Y.fromSpecStalk (genericPoint Y))) x = genericPoint X ∧
            IsIso ((pullback.fst f (Y.fromSpecStalk (genericPoint Y))).residueFieldMap x)) := by
  sorry

end AlgebraicGeometry
