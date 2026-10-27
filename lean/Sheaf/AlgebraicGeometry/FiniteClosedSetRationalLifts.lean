/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.DensePoints

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Separation.Basic
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.FibreResidueArrow

/-!
# Rational lifts of a finite closed set after finite scalar extension

Source: Milne, Algebraic Groups (2017), Theorem B.37, Step 2, printed p.605,
second paragraph; its closed-lift argument for surjective morphisms of finite-type schemes.
Residue-field input: Stacks Project, Tag 0478.
(blueprint: lem-sfb-finite-closed-set-rational-lifts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Simultaneously split a finite set of closed target points and lift every resulting
point to a rational source point after one finite extension of the ground field.

Source: Milne, Algebraic Groups (2017), Theorem B.37, Step 2, printed p.605,
second paragraph, generalized from the orbit map to a surjective finite-type-scheme map.
(blueprint: lem-sfb-finite-closed-set-rational-lifts).

Proof: If S is empty, use k and the empty list. Otherwise, each closed nonempty
fibre f⁻¹({s}) contains a point x_s closed in X: finite type gives quasi-compactness,
and schemes are sober and hence T0 (lem-sc-scheme-sober and
lem-sc-quasi-compact-kolmogorov-closed-point). Both E_s = κ(x_s) and F_s = κ(s)
are finite over k by lem-kun-closed-point-field. The residue embedding F_s → E_s
identifies the composite Spec E_s → X → Y with Spec E_s → Spec F_s → Y
(lem-weil-pbc-morphism-from-spec-field).

Apply lem-sfb-common-normal-compatible-groups to the finite nonempty family E_s,
with trivial groups, to get a finite normal K/k containing each E_s and hence each F_s.
The base changes D_s = (Spec E_s)_K and T_s = (Spec F_s)_K are spectra of the
corresponding tensor products (lem-weil-pbc-fibre-product-affine-spectra).
By lem-sfb-normal-field-tensor-rational-points their point sets are finite and their
structural residue maps from K are isomorphisms. Pullback pasting identifies T_s
with the fibre of Y_K → Y over s (def-pc-fibre-product and def-pc-scheme-fibre).
The residue-arrow identification lem-zl-fibre-residue-arrow then gives rationality
as points of Y_K.

The surjective map Spec E_s → Spec F_s remains surjective after base change, so
D_s → T_s is surjective (lem-weil-pbc-surjective-base-change). Each point of D_s
gives a section Spec K → D_s through its residue isomorphism and
lem-weil-pbc-morphism-from-spec-field. Compose with D_s → X_K to get rational
source points whose images cover T_s. Enumerate the finite disjoint union of the
point sets of D_s to obtain the list. Every image lies over S, giving equality
of image sets; repetitions are harmless. Normality is used only to construct K;
no separability, reducedness, smoothness or flatness is assumed. -/
theorem exists_finite_extension_rational_lifts_of_finite_closed_set
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [Surjective f.left]
    (S : Set Y.left) (hS : S.Finite) (hclosed : S ⊆ closedPoints Y.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K),
      ∃ zs : List ((pullback.snd X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fieldPoints K),
        (∀ y : (pullback Y.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
          (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y ∈ S →
          ∃ q : (pullback.snd Y.hom
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fieldPoints K,
            q.1 default = y) ∧
        {y | ∃ z ∈ zs,
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).left
            (z.1 default) = y} =
          (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹' S := by
  sorry

end AlgebraicGeometry
