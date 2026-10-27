/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Picard.RationalPointBaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeResidueIso
import Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange

/-!
# Rigidified see-saw on a product

Source: Milne, Abelian Varieties, Chapter I, Theorem 5.16 and Corollaries 5.17–5.18,
printed p.26; uniqueness from flat base change for global functions, Stacks Tag 02KH
(blueprint: lem-sfb-rigidified-product-seesaw).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Every prescribed isomorphism along the rational section extends uniquely when the
invertible modules agree on all rational fibres. A fibrewise trivial invertible module is
therefore the pullback of its restriction to that section. All pullbacks here are tensor
pullbacks, including the restrictions to the fibres of the second projection.

Source: Milne, Abelian Varieties, I 5.16–5.18, printed p.26, and Stacks Tag 02KH
(blueprint: lem-sfb-rigidified-product-seesaw).

Proof:
1. The base change q of f to T is proper, flat and of finite presentation:
use lem-pc-flat-field, pqf-lem-lft-fp-locnoeth and
lem-sfb-space-flat-proper-fp-locality. Its fibres are geometrically integral. Smoothness
makes T reduced (sbc-lem-smooth-geometrically-reduced); finite type makes T Noetherian
(lem-weil-pbc-finite-type-over-noetherian).
2. Form H = F tensor E-dual. In local rank-one bases the fibre isomorphisms trivialize H,
and the prescribed alpha is a trivialization of the section restriction of H
(def-sc-invertible-module, def-pc-module-pullback).
3. Closed points of T are rational (lem-weil-pbc-closed-point-residue-field-base).
The trivial-fibre locus is closed (lem-sc-picard-fiber-triviality-closed) and contains
all closed points, which are dense (lem-sc-lft-over-field-jacobson-space). Thus all
residue-field fibres of H are trivial.
4. Their global sections have dimension one (lem-pc-h0-proper-variety). The invertible
module H is finitely presented and flat over T, as is seen in its local bases.
Grauert's theorem thm-pc-semicontinuity-base-change makes N = q_* H invertible and
identifies its residue-field fibres with these global sections.
5. The evaluation q^* N → H of lem-pc-module-pullback-adjunction is multiplication on
fibre sections. Under the preceding base-change identification, each fibre map is the
isomorphism O tensor k → O. Both modules have rank one; hence the evaluation is an
isomorphism by lem-sc-finite-locally-free-residue-isomorphism.
6. Restrict evaluation to the section, giving b : N ≅ s_x^* H. If a is the prescribed
trivialization there, evaluation composed with q^*(b^{-1} a) trivializes H and hence
gives the desired isomorphism E ≅ F. Its section restriction is exactly alpha.
7. Proper geometric integrality gives Gamma(V,O) = k (lem-pc-h0-proper-variety).
Flat base change on each affine open U of T identifies Gamma(V times U,O) with
Gamma(U,O) (lem-weil-pbc-stein-flat-base-change-global-sections), via pullback.
Thus any global function u satisfies u = q^* s_x^* u. The ratio of two extensions is
an automorphism of E, hence multiplication by a global unit. Its section restriction
is one, so this identity makes the ratio one. This proves uniqueness.
8. For fibrewise trivial H, q^* s_x^* H also has trivial fibres, since an invertible
module over a field is one-dimensional. Apply the extension assertion to this module
and H, using the canonical identity on their section restrictions. Invert the resulting
isomorphism to obtain H ≅ q^* s_x^* H. The empty base requires no separate assumption. -/
theorem rigidified_product_seesaw
    {k : Type u} [Field k] [IsAlgClosed k]
    {V T : Scheme.{u}} (f : V ⟶ Spec (.of k)) (g : T ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    [Smooth g] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (x : f.fieldPoints k) :
    (∀ (E F : (Limits.pullback f g).Modules) [E.IsInvertible] [F.IsInvertible],
      (∀ t : g.fieldPoints k,
        Nonempty
          ((tensorPullback
            (Limits.pullback.fst (Limits.pullback.snd f g) t.1)).obj E ≅
            (tensorPullback
              (Limits.pullback.fst (Limits.pullback.snd f g) t.1)).obj F)) →
      ∀ α : (tensorPullback (f.fieldPointBaseChange x (Over.mk g))).obj E ≅
          (tensorPullback (f.fieldPointBaseChange x (Over.mk g))).obj F,
        ∃! e : E ≅ F,
          (tensorPullback (f.fieldPointBaseChange x (Over.mk g))).mapIso e = α) ∧
    (∀ (H : (Limits.pullback f g).Modules) [H.IsInvertible],
      (∀ t : g.fieldPoints k,
        Nonempty
          ((tensorPullback
            (Limits.pullback.fst (Limits.pullback.snd f g) t.1)).obj H ≅
            SheafOfModules.unit _)) →
      Nonempty (H ≅ (tensorPullback (Limits.pullback.snd f g)).obj
        ((tensorPullback (f.fieldPointBaseChange x (Over.mk g))).obj H))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
