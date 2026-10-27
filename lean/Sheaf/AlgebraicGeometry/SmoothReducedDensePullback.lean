/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite

/-!
# Smooth pullback of reduced schemes and dense open subsets

Source: ILO, Expose VIII, 2.2.7--2.2.9, printed pp.90--91; Stacks Project,
Tags 034E, 01UA and 00HS (blueprint: lem-trf-smooth-reduced-dense-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth morphism to a reduced locally Noetherian scheme has reduced locally
Noetherian source, preserves generic points of irreducible components, and pulls back
any dense open subset densely in the source and in each of its irreducible components.
Extension of a quasi-coherent ideal of finite type preserves nowhere density of its zero set.

Source: ILO, Expose VIII, 2.2.7--2.2.9, printed pp.90--91; Stacks Project,
Tags 034E (descent.tex, lemma-reduced-local-smooth), 01UA (morphisms.tex,
lemma-fppf-open) and 00HS (algebra.tex, lemma-flat-going-down)
(blueprint: lem-trf-smooth-reduced-dense-pullback).

Proof:
1. By `lem-pc-smooth-flat`, the morphism is flat and locally of finite presentation.
   Finite presentations are finite type (`def-sbc-locally-finite-presentation`,
   `def-weil-finite-type-morphism`), so `pqf-lem-locnoeth-lft` gives local Noetherianity.
2. By `sbc-lem-smooth-geometrically-reduced`, every field-valued base change is reduced:
   factor the field-valued point through its residue field and use geometric reducedness
   of that fibre. Apply `lem-sfb-flat-geometrically-reduced-pullback` to the identity
   base change of S. The fibre-product universal property (`def-pc-fibre-product`)
   identifies this pullback with T, proving reducedness.
3. Let xi be generic in a component C of T. Choose a component D containing h(xi)
   (`lem-sc-irreducible-components-cover`) and its generic point eta
   (`lem-sc-scheme-sober`). Flat generalization lifting
   (`lem-weil-pbc-flat-generalizations-lift`) lifts eta to xi' generalizing xi.
   The closure of xi' contains C; maximality of C makes it equal to C
   (`def-weil-irreducible-components`, `def-sc-generic-point`). Uniqueness of generic
   points (`lem-sc-scheme-sober`) gives xi' = xi, hence h(xi) = eta.
4. Flatness and local finite presentation make h open (`lem-weil-pbc-flat-lfp-open`).
   Every nonempty open W in T has nonempty open image, meeting the dense open U.
   Lifting a point of that intersection shows W meets the inverse image of U.
5. For a component D of S, local finiteness
   (`lem-sc-locnoeth-components-locally-finite`) gives a neighbourhood of its generic
   point meeting finitely many components. Remove the other components. The remaining
   nonempty open lies in D, since components cover S. It meets U, so the generic point
   of D lies in U. Step 3 puts each component generic point of T in the inverse image
   of U, proving density in that component in its subspace topology.
6. The pullback of the closed immersion V(J) into S is a closed immersion
   (`lem-weil-pbc-closed-immersion-base-change`). Its kernel is J.comap h
   (`def-nagata-extended-ideal`, `def-sbc-closed-immersion-ideal-sheaf`), and its image
   is the zero set (`lem-weil-pbc-closed-immersion-image-zero-locus`). On affine charts,
   `lem-weil-pbc-fibre-product-affine-spectra` identifies its ring with B tensor_A A/I.
   The inverse maps b tensor a_bar to b*h(a) modulo IB, and b_bar to b tensor 1,
   identify this ring with B/IB. A prime contains IB exactly when its contraction
   contains I. Thus the zero set of the extended ideal is the inverse image of V(J).
7. The complement of V(J) is dense open. Step 4 makes its inverse image dense, and
   step 6 identifies the closed complement with the extended ideal's zero set.
   A closed set with dense complement is nowhere dense. Empty schemes give vacuous
   source conclusions; omitted components and the unit ideal cause no exception. -/
theorem smooth_reduced_dense_pullback {S T : Scheme.{u}}
    [IsReduced S] [IsLocallyNoetherian S] (h : T ⟶ S) [Smooth h] :
    IsReduced T ∧ IsLocallyNoetherian T ∧
      (∀ (C : Set T), C ∈ irreducibleComponents T →
        ∀ (ξ : T), IsGenericPoint ξ C →
          ∃ D : Set S, D ∈ irreducibleComponents S ∧ IsGenericPoint (h ξ) D) ∧
      (∀ (U : S.Opens), Dense (U : Set S) →
        Dense (h ⁻¹' (U : Set S)) ∧
          ∀ (C : Set T), C ∈ irreducibleComponents T →
            Dense ((Subtype.val : C → T) ⁻¹' (h ⁻¹' (U : Set S)))) ∧
      (∀ (J : S.IdealSheafData), Scheme.Modules.IsQuasiCoherentFiniteType J.toModules →
        IsNowhereDense (J.support : Set S) →
          IsNowhereDense ((J.comap h).support : Set T)) := by
  sorry

end AlgebraicGeometry
