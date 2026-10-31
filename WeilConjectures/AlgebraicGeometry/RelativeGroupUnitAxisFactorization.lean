/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.ProperFlatGlobalSections
import WeilConjectures.RingTheory.SmoothAlgebraReduced
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Units on relative powers of a smooth connected group scheme

Source: Milne, Algebraic Groups (2017), Proposition 12.48, identity (79), and
Remark 12.50; relative extension using Stacks Tags 0E0L and 033B
(blueprint: lem-sfb-relative-group-unit-axis-factorization).

Products are taken in `Over S`, so their underlying schemes are fibre products over `S`.
The two helper maps are defined by the product universal property, using the identity
of the given group object in all constant coordinates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj BigOperators

namespace AlgebraicGeometry

/-- Insert a group element into coordinate `i`, with identity elements elsewhere.
Source: Milne, Algebraic Groups (2017), Proposition 12.48, identity (79), iterated
(blueprint: lem-sfb-relative-group-unit-axis-factorization). -/
noncomputable def groupIdentityAxis {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    (n : ℕ) (i : Fin n) : G ⟶ ∏ᶜ (fun _ : Fin n => G) :=
  Pi.lift (fun j => if j = i then 𝟙 G else (1 : G ⟶ G))

/-- The all-identity section of a finite relative power of a group scheme.
Source: Milne, Algebraic Groups (2017), Proposition 12.48, identity (79), iterated
(blueprint: lem-sfb-relative-group-unit-axis-factorization). -/
noncomputable def groupPowerIdentitySection {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    (n : ℕ) : Over.mk (𝟙 S) ⟶ ∏ᶜ (fun _ : Fin n => G) :=
  Pi.lift (fun _ => (1 : Over.mk (𝟙 S) ⟶ G))

/-- Every unit on a nonempty finite relative power factors by its identity-axis restrictions,
with the base-unit correction of exponent `1 - n`. In particular an axis-trivial unit is one.
The equalities are equalities of global regular functions, via coercion from units.

Source: Milne, Algebraic Groups (2017), Proposition 12.48, identity (79), and Remark 12.50;
relative extension via Stacks Tags 0E0L and 033B
(blueprint: lem-sfb-relative-group-unit-axis-factorization).

Proof:
1. Put `c = e_n^* u` and `u_i = a_i^* u`. Normalize to the unit
   `v = u * p_n^*(c^(n-1)) * product_i pi_i^*(u_i^(-1))`.
   The fibre-product identities give `a_j^* v = 1` for every `j` and `e_n^* v = 1`.
   For one factor the axis is the identity map.
2. If the structure map is proper, smoothness gives flatness and geometrically reduced
   fibres (`lem-pc-smooth-flat`, `sbc-lem-smooth-geometrically-reduced`). Apply
   `lem-sc-proper-flat-global-sections` to the structure map and each base-changed
   projection. Pullback on global sections is bijective at each stage, so `v = p_n^* d`.
   The identity section gives `d = 1`. This argument allows nonreduced bases.
3. If the base is reduced, each iterated product is reduced: the successive projections
   are smooth by `lem-pc-proper-base-change`, and affine smooth algebras over reduced
   rings are reduced by `lem-sfb-smooth-algebra-over-reduced-ring` (033B).
   Localizations remain reduced, giving the local-ring condition without Noetherianity.
4. Over an algebraically closed field mapping to the base, the powers are nonempty smooth
   connected schemes. By `lem-sbc-smooth-connected-generic-geometry-core` they are integral
   with integrally closed local rings. They are finite type by
   `lem-sfb-finite-type-composition-base-change`. Separatedness follows by base change
   (`lem-weil-pbc-separated-base-change`) and taking the intersection of the pulled-back
   coordinate diagonals (`lem-weil-pbc-closed-immersion-base-change`).
5. Apply `lem-sfb-rosenlicht-product-unit-factorization` to successive pairs of factors.
   Induction, starting with one factor, shows every axis-trivial unit on each geometric
   fibre is one: its restrictions to the two blocks and to their identity are all one.
6. Thus `v - 1` vanishes in every residue field, by extending each residue field to an
   algebraic closure and using the fibre-product universal property. On each affine open,
   `lem-weil-pbc-qc-scheme-vanishing-section-nilpotent` makes it nilpotent; reducedness
   from step 3 makes it zero. The sheaf axiom gives `v = 1` globally.
7. Rearrange the normalization to obtain the displayed formula. If all axis restrictions
   of `u` are one, then `c = 1` using any axis (there is one since `n ≥ 1`), so `u = 1`.
   For the empty base the section rings are zero rings and all these identities hold. -/
theorem relative_group_unit_axis_factorization {S : Scheme.{u}} (G : Over S)
    [CommGrpObj G] [Smooth G.hom] [IsSeparated G.hom]
    [LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]
    [GeometricallyConnected G.hom] (hbase : IsProper G.hom ∨ IsReduced S)
    (n : ℕ) (hn : 1 ≤ n) (u : (Γ((∏ᶜ (fun _ : Fin n => G)).left, ⊤))ˣ) :
    (u : Γ((∏ᶜ (fun _ : Fin n => G)).left, ⊤)) =
      ↑(Units.map (∏ᶜ (fun _ : Fin n => G)).hom.appTop.hom.toMonoidHom
          ((Units.map (groupPowerIdentitySection G n).left.appTop.hom.toMonoidHom u) ^
            (1 - (n : ℤ))) *
        ∏ i : Fin n,
          Units.map (Pi.π (fun _ : Fin n => G) i).left.appTop.hom.toMonoidHom
            (Units.map (groupIdentityAxis G n i).left.appTop.hom.toMonoidHom u)) ∧
      ((∀ i : Fin n,
          (groupIdentityAxis G n i).left.appTop (u : Γ((∏ᶜ (fun _ : Fin n => G)).left, ⊤))
            = 1) →
        (u : Γ((∏ᶜ (fun _ : Fin n => G)).left, ⊤)) = 1) := by
  sorry

end AlgebraicGeometry
