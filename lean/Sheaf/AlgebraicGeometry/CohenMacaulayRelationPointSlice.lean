/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.CategoryTheory.Yoneda
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.GroupoidQuasiFiniteLocusDescent
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE

/-! # An affine slice at a finite-type point of a Cohen--Macaulay relation

Source: Stacks Project, More on Groupoids, Tag 04N0 (lemma-max-slice-quasi-finite),
clauses (1)--(4), in Situation 04MY, specialized to an equivalence relation
(blueprint: lem-sfb-cm-relation-point-slice).

The equivalence relation is expressed on sections in `Over S`. The fibre-local
Cohen--Macaulay hypotheses use the existing scheme fibres, stalks, depth and dimension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A Cohen--Macaulay locally finitely presented equivalence relation admits an affine
slice through any finite-type point, with flat locally finitely presented locally
quasi-finite saturation.

Source: Stacks Project, More on Groupoids, Tag 04N0, clauses (1)--(4), with Situation
04MY, specialized to an equivalence relation
(blueprint: lem-sfb-cm-relation-point-slice).

Proof:
1. Injectivity on sections and reflexivity, symmetry and transitivity provide unique
   identity, inverse and composition operations. Yoneda (`lem-pc-yoneda`) realizes
   them as scheme morphisms satisfying `def-a1-groupoid-scheme`. The stabilizer has
   exactly the identity on every test scheme, so it is the identity scheme over `V`;
   each stabilizer fibre is a one-point spectrum and has dimension zero.
2. Apply `lem-sfb-cm-groupoid-maximal-slice` at `v`. It gives an affine `B`, a locally
   finitely presented map `g₀ : B → V`, and `b` over `v`. Its saturation `h₀` is
   Cohen--Macaulay and locally finitely presented, and its fibre has dimension zero
   at `(b,e(v))`. In particular `h₀` is flat.
3. Choose affine neighbourhoods of this point and of `v` giving a finite-presentation
   ring map. By `lem-weil-pbc-fibre-product-affine-spectra`, its fibre is the spectrum
   of the fibre tensor product. Passing to an open preserves dimension at the point.
   Apply `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension` to conclude that `h₀`
   is quasi-finite there, in the sense of `pqf-def-quasifinite`.
4. Local finite presentation implies local finite type for `s`, `t` and `g₀`.
   By `lem-sfb-groupoid-quasifinite-locus-descent`, the quasi-finite locus of `h₀`
   is the inverse image of an open `W` of `B`. The identity-section point shows
   `b ∈ W`. The restricted saturation is locally quasi-finite everywhere.
5. Choose a principal affine open `A` with `b ∈ A ⊆ W`. Its inclusion in `B` has
   presentation `C[z]/(fz-1)` and is locally finitely presented. Composition
   (`lem-sbc-locally-finite-presentation-composition`) gives the same property for
   `g = g₀|A`. Pullbacks identify its saturation with the source-open restriction
   of `h₀`. Stalk maps are unchanged, so flatness persists. Restricting affine
   presentations preserves local finite presentation, and
   `lem-weil-pbc-lqf-restriction-to-opens` preserves local quasi-finiteness.
   Give `A` its induced `S`-structure and take `a` to be `b` in `A`.
-/
theorem exists_cm_relation_point_slice
    {S : Scheme.{u}} {V R : Over S} (s t : R ⟶ V)
    (hinj : ∀ T : Over S,
      Function.Injective (fun r : T ⟶ R ↦ (r ≫ s, r ≫ t)))
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Flat s.left] [Flat t.left]
    (hcm_s : ∀ (v : V.left) (x : s.left.fiber v),
      IsNoetherianRing ((s.left.fiber v).presheaf.stalk x) ∧
        (IsLocalRing.depth (R := (s.left.fiber v).presheaf.stalk x)
          ((s.left.fiber v).presheaf.stalk x) : WithBot ℕ∞) =
          ringKrullDim ((s.left.fiber v).presheaf.stalk x))
    (hcm_t : ∀ (v : V.left) (x : t.left.fiber v),
      IsNoetherianRing ((t.left.fiber v).presheaf.stalk x) ∧
        (IsLocalRing.depth (R := (t.left.fiber v).presheaf.stalk x)
          ((t.left.fiber v).presheaf.stalk x) : WithBot ℕ∞) =
          ringKrullDim ((t.left.fiber v).presheaf.stalk x))
    [LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left]
    (v : V.left) [LocallyOfFiniteType (V.left.fromSpecResidueField v)]
    [QuasiCompact (V.left.fromSpecResidueField v)] :
    ∃ (A : Over S) (g : A ⟶ V) (a : A.left),
      IsAffine A.left ∧ LocallyOfFinitePresentation g.left ∧ g.left a = v ∧
        Flat (pullback.snd g.left t.left ≫ s.left) ∧
        LocallyOfFinitePresentation (pullback.snd g.left t.left ≫ s.left) ∧
        Scheme.Hom.IsLocallyQuasiFinite (pullback.snd g.left t.left ≫ s.left) := by
  sorry

end AlgebraicGeometry
