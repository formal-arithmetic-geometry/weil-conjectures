/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.ZetaSeries
public import Sheaf.AlgebraicGeometry.PureDimension
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.Dimension

/-! # Rationalizing a geometric node over its residue field

Source: Stacks Project, Curves, Tag 0CBY, first proof, residue-field paragraph,
expanded using Tags 0C59 and 0C5B, Morphisms Tag 02G7, Algebra Tag 00P3,
and Properties Tag 04MU (blueprint: lem-trf-geometric-node-residue-rationalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonsmooth point of a geometrically nodal finite type scheme has finite separable
residue field. Its canonical residue-field lift is closed and rational on a finite type
scheme of dimension one, and its geometric lifts remain nonsmooth ordinary double points.
The two projection equations determine `z` uniquely. Rationality makes the point over its
image in every algebraic-closure base change unique, so quantifying over `zbar` with the
specified first projection states the property of that induced geometric point.
All completed-local-ring comparisons are ring isomorphisms.

Source: Stacks Project, Curves, Tag 0CBY, first proof, residue-field paragraph,
expanded through Tags 0C59 and 0C5B and Morphisms Tag 02G7; dimension uses Algebra
Tag 00P3 and Properties Tag 04MU
(blueprint: lem-trf-geometric-node-residue-rationalization).

Proof:
1. By lem-pc-flat-field, C is flat over k. The finite type coordinate rings are
   finitely presented by lem-weil-pbc-finite-type-noetherian-finite-presentation.
   Apply lem-trf-nodal-family-fitting-singular: the first-Fitting singular subscheme
   Z has support the nonsmooth locus, is unramified, and commutes with base change.
2. On an affine chart Spec A around x, Z is Spec(A/I). This quotient is finite type.
   Apply lem-trf-unramified-over-field-local-criterion to Z: x is closed in Z and
   its residue field is finite separable over k. Its residue field is C.residueField x,
   and the closed immersion Z into C makes x closed in C.
3. The fibre-product universal property gives z from the residue-point map and the
   identity of Spec F. Thus z lies over x. On residue fields its structural map a
   has a retraction b into F. Since b is injective, b a = 1 implies a b = 1, proving
   rationality. The residue-point map factors through Z, so z factors through Z_F.
4. By lem-sfb-finite-type-composition-base-change, D is finite type over F.
   By lem-trf-nodal-family-fitting-singular and its base-change assertion, Z_F is
   the unramified singular subscheme of D. Apply the unramified local criterion
   again to make z closed in Z_F, hence in D. No separatedness is used.
5. For every algebraic closure Omega of F, zbar factors through Z_Omega. The same
   singular-support base-change assertion makes zbar nonsmooth. Associativity of
   fibre products identifies D_Omega with C_Omega; apply the given nodal completion
   hypothesis using the composite embedding k into F into Omega.
6. This geometric base change is nonempty because it contains zbar. Its pure
   dimension one, together with lem-sc-irreducible-components-cover, gives
   topological Krull dimension one by the irreducible-closed-chain definition.
7. Choose a finite affine open cover of D. The inverse images cover D_Omega by
   lem-weil-pbc-open-fibre-product and lem-weil-pbc-fibre-product-affine-spectra.
   The ring clause of lem-pc-dim-base-change identifies the dimensions chartwise.
   Apply lem-pc-dimension-affine-open-cover and lem-pc-scheme-dimension-local-rings
   to obtain dim D = dim D_Omega = 1. -/
theorem geometric_node_residue_rationalization
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hgeom : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω],
      (pullback (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).IsPureDimension 1 ∧
        ∀ y : pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
          y ∉ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).smoothLocus →
            Nonempty
              (AdicCompletion (IsLocalRing.maximalIdeal
                  ((pullback (C := Scheme.{u}) f
                    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).presheaf.stalk y))
                ((pullback (C := Scheme.{u}) f
                    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).presheaf.stalk y)
                ≃+* (MvPowerSeries (Fin 2) Ω ⧸
                  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                    MvPowerSeries.X (1 : Fin 2)})))
    (x : C) (hx : x ∉ f.smoothLocus) :
    x ∈ closedPoints C ∧ (f.residueFieldAlgebraMap x).Finite ∧
      @Algebra.IsSeparable k (C.residueField x) _ _
        (f.residueFieldAlgebraMap x).toAlgebra ∧
      ∃ z : Spec (C.residueField x) ⟶
          pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))),
        z ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))) =
            C.fromSpecResidueField x ∧
        z ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))) =
            𝟙 (Spec (C.residueField x)) ∧
        LocallyOfFiniteType
          (pullback.snd f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x)))) ∧
        QuasiCompact
          (pullback.snd f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x)))) ∧
        topologicalKrullDim
          (pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x)))) = 1 ∧
        z (IsLocalRing.closedPoint (C.residueField x)) ∈
          closedPoints (pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x)))) ∧
        pullback.fst f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x)))
          (z (IsLocalRing.closedPoint (C.residueField x))) = x ∧
        Function.Bijective
          ((pullback.snd f
            (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x)))).residueFieldAlgebraMap
              (z (IsLocalRing.closedPoint (C.residueField x)))) ∧
        ∀ (Ω : Type u) [Field Ω] [Algebra (C.residueField x) Ω]
          [IsAlgClosure (C.residueField x) Ω]
          (zbar : pullback (C := Scheme.{u})
            (pullback.snd f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))))
            (Spec.map (CommRingCat.ofHom (algebraMap (C.residueField x) Ω)))),
          pullback.fst
              (pullback.snd f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))))
              (Spec.map (CommRingCat.ofHom (algebraMap (C.residueField x) Ω))) zbar =
            z (IsLocalRing.closedPoint (C.residueField x)) →
          zbar ∉ (pullback.snd
              (pullback.snd f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))))
              (Spec.map (CommRingCat.ofHom (algebraMap (C.residueField x) Ω)))).smoothLocus ∧
          Nonempty
            (AdicCompletion (IsLocalRing.maximalIdeal
                ((pullback (C := Scheme.{u})
                  (pullback.snd f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))))
                  (Spec.map (CommRingCat.ofHom
                    (algebraMap (C.residueField x) Ω)))).presheaf.stalk zbar))
              ((pullback (C := Scheme.{u})
                (pullback.snd f (Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x))))
                (Spec.map (CommRingCat.ofHom
                    (algebraMap (C.residueField x) Ω)))).presheaf.stalk zbar)
              ≃+* (MvPowerSeries (Fin 2) Ω ⧸
                Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                  MvPowerSeries.X (1 : Fin 2)})) := by
  sorry

end AlgebraicGeometry
