/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Mathlib.RingTheory.Adjoin.FG
public import Sheaf.RingTheory.ColimOfLocalizations
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.FiniteType
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.AlgebraicGeometry.ZModSheafInvertibleOrders
public import Sheaf.AlgebraicGeometry.PullbackConstantModule
public import Sheaf.Paper.KunBcMapOnCohomology
public import Sheaf.AlgebraicGeometry.HigherDirectImagesLimits
public import Mathlib.FieldTheory.IsSepClosed
public import Sheaf.EtaleCohomology.SepClosedFieldVanishing
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
public import Sheaf.AlgebraicGeometry.OpenProductExchange
public import WeilConjectures.SixFunctors.BaseChange.Derived

@[expose] public section

/-!
# Vanishing on the generic fibre over a normal integral base

Source: Stacks Project, Tag 0F1I, final reduction and final paragraph; current blueprint,
sec-smooth-purity/sk-prop-sf-kunneth-ordinary (blueprint: lem-kun-0f1i-normal).

The function field is the canonical generic stalk. Both fibre products and their projection
are Mathlib's chosen pullbacks. Higher direct images have abelian-group coefficients, with
`ULift` implementing the small-etale-site coefficient universe convention.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The constant cyclic sheaf has zero positive higher direct images along the generic-fibre
projection of a product with a finite-type scheme over a field, when the second factor is
an affine normal integral scheme with algebraically closed function field.
Source: Stacks Project, Tag 0F1I, final reduction; current blueprint lemma
`lem-kun-0f1i-normal` (blueprint: lem-kun-0f1i-normal).

Proof:
1. Write S' = Spec B. By lem-sc-integral-function-field-affine-fraction, its function
   field is Frac B. By lem-kun-algebra-union, B is the directed union of its finitely
   generated K-subalgebras B_i. Form pairs (i,g), with g nonzero, ordered by inclusion
   and invertibility in the later localization. By lem-kun-colim-of-localizations this
   is a nonempty filtered index and Frac B is the colimit of (B_i)_g.
2. Put S_j = Spec B_i and U_j = Spec (B_i)_g. The repeated diagram of B_i also has
   colimit B: any compatible cocone is defined on b at a stage containing b, independently
   of the choice by a common upper bound. By lem-weil-pbc-spec-colimit-limit the spectra
   have limits S' and Spec L. The fibre-product universal property def-pc-fibre-product
   constructs limits X times_K S' and X times_K Spec L of the product diagrams. The
   projections are the given maps. All transitions are affine by
   lem-weil-pbc-affine-morphism-permanence and stability under base change.
3. Localizing a finitely generated algebra remains finitely generated, by adjoining 1/g
   (def-weil-pbc-finite-type-algebra, def-weil-finite-type-morphism). Each U_j to S_j is
   a principal-open immersion by lem-weil-pbc-principal-localization-open-immersion,
   and affine by lem-weil-pbc-morphism-affine-schemes-affine, hence qcqs by
   lem-weil-pbc-affine-morphism-permanence.
4. Fix a divisor d of the positive n. Signed divisors give the same cyclic groups after
   taking absolute values. The constant sheaf Z/dZ is annihilated by n, hence has orders
   invertible in K by lem-kun-zn-sheaf-invertible-orders. The identifications of
   lem-kun-pullback-constant give compatible transition maps, and their colimit on
   Spec L is the constant sheaf again by def-weil-pbc-category-colimit.
5. Apply lem-kun-0f1h at every finite-type open-immersion square. With abelian-group
   coefficients, sk-def-exchange restricts this derived exchange to the bounded-below
   mate, and lem-kun-bc-map-on-cohomology identifies its homology with the canonical
   higher-direct-image base-change map, which is therefore an isomorphism.
6. For a fixed positive q apply lem-kun-0ezt to these four inverse systems, their affine
   transitions, qcqs open immersions, and compatible torsion constant sheaves. It gives
   an isomorphism from the inverse image of R^q(Spec L to S')_* Z/dZ to R^q h_* Z/dZ.
7. Algebraic closedness implies separable closedness (def-weil-algebraic-closure,
   def-kun-separably-closed). By the field-spectrum clause of lem-kun-0ezp, the first
   higher direct image is zero. Its inverse image is zero by
   prop-weil-pbc-inverse-image-exact. The isomorphism gives the required vanishing for
   every positive q and every divisor d of n. -/
theorem isZero_higherDirectImage_constant_genericFibre
    {K : Type u} [Field K] (n : invertibleTorsionOrders K)
    (X S' : Scheme.{u}) [X.Over (Spec (.of K))] [S'.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [IsAffine S'] [IsIntegral S'] (_hnormal : IsNormalScheme S')
    [IsAlgClosed S'.functionField] (q : ℤ) (_hq : 0 < q) (d : ℕ) (_hd : d ∣ n.val) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (pullback (X ↘ Spec (.of K)) (S' ↘ Spec (.of K))).smallEtaleTopology
        AddCommGrpCat.{u + 1}) q).obj
      ((lowerStar AddCommGrpCat.{u + 1}
        (pullback.fst
          (pullback.snd (X ↘ Spec (.of K)) (S' ↘ Spec (.of K)))
          (S'.fromSpecStalk (genericPoint S')))).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((constantSheaf
            (pullback (pullback.snd (X ↘ Spec (.of K)) (S' ↘ Spec (.of K)))
              (S'.fromSpecStalk (genericPoint S'))).smallEtaleTopology
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))))) :=
  sorry

end AlgebraicGeometry.Etale
