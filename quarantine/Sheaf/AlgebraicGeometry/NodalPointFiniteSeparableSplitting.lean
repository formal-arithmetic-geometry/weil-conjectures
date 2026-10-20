/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.ZetaSeries
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.Paper.OrgogozoInductionData
import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion
import Sheaf.AlgebraicGeometry.RationalNodeQuadraticCompletion
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular

/-!
# Splitting a nodal point over a finite separable extension

Source: Stacks Project, curves.tex, Tags 0CBT, 0CBU and 0CBW, and the residue-field
paragraph of the first proof of Tag 0CBY
(blueprint: lem-trf-nodal-point-finite-separable-splitting).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonsmooth point on a geometrically nodal finite-type curve is closed with finite
separable residue field. After a further extension of degree at most two it has a rational
split lift. The geometric completed equations are ring isomorphisms; the split equation
in the conclusion respects the ground field, as specified by `Orgogozo.IsOrdinaryDoublePoint`.
Smoothness at a point means smoothness on some open neighbourhood, so no additional
finite-presentation instance is required in the statement.

Source: Stacks Project, curves.tex, Tags 0CBT, 0CBU, 0CBW and the residue-field paragraph
of the first proof of Tag 0CBY
(blueprint: lem-trf-nodal-point-finite-separable-splitting).

Proof:
1. The structure morphism is flat by lem-pc-flat-field and locally of finite presentation
   by pqf-lem-lft-fp-locnoeth, since a field is Noetherian. Apply
   lem-trf-nodal-family-fitting-singular: the first Fitting singular subscheme has precisely
   the nonsmooth support, is unramified over k, and commutes with arbitrary base change.
2. Apply lem-trf-unramified-over-field-local-criterion to this closed subscheme. Its points
   are closed with finite separable residue fields. The closed immersion preserves residue
   fields, so x is closed in C and F = kappa(x) is finite separable over k.
3. Rationalize x over F using its residue-point map. The resulting F-rational point z of
   D = C_F belongs to the base-changed singular subscheme. Its lift to an algebraic closure
   Omega of F is nonsmooth; the hypothesis supplies the completed equation Omega[[u,v]]/(uv).
   The affine fibre-product description is lem-weil-pbc-fibre-product-affine-spectra.
4. The rational point z is closed: evaluation on each affine neighbourhood surjects onto F.
   D is finite type. Apply lem-pc-dim-base-change to its affine charts, then
   lem-pc-dimension-affine-open-cover and lem-pc-scheme-dimension-local-rings. The geometric
   fibre is nonempty at the lifted z and pure of dimension one, so D has dimension one.
5. By lem-trf-rational-node-quadratic-completion, the completion at z is F[[u,v]]/(q) as an
   F-algebra, with q = a*u^2 + b*u*v + c*v^2 and discriminant b^2 - 4*a*c nonzero.
6. If a = 0, take K = F; then b is nonzero. Otherwise adjoin a root r of a*T^2+b*T+c
   only if necessary. An irreducible quadratic gives degree two. Its discriminant is
   nonzero, so this extension is separable, including in characteristic two, where its
   derivative is b. Every s+t*r satisfies a separable quadratic when t is nonzero.
7. If a = 0, use U = v, V = b*u+c*v, with inverse v = U, u = (V-c*U)/b.
   Otherwise set r2 = -b/a-r. Then q = a*(u-r*v)*(u-r2*v) and r differs from r2.
   Set U = a*(u-r*v), V = u-r2*v; the inverse is
   v = (U/a-V)/(r2-r), u = V+r2*v. These inverse linear substitutions act coefficientwise
   on power series and identify K[[u,v]]/(q) with K[[U,V]]/(U*V).
8. Apply the every-presentation clause of lem-trf-separable-closed-point-formal-presentation
   over F to the canonical K-rational lift of z, using the presentation in step 5 with
   n = 2 and relation q. Its completion is K[[u,v]]/(q) as a K-algebra; compose with step 7.
   The lift lies over x and its structural residue map is an isomorphism. Separability
   of K/k follows from lem-zl-separable-permanence. Products of finite bases show K/k is
   finite, while the chosen embedding F into K has degree at most two. -/
theorem nodal_point_finite_separable_splitting
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ι : k →+* Ω),
      (pullback f (Spec.map (CommRingCat.ofHom ι))).IsPureDimension 1 ∧
      ∀ y : pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom ι)),
        (¬ ∃ U : (pullback f (Spec.map (CommRingCat.ofHom ι))).Opens,
          y ∈ U ∧ Smooth (U.ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom ι)))) →
        Nonempty
          (AdicCompletion
            (IsLocalRing.maximalIdeal
              ((pullback f (Spec.map (CommRingCat.ofHom ι))).presheaf.stalk y))
            ((pullback f (Spec.map (CommRingCat.ofHom ι))).presheaf.stalk y) ≃+*
              Orgogozo.nodeRing Ω))
    (x : C) (hx : ¬ ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) :
    x ∈ closedPoints C ∧ (f.residueFieldAlgebraMap x).Finite ∧
      @Algebra.IsSeparable k (C.residueField x) _ _
        (f.residueFieldAlgebraMap x).toAlgebra ∧
      ∃ (K : Type u) (_ : Field K) (i : C.residueField x →+* K),
        (i.comp (f.residueFieldAlgebraMap x)).Finite ∧
        @Algebra.IsSeparable k K _ _ (i.comp (f.residueFieldAlgebraMap x)).toAlgebra ∧
        @Module.finrank (C.residueField x) K _ _ i.toAlgebra.toModule ≤ 2 ∧
        ∃ x' : pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom (i.comp (f.residueFieldAlgebraMap x)))),
          pullback.fst f
            (Spec.map (CommRingCat.ofHom (i.comp (f.residueFieldAlgebraMap x)))) x' = x ∧
          Function.Bijective
            (Scheme.Hom.residueFieldAlgebraMap (pullback.snd f
              (Spec.map (CommRingCat.ofHom (i.comp (f.residueFieldAlgebraMap x))))) x') ∧
          Orgogozo.IsOrdinaryDoublePoint
            (pullback.snd f
              (Spec.map (CommRingCat.ofHom (i.comp (f.residueFieldAlgebraMap x))))) x' := by
  sorry

end AlgebraicGeometry
