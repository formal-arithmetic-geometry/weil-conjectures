/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.ZetaSeries
public import Mathlib.FieldTheory.Separable
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.RingTheory.GeometricFieldStalkDescent
import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import Sheaf.TraceFormula.CompletionLocalCompleteIntersection
import Sheaf.TraceFormula.FormalJacobianQuadraticCriterion

/-!
# Pointwise nodal criterion using the first Fitting ideal

Source: Stacks Project, curves.tex, Tags 0C4D, 0C4E and 0C4C
(blueprint: lem-trf-nodal-point-local-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- At a closed point of a pure one-dimensional locally finite type scheme over a field,
the geometric nodal completion condition is equivalent to finite separability of the
residue field, an affine local-complete-intersection neighbourhood, and equality of the
first Fitting stalk ideal with the maximal ideal. The latter is precisely the condition
that the singular-subscheme local ring is the residue field via the residue map.
Source: Stacks Project, curves.tex, Tags 0C4D, 0C4E and 0C4C
(blueprint: lem-trf-nodal-point-local-criterion).

Proof plan:
1. Choose an affine neighbourhood and use `lem-weil-pbc-lft-affine-pairs` for finite type.
   `lem-trf-geometric-field-stalk-descent` gives finite closed residue fields and rational
   geometric lifts. The definition of the first Fitting subscheme identifies its stalk
   with the local ring modulo the localized first Fitting ideal.
2. For a nodal completion, `lem-trf-separable-closed-point-formal-presentation` gives the
   formal differential presentation. Apply the ring-isomorphism clause of
   `lem-trf-formal-jacobian-quadratic-criterion` to the model `uv`, whose discriminant is
   one in every characteristic. Obtain depth one and the maximal Jacobian-minor ideal;
   `lem-trf-fitting-ideal-independence-base-change` identifies it with the Fitting ideal.
3. Faithful flatness of local completion and faithful-flat ideal contraction descend the
   ideal equality to the geometric local ring. Finite generation of differentials and
   their base-change and localization comparisons identify this with the geometric
   first-Fitting singular subscheme (`lem-weil-pbc-kahler-differentials-base-change` and
   `lem-weil-pbc-kahler-differentials-localization`).
4. Apply `lem-trf-geometric-field-stalk-descent` to the affine singular quotient to
   descend its field stalk and obtain finite separability of the residue field.
5. The separable formal-presentation lemma gives a flat local geometric extension with
   field closed fibre. Apply `lem-weil-pbc-flat-local-depth-formula` to completion and
   geometric extension; the closed-fibre depths are zero, hence all local depths are one.
6. The formal Jacobian criterion now gives a nondegenerate binary quadratic hypersurface
   presentation of the original completion. Its nonzero equation is a regular sequence
   of length one. `lem-trf-completion-local-complete-intersection` gives a principal affine
   neighbourhood that is a local complete intersection over the base field.
7. Conversely, pure dimension gives local dimension one by
   `lem-sbc-equidimensional-open-local-dimension` and
   `lem-weil-pbc-closed-point-dimension-local-ring`. The LCI depth conclusion of
   `lem-trf-completion-local-complete-intersection` gives local depth one.
8. The flat-local depth formula carries this to completion; the formal presentation and
   Fitting base change give the maximal Jacobian ideal. The formal Jacobian criterion
   yields a nondegenerate binary quadratic presentation over the residue field.
9. Take a geometric lift using `lem-trf-geometric-field-stalk-descent` and extend the
   presentation using `lem-trf-separable-closed-point-formal-presentation`. Over the
   algebraic closure the quadratic splits into independent linear factors, also in
   characteristic two; changing coordinates identifies its quotient with `Ω[[u,v]]/(uv)`.
-/
theorem nodalPoint_iff_separable_lci_firstFitting
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hpure : C.IsPureDimension 1)
    (x : C) (hx : x ∈ closedPoints C)
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] :
    (∃ y : pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) y = x ∧
      Nonempty
        (AdicCompletion
          (IsLocalRing.maximalIdeal
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).presheaf.stalk y))
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).presheaf.stalk y) ≃+*
          (MvPowerSeries (Fin 2) Ω ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}))) ↔
    (f.residueFieldAlgebraMap x).Finite ∧
      @Algebra.IsSeparable k (C.residueField x) _ _
        (f.residueFieldAlgebraMap x).toAlgebra ∧
      ∃ (U : C.affineOpens) (hxU : x ∈ U.1)
        (hfg : @Algebra.FiniteType k Γ(C, U.1) _ _
          ((f.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra),
        @Algebra.IsLocalCompleteIntersection k Γ(C, U.1) _ _
          ((f.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
          hfg ∧
        ((Scheme.firstFittingIdealSheaf f).ideal U).map (C.presheaf.germ U.1 x hxU).hom =
          IsLocalRing.maximalIdeal (C.presheaf.stalk x) := by
  sorry

end AlgebraicGeometry
