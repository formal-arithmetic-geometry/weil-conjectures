module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.FieldTheory.Separable
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.Paper.OrgogozoInductionData
import Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import WeilConjectures.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

/-! # An étale base neighbourhood making a nodal point rational and split

Source: Stacks Project, curves.tex, Tag 0CBY, first proof, second paragraph
(blueprint: lem-trf-nodal-family-split-point-neighbourhood).

The completed fibre equation uses the existing scalar-compatible ordinary-double-point
predicate. Finite type over the integers uses the canonical map to `Spec (ULift ℤ)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonsmooth point of a flat finitely presented nodal family between schemes of finite
 type over the integers becomes rational and split after an affine étale base neighbourhood.
 The residue-field extension is the one induced by the étale map. The point `z₁` is the
 unique point of the scheme-theoretic fibre lying over the displayed total-space point `x₁`.
 `Orgogozo.IsOrdinaryDoublePoint` requires the completion isomorphism to respect the
 structural field, both in the geometric hypothesis and in the split-fibre conclusion.

Source: Stacks Project, curves.tex, Tag 0CBY, first proof, second paragraph
(blueprint: lem-trf-nodal-family-split-point-neighbourhood).

Proof:
1. Form the fibre C over s₀ = f₀(x₀), with its point over x₀. Finite presentation implies
   finite type by lem-weil-pbc-lfp-affine-opens-finite-presentation and
   lem-weil-pbc-lft-affine-pairs. Finite type survives base change by
   lem-sfb-finite-type-composition-base-change. Associativity of base change identifies
   its geometric fibres with the given fibres. The base-change compatibility of the
   first-Fitting singular subscheme in lem-trf-nodal-family-fitting-singular shows that
   the point of C is nonsmooth.
2. Apply lem-trf-nodal-point-finite-separable-splitting to obtain a finite separable
   extension L/k and an L-rational split node over x₀. Realize L by an étale pointed
   neighbourhood U of S₀ using lem-weil-pbc-etale-neighbourhood-prescribed-residue-field.
3. Choose an affine finite-presentation chart V₁ around the chosen point of U. The
   restriction is étale by lem-a1-etale-open-restriction. Finite sets of generators for
   the chart over an affine chart of S₀, and for that chart over the integers, show V₁
   is of finite type over the integers (lem-weil-pbc-lft-affine-pairs). The residue-field
   isomorphism under open restriction (lem-weil-pbc-residue-field-point-naturality)
   identifies its residue field K with L as a k-algebra, so K/k is finite separable.
4. Base change to X₁ = X₀ ×_{S₀} V₁. Flatness and local finite presentation follow from
   lem-weil-pbc-flat-morphism-base-change and lem-weil-pbc-qcqs-morphism-permanence.
   By lem-weil-pbc-fibre-of-base-change its fibre at v₁ is C_K. On affine charts scalar
   transport sends b ⊗ l to b ⊗ α(l), where α : L ≃ K; this is compatible with restriction
   by lem-weil-pbc-fibre-product-affine-spectra. It transports the rational point and
   the completed equation. The induced local-ring isomorphism preserves maximal-ideal
   powers; coefficientwise α preserves uv, so the resulting equation is a K-algebra
   isomorphism of the completed fibre ring with K[[u,v]]/(uv).
5. Take x₁ to be the image of this point in X₁. Its projections are x₀ and v₁. The
   fibre-to-total-space residue map is an isomorphism by
   lem-weil-pbc-fibre-ring-residue-field-iso, so the structural map K → κ(x₁) is an
   isomorphism as well. This proves all the claimed clauses. -/
theorem exists_nodal_family_split_point_neighbourhood
    {X₀ S₀ : Scheme.{u}} (f₀ : X₀ ⟶ S₀)
    [Flat f₀] [LocallyOfFinitePresentation f₀] [QuasiCompact f₀] [QuasiSeparated f₀]
    [LocallyOfFiniteType (specULiftZIsTerminal.from X₀)]
    [QuasiCompact (specULiftZIsTerminal.from X₀)]
    [LocallyOfFiniteType (specULiftZIsTerminal.from S₀)]
    [QuasiCompact (specULiftZIsTerminal.from S₀)]
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S₀),
      (pullback (C := Scheme.{u}) f₀ g).IsPureDimension 1 ∧
        ∀ z : pullback (C := Scheme.{u}) f₀ g,
          (¬ ∃ U : (pullback (C := Scheme.{u}) f₀ g).Opens,
            z ∈ U ∧ Smooth (U.ι ≫ pullback.snd f₀ g)) →
          Orgogozo.IsOrdinaryDoublePoint (pullback.snd f₀ g) z)
    (x₀ : X₀) (hx₀ : ¬ ∃ U : X₀.Opens, x₀ ∈ U ∧ Smooth (U.ι ≫ f₀)) :
    ∃ (V₁ : Scheme.{u}) (e : V₁ ⟶ S₀) (v₁ : V₁)
      (x₁ : pullback (C := Scheme.{u}) f₀ e),
      IsAffine V₁ ∧ LocallyOfFiniteType (specULiftZIsTerminal.from V₁) ∧
        QuasiCompact (specULiftZIsTerminal.from V₁) ∧ Etale e ∧ e v₁ = f₀ x₀ ∧
        pullback.fst f₀ e x₁ = x₀ ∧ pullback.snd f₀ e x₁ = v₁ ∧
        (e.residueFieldMap v₁).hom.Finite ∧
        @Algebra.IsSeparable (S₀.residueField (e v₁)) (V₁.residueField v₁) _ _
          (e.residueFieldMap v₁).hom.toAlgebra ∧
        Flat (pullback.snd f₀ e) ∧ LocallyOfFinitePresentation (pullback.snd f₀ e) ∧
        Function.Bijective ((pullback.snd f₀ e).residueFieldMap x₁).hom ∧
        ∃ z₁ : (pullback.snd f₀ e).fiber v₁,
          (pullback.snd f₀ e).fiberι v₁ z₁ = x₁ ∧
          Orgogozo.IsOrdinaryDoublePoint
            ((pullback.snd f₀ e).fiberToSpecResidueField v₁) z₁ := by
  sorry

end AlgebraicGeometry
