module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic
public import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
public import Sheaf.AlgebraicGeometry.EquidimensionalOpenLocalDimension
public import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
public import Sheaf.RingTheory.PresentationFittingIdeal
public import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
public import Sheaf.TraceFormula.CompleteIntersectionFibresLimitDescent
public import Sheaf.TraceFormula.PureRelativeDimensionFiniteStage
public import Sheaf.TraceFormula.UnramifiedLimitDescent
public import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
public import WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

@[expose] public section

/-! # Finite-type approximation of an affine nodal family

Source: Stacks Project, Curves, Tags 0C5F and 0CBY
(blueprint: lem-trf-nodal-family-noetherian-approximation).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Finite-type approximation of a flat, finitely presented family of nodal curves.

Source: Stacks Project, Curves, Tags 0C5F and 0CBY
(blueprint: lem-trf-nodal-family-noetherian-approximation).

The proof is the affine Noetherian approximation argument of Tag 0CBY, with the
nodal fibre condition descended by the eight steps in the node's proof plan:

1. Choose affine neighbourhoods `U` of `x` and `V` of `f x`, with `U` inside
   the inverse image of `V`; flatness, finite presentation, and the fibrewise
   hypotheses restrict to this pair.
2. Write `V` as an inverse limit of affine schemes of finite type over `ℤ` and
   spread out the affine morphism and the Cartesian square to one finite stage.
3. The geometric fibres of the restricted morphism are local complete
   intersections by the nodal curve criterion; generic limit descent gives a
   finite stage that is flat, locally finitely presented, and has such fibres.
4. Compare ordinary and geometric fibre dimensions after field extension and
   descend purity of relative dimension one to a finite stage.
5. Form the first-Fitting singular subscheme. Its defining Fitting ideal and
   hence the singular subscheme commute with every base change.
6. The singular subscheme is of finite type and its map to the base is
   unramified in the limit; unramifiedness descends to a finite stage.
7. The nodal curve criterion applied to the local-complete-intersection fibres
   and the unramified singular locus gives the completed node equation at every
   nonsmooth point of the descended family.
8. Choose that finite stage as `(X₀,S₀,f₀)`. The Cartesian identifications carry
   `x` to a nonsmooth point `x₀`, and all the required properties follow.
-/
theorem nodal_family_noetherian_approximation
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hflat : Flat f)
    (hfp : LocallyOfFinitePresentation f)
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ S),
      IsEmpty (pullback (C := Scheme.{u}) f y) ∨
        (Scheme.IsPureDimension (pullback (C := Scheme.{u}) f y) 1 ∧
          ∀ z : pullback (C := Scheme.{u}) f y,
            (¬ ∃ U : (pullback (C := Scheme.{u}) f y).Opens,
              z ∈ U ∧ Smooth (U.ι ≫ pullback.snd f y)) →
              Nonempty
                (AdicCompletion
                  (IsLocalRing.maximalIdeal
                    ((pullback (C := Scheme.{u}) f y).presheaf.stalk z))
                  ((pullback (C := Scheme.{u}) f y).presheaf.stalk z) ≃+*
                  (MvPowerSeries (Fin 2) Ω ⧸
                    Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}))))
    (x : X)
    (hx : ¬ ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U)
      (V : S.Opens) (_ : IsAffineOpen V) (_ : f x ∈ V)
      (hUV : U ≤ f ⁻¹ᵁ V)
      (X₀ S₀ : Scheme.{u})
      (f₀ : X₀ ⟶ S₀)
      (aX : X₀ ⟶ Spec (.of (ULift.{u} ℤ)))
      (aS : S₀ ⟶ Spec (.of (ULift.{u} ℤ)))
      (s : V.toScheme ⟶ S₀)
      (h : U.toScheme ⟶ V.toScheme)
      (i : U.toScheme ≅ pullback f₀ s),
      h ≫ V.ι = U.ι ≫ f ∧
      LocallyOfFiniteType aX ∧ QuasiCompact aX ∧ QuasiSeparated aX ∧
      LocallyOfFiniteType aS ∧ QuasiCompact aS ∧ QuasiSeparated aS ∧
      Flat f₀ ∧ LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧
      QuasiSeparated f₀ ∧ LocallyOfFiniteType f₀ ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S₀),
        IsEmpty (pullback (C := Scheme.{u}) f₀ y) ∨
          (Scheme.IsPureDimension (pullback (C := Scheme.{u}) f₀ y) 1 ∧
            ∀ z : pullback (C := Scheme.{u}) f₀ y,
              (¬ ∃ W : (pullback (C := Scheme.{u}) f₀ y).Opens,
                z ∈ W ∧ Smooth (W.ι ≫ pullback.snd f₀ y)) →
                Nonempty
                  (AdicCompletion
                    (IsLocalRing.maximalIdeal
                      ((pullback (C := Scheme.{u}) f₀ y).presheaf.stalk z))
                    ((pullback (C := Scheme.{u}) f₀ y).presheaf.stalk z) ≃+*
                    (MvPowerSeries (Fin 2) Ω ⧸
                      Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                        (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))) ∧
      ¬ ∃ W : X₀.Opens,
        (pullback.fst f₀ s) (i.hom ⟨x, ‹x ∈ U›⟩) ∈ W ∧
          Smooth (W.ι ≫ f₀) := by
  sorry

end AlgebraicGeometry
