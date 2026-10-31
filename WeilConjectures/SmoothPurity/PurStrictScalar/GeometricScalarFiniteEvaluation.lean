/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport
import WeilConjectures.SmoothPurity.PurStrictScalar.NativeSupportFiniteEvaluation
import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarFiniteCoordinate

/-! # Finite evaluation of the geometric scalar mate

Source: Stacks 07A6, 0B56, 0D6E, 0E8I and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The geometric scalar mate on an E reduction evaluates to the finite mate.
This calculation stops before ramified reduction balancing; it uses no F reduction
calculus. Source: Stacks 07A6 (lemma-adjoint), 0B56
(equation-projection-formula-map), 0D6E, 0940 (section-derived-limits), and
sites-modules.tex 0E8I (lemma-j-shriek-and-tensor).
(blueprint: lem-pur-geometric-scalar-finite-evaluation).
Proof: first compare evaluation of supportModel with supportEvaluation. For its
proper part, use the identity-on-sections ordinary restriction square and the
whole-complex unit equations of systemProper and evalR. Transpose under the
finite geometric adjunction. The normalized counit makes both transposes equal,
so its Hom bijection identifies the two proper comparison maps. For the open
part, the systemOpen and evalJ comparisons are localizations of their ordinary
open-unit normalized comparisons. On the open their units are the identity;
outside it the extended modules are zero. Thus these comparisons agree after
finite coefficient restriction. Next apply the same adjunction calculation to
proper scalar extension. The tensor-unit normalized scalar adjunction identifies
its transpose with scalar extension of the proper counit, which is exactly the
finite properComparison. The ordinary open tensor comparison is the balancing
map on the open and zero outside, hence its localization is openComparison.
The finiteOrdinaryBalancing pure-tensor equation commutes with these unit and
counit maps: both routes take b tensor x to the same quotient coefficient tensor
x. Its universal cochain counit equation identifies the localized comparison
with finiteBalancing. Compose the proper equation with proper image of the open
equation. Naturality moves the input reductionEvaluation through these factors.
The source factors are sourceEvaluation; the target factors, in order, are
constantImageEvaluation, tensorEvaluation, reductionEvaluation, finiteBalancing
and positiveImageRestriction, namely scalarImageEvaluation. The surviving maps
are the two factors defining finiteTensorMap. Whole-diagram resolutions and
localization uniqueness extend the equation to every M. This uses equations of
mates, never faithfulness of derived evaluation. All exponents are positive;
the same unit calculation covers e=1, n=0, zero inputs and empty opens. -/
theorem geometricScalar_finiteEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n).map
        ((T l E F i Y).map ((supportModel l E c S).hom.app M) ≫
          (comparison l E F i c).app ((reduction l E X S).obj M)) ≫
        (scalarImageEvaluation l E F i c S e he hepos n).hom.app M =
      (sourceEvaluation l E F i c S e he hepos n).hom.app M ≫
        (positiveRestriction l F Y (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
          (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M)  := by
  let N := (pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
    (Nat.le_add_left 1 n) X)).obj M
  have hs := constantScalar_finiteCoordinate l E F i c e he hepos n
    ((reduction l E X S).obj M) N ((reductionEvaluation l E X S n).app M)
  have ht := (tensorEvaluation l E F i Y n).hom.naturality
    ((supportModel l E c S).hom.app M)
  have hn := nativeSupport_finiteEvaluation l E c S M n
  have hf : (PurCompactSupport.comparison
      (PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)) c).app N =
      PurCompactSupport.finiteTensorMap l E F i e he hepos n c M :=
    PurCompactSupport.comparison_factorization _ c N
  simp only [Functor.comp_map] at ht
  simp only [Iso.app_hom, Functor.comp_obj] at hs
  simp only [scalarImageEvaluation, sourceEvaluation, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  erw [hs]
  erw [reassoc_of% ht]
  simp only [← Functor.map_comp_assoc]
  erw [hn]
  erw [hf]

end WeilConjectures.PurStrictScalar
