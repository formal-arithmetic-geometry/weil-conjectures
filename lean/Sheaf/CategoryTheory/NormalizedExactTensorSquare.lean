/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.CategoryTheory.ConstantModuleDerivedComparisonData
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat

/-! # Descent of an exact tensor square with representative normalizations

Source: Stacks Project, Cohomology on Sites, Tag 07A4, and Derived Categories,
Tags 0FPQ and 0FPT; resolving-localization argument.
(blueprint: lem-sfb-normalized-exact-tensor-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe a b c e ha hb hc he wa wb wc we
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.ConstantModuleDerivedProjection

/-- Localization of a commuting ordinary tensor square retains its tensor equation.
Source: Stacks Tags 07A4, 0FPQ and 0FPT; steps 2 and 3 of
`lem-sfb-constant-module-tensor-square-descent`.
(blueprint: lem-sfb-normalized-exact-tensor-square).

Proof: choose a functorial flat resolution for each of the two source inputs. Its
terms are flat and it is K-flat. Exactness and flat preservation show that its images
under L, S, and their two composites are flat-term K-flat resolutions. On these models,
precompose the proposed equation with L-derived followed by T-derived applied to the
source localization tensorator, and postcompose with the tensor of the two comparison
maps to the chosen H-complex models, followed by the H-localization tensorator.
Every map cancelled here is invertible: these are exact-functor factorization maps,
the specified natural isomorphism i, and the localization tensorators on K-flat pairs.
Substitute the four TensorNormalization equations and the LeftLocalizationCondition
at P, Q and their signed tensor total. Naturality moves the exact-functor factors past
the total comparison maps. Both composites now equal Q_H of the corresponding signed
total ordinary tensor square. On each bidegree summand this is exactly ho at P^p,Q^q;
additivity preserves the differential signs and coproduct preservation assembles the
summands. Hence the model square commutes. Finally, naturality in each derived variable
transports the equality along the two resolution isomorphisms to arbitrary unbounded
inputs. Neither the ordinary tensorators nor the given derived structures are changed:
only their four specified normalizations are used. In particular the assertion is valid
for independent localization universes, arbitrary exact flat-preserving functors, and
the zero categories. -/
theorem normalized_exact_tensor_square
    {B : Type a} [Category.{ha} B] [Abelian B] [IsGrothendieckAbelian.{ha} B]
    [HasColimitsOfSize.{0, 0} B] [MonoidalCategory B] [MonoidalClosed B]
    [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
    [HasDerivedCategory.{wa} B]
    {E : Type b} [Category.{hb} E] [Abelian E] [IsGrothendieckAbelian.{hb} E]
    [HasColimitsOfSize.{0, 0} E] [MonoidalCategory E] [MonoidalClosed E]
    [MonoidalPreadditive E] [BraidedCategory E] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wb} E]
    {F : Type c} [Category.{hc} F] [Abelian F] [IsGrothendieckAbelian.{hc} F]
    [HasColimitsOfSize.{0, 0} F] [MonoidalCategory F] [MonoidalClosed F]
    [MonoidalPreadditive F] [BraidedCategory F] [Abelian.HasFunctorialFlatResolution F]
    [HasDerivedCategory.{wc} F]
    {H : Type e} [Category.{he} H] [Abelian H] [IsGrothendieckAbelian.{he} H]
    [HasColimitsOfSize.{0, 0} H] [MonoidalCategory H] [MonoidalClosed H]
    [MonoidalPreadditive H] [BraidedCategory H] [Abelian.HasFunctorialFlatResolution H]
    [HasDerivedCategory.{we} H]
    (L : B ⥤ E) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesColimitsOfSize.{0, 0} L] [L.PreservesFlat]
    (L' : F ⥤ H) [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesColimitsOfSize.{0, 0} L'] [L'.PreservesFlat]
    (S : B ⥤ F) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesColimitsOfSize.{0, 0} S] [S.PreservesFlat]
    (T : E ⥤ H) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesColimitsOfSize.{0, 0} T] [T.PreservesFlat]
    (mL : L.Monoidal) (mL' : L'.Monoidal) (mS : S.Monoidal) (mT : T.Monoidal)
    (nL : L.mapDerivedCategory.Monoidal) (nL' : L'.mapDerivedCategory.Monoidal)
    (nS : S.mapDerivedCategory.Monoidal) (nT : T.mapDerivedCategory.Monoidal)
    (o : L ⋙ T ≅ S ⋙ L')
    (ho : TensorSquare L L' S T mL mL' mS mT o)
    (hL : TensorNormalization B E L mL nL)
    (hL' : TensorNormalization F H L' mL' nL')
    (hS : TensorNormalization B F S mS nS)
    (hT : TensorNormalization E H T mT nT)
    (i : L.mapDerivedCategory ⋙ T.mapDerivedCategory ≅
      S.mapDerivedCategory ⋙ L'.mapDerivedCategory)
    (hi : LeftLocalizationCondition L L' S T o i) :
    TensorSquare L.mapDerivedCategory L'.mapDerivedCategory S.mapDerivedCategory
      T.mapDerivedCategory nL nL' nS nT i := by sorry

end CategoryTheory.ConstantModuleDerivedProjection
