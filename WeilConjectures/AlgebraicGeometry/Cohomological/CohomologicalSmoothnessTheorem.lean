/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessComparison
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorCompositionEquation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.ShiftedLineSiteInverse.ShiftedLineSiteInverse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# Cohomological smoothness for smooth morphisms

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-cohsm/
thm-pur-cohomological-smoothness.proof.md (blueprint: thm-pur-cohomological-smoothness).

This statement records the orientation-free tensor, invertibility, arbitrary base-change,
and composition clauses in the canonical pro-etale comparison coordinates.
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

section

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

namespace AlgebraicGeometry.Etale.CanonicalSmoothBaseChange
open scoped CategoryTheory.Functor

private lemma unit_tensor_base_change
    {Cx Cy Cx' Cy' : Type*} [Category* Cx] [Category* Cy]
    [Category* Cx'] [Category* Cy']
    [MonoidalCategory Cx] [MonoidalCategory Cy]
    [MonoidalCategory Cx'] [MonoidalCategory Cy']
    (F R : Cy ⥤ Cx) (F' R' : Cy' ⥤ Cx') (Ga : Cx ⥤ Cx') (Gb : Cy ⥤ Cy')
    (τ : ∀ M N : Cy, R.obj M ⊗ F.obj N ⟶ R.obj (M ⊗ N))
    (τ' : ∀ M N : Cy', R'.obj M ⊗ F'.obj N ⟶ R'.obj (M ⊗ N))
    (β : R ⋙ Ga ⟶ Gb ⋙ R')
    (δa : ∀ M N : Cx, Ga.obj (M ⊗ N) ⟶ Ga.obj M ⊗ Ga.obj N)
    (δb : ∀ M N : Cy, Gb.obj (M ⊗ N) ⟶ Gb.obj M ⊗ Gb.obj N)
    (κ : ∀ N : Cy, Ga.obj (F.obj N) ⟶ F'.obj (Gb.obj N))
    (e : Gb.obj (𝟙_ Cy) ⟶ 𝟙_ Cy')
    (hτ : ∀ M N : Cy,
      Ga.map (τ M N) ≫ β.app (M ⊗ N) ≫ R'.map (δb M N) =
        δa (R.obj M) (F.obj N) ≫ β.app M ▷ Ga.obj (F.obj N) ≫
          R'.obj (Gb.obj M) ◁ κ N ≫ τ' (Gb.obj M) (Gb.obj N))
    (hτ' : ∀ {M M' : Cy'} (φ : M ⟶ M') (N : Cy'),
      R'.map φ ▷ F'.obj N ≫ τ' M' N = τ' M N ≫ R'.map (φ ▷ N))
    (he : ∀ N : Cy, δb (𝟙_ Cy) N ≫ e ▷ Gb.obj N ≫ (λ_ (Gb.obj N)).hom =
      Gb.map (λ_ N).hom) (N : Cy) :
    Ga.map (τ (𝟙_ Cy) N ≫ R.map (λ_ N).hom) ≫ β.app N =
      δa (R.obj (𝟙_ Cy)) (F.obj N) ≫
        (β.app (𝟙_ Cy) ≫ R'.map e) ▷ Ga.obj (F.obj N) ≫
        R'.obj (𝟙_ Cy') ◁ κ N ≫ τ' (𝟙_ Cy') (Gb.obj N) ≫
        R'.map (λ_ (Gb.obj N)).hom := by
  rw [Ga.map_comp, Category.assoc]
  erw [β.naturality]
  change Ga.map (τ (𝟙_ Cy) N) ≫ β.app (𝟙_ Cy ⊗ N) ≫
    R'.map (Gb.map (λ_ N).hom) = _
  rw [← he, R'.map_comp, R'.map_comp]
  rw [reassoc_of% (hτ (𝟙_ Cy) N)]
  rw [← reassoc_of% (hτ' e (Gb.obj N))]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, whisker_exchange_assoc]

private lemma exceptional_tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {a : X' ⟶ X} {g : S' ⟶ S}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f g) (M N : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.map
        (rightDerivedUpperShriekTensorMap f M N) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq).app
        (M ⊗ N) ≫
      (rightDerivedUpperShriek A f').map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g M N).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a
      ((rightDerivedUpperShriek A f).obj M)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)).hom ≫
      (rightDerivedUpperShriekBaseChangeMap A sq).app M ▷
        ((upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)) ≫
      ((rightDerivedUpperShriek A f').obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)) ◁
          (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
            sq.toCommSq N) ≫
      rightDerivedUpperShriekTensorMap f'
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap A
    sq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  exact Adjunction.projectionTensorMap_mateEquiv
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A f')
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) f').app M).app N)
    (fun φ N ↦ NatTrans.congr_app
      ((projectionMap (ModuleCat.{u + 1} A) f').naturality φ) N)
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
      a M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
      sq.toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap A sq)
    (inv (rightDerivedLowerShriekBaseChangeMap A sq))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N

private lemma dualizing_tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {a : X' ⟶ X} {g : S' ⟶ S}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f g) (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.map
        (dualizingComplexTensorMap A f K) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq).app K =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a
      (dualizingComplex A f)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).hom ≫
      (dualizingComplexBaseChangeMap A sq) ▷
        ((upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) ≫
      (dualizingComplex A f') ◁
        (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
          sq.toCommSq K) ≫
      dualizingComplexTensorMap A f'
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) := by
  exact unit_tensor_base_change
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    (rightDerivedUpperShriek A f)
    (upperStar (ModuleCat.{u + 1} A) f').leftDerivedFunctor
    (rightDerivedUpperShriek A f')
    (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    (rightDerivedUpperShriekTensorMap f)
    (rightDerivedUpperShriekTensorMap f')
    (rightDerivedUpperShriekBaseChangeMap A sq)
    (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
      a M N).hom)
    (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g M N).hom)
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
      sq.toCommSq N)
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom
    (exceptional_tensor_base_change A sq)
    (Adjunction.projectionTensorMap_naturality_left
      (rightDerivedUpperShriekAdjunction A f')
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) f').app M).app N)
      (fun φ N ↦ NatTrans.congr_app
      ((projectionMap (ModuleCat.{u + 1} A) f').naturality φ) N))
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom (ModuleCat.{u + 1} A) g) K

end AlgebraicGeometry.Etale.CanonicalSmoothBaseChange

namespace AlgebraicGeometry.ProEtale

/-- Equality of the canonical tensor maps under base change, in comparison coordinates.
The left side is u*θ followed by β_K. The right side uses the monoidal pullback
comparison, b = β_Λ with its unit normalization, the pullback-square comparison,
and θ' at v*K. Applying ν* to the entire equation retains every comparison arrow.
Source: blueprint thm-pur-cohomological-smoothness, clause 3, proof Step 7
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def smoothTensorBaseChangeCoherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {v : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback u' f' f v)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Prop :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) u').leftDerivedFunctor.map
          (Etale.dualizingComplexTensorMap Λ f K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap Λ sq).app K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) u'
          (Etale.dualizingComplex Λ f)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).hom ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X').map
          (Etale.dualizingComplexBaseChangeMap Λ sq)).app _ ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X').obj
          (Etale.dualizingComplex Λ f')).map
          (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq K) ≫
        Etale.dualizingComplexTensorMap Λ f'
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) v).leftDerivedFunctor.obj K))

/-- The tensor formula under composition: q is invertible and the two specified
arrows agree for every representative of a pro-etale Dctf input. The right side
first reassociates, uses pullback composition and monoidality, pulls back θ_g,
and applies θ_f at g!K. The left side uses q, θ_fg and the exceptional comparison.
Source: blueprint thm-pur-cohomological-smoothness, clause 4, proof Steps 9--10
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def smoothTensorCompositionCoherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] : Prop :=
  IsIso ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
    (smoothDualizingCompMap Λ f g)) ∧
  ∀ K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategory.obj K) →
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).map
          (smoothDualizingCompMap Λ f g)).app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ g)).leftDerivedFunctor.obj K) ≫
        Etale.dualizingComplexTensorMap Λ (f ≫ g) K ≫
        (smoothExceptionalCompIso Λ f g).hom.app K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      ((Etale.derivedTensorAssociator (ModuleCat.{u + 1} Λ) X
          (Etale.dualizingComplex Λ f)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
            (Etale.dualizingComplex Λ g))
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ g)).leftDerivedFunctor.obj K)).hom ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          (Etale.dualizingComplex Λ f)).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj
                (Etale.dualizingComplex Λ g))).map
              ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).hom.app K) ≫
            (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f
              (Etale.dualizingComplex Λ g)
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj K)).inv ≫
            (Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.map
              (Etale.dualizingComplexTensorMap Λ g K)) ≫
        Etale.dualizingComplexTensorMap Λ f
          ((Etale.rightDerivedUpperShriek Λ g).obj K))

/-- Arbitrary finite-type base changes in the fixed purity setting, with the
base-changed compactification and every representative of a pro-etale Dctf input.
Source: blueprint thm-pur-cohomological-smoothness, clause 3
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def comparedSmoothTensorBaseChangeClause
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] : Prop :=
  ∀ (X' Y' : Scheme.{u}) [X'.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    [u'.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))] (sq : IsPullback u' f' f v),
    letI := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
    letI : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    ∀ K : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K) →
      smoothTensorBaseChangeCoherence P.Coefficient sq K

/-- The base-change equation with the same canonical compactification as the
recorded cohomological-smoothness definition. Nagata supplies it internally.
Source: blueprint thm-pur-cohomological-smoothness, clause 3
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def comparedSmoothBaseChangeCoherence
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : Prop :=
  letI := (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  comparedSmoothTensorBaseChangeClause P f

/-- Composition coherence with the canonical Nagata compactifications used by
comparedDualizing; the induced comparison is constructed above from their triangle.
Source: blueprint thm-pur-cohomological-smoothness, clause 4
(blueprint: thm-pur-cohomological-smoothness). -/
noncomputable def comparedSmoothCompositionCoherence
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))] [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] : Prop :=
  letI := (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.comparedCompactification g (Z ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.comparedCompactification (f ≫ g) (Z ↘ Spec (.of P.field.k))).hasCompactification
  smoothTensorCompositionCoherence P.Coefficient f g

/-- Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/thm-pur-cohomological-smoothness.proof.md, both paragraphs;
DAG thm-pur-cohomological-smoothness, proof Steps 1--10
(blueprint: thm-pur-cohomological-smoothness).

The four orientation-free assertions for smooth separated f: the canonical tensor
formula, invertibility with a Dctf inverse, arbitrary base change including equality
of tensor maps, and equality of tensor maps under exceptional composition.

Proof, following the ten DAG steps:

1. Work at A = A_(E,n). Finite-type k-schemes are Noetherian
(lem-weil-pbc-finite-type-over-noetherian). Nagata compactifies f; the compactification
is finite-dimensional by lem-kun-dimension-finite-type, with bound zero allowed when
empty. The coefficient quotient is finite and annihilated by l^n, which is invertible
on k since l ≠ p. These verify the hypotheses of thm-asd-smooth-tensor and
thm-sf-ambient-adjoint-class. The ordinary affine-space adjunction and historical
Kummer normalization are cor-amb-affine-space-adjunction and
prop-pur-affine-line-orientation-uniqueness; neither chooses an orientation here.

2. Write V_T = nu_T*. By lem-sf-proetale-constructible-origin choose a bounded
constructible etale H representing K. The unit of thm-weil-pbc-site-comparison
identifies Rnu_* V_Y H with H. The exceptional defining formula then identifies
f!K with V_X f×H and omega_f with V_X W_f, W_f = f×A_Y. Transport the etale counit
through the Hom bijection of thm-sf-ambient-adjoint-class and the compact-support
comparison C of lem-sf-class-compact-support-comparison. Its formula is
ε^P_(V_Y H) = V_Y(ε^F_H) composed with C_(f×H): both counits transpose the same
identity. Naturality makes this independent of the etale antecedent.

3. Apply thm-asd-smooth-tensor: W_f = L[2d] for a locally constant free rank-one
sheaf L, and the canonical theta is invertible. It is the specified inverse
projection/counit transpose, not an arbitrary isomorphism. No trivialization or
identification of L with a Tate twist is chosen.

4. Construct the inverse L^vee[-2d] using def-pur-sheaf-hom. On a trivializing cover
the evaluations are multiplication A tensor A to A with inverse a maps to 1 tensor a.
Their isomorphy follows from lemma-weil-pbc-geometric-stalk-conservative. Both lines
are flat because tensor by a trivial line preserves injections locally; both are
constructible. Their derived evaluations cancel the opposite shifts. Transport by
V_X and lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The pulled-back lines
remain flat and constructible, so the inverse is Dctf as required by the definition.

5. lem-sf-comparison-tor-amplitude reflects the finite Tor interval of K to H.
The line description makes W_f bounded constructible. Apply
lem-pur-projection-comparison-etale-origin to W_f and H: its equation identifies
the actual projection maps through C. Use lem-weil-pbc-comparison-pullback and the
monoidal comparison to identify the tensor sources. Finite Tor is used to keep
these comparisons within their bounded-below domains.

6. Substitute that projection equation and Step 2's counit equation into the
transpose of V_X theta_(f,H). It becomes inverse PF followed by 1 tensor ε and
the unit constraint. fix-prop-projection-formula makes PF invertible here. Tensor
symmetry matches the source order in def-pur-co-smoothness. Injectivity of the
restricted Hom bijection identifies the transported map with the specified
pro-etale theta, proving its isomorphy naturally in K.

7. lem-pur-smb-extraordinary supplies β_K for every Cartesian square in the fixed
setting. At the coefficient unit, the exact constant pullback and unit constraint
give b. prop-asd-smooth-base-change gives the etale equality between u*theta followed
by β_K and theta' following 1 tensor b. Realize it using the pullback and tensor
comparisons of Step 5. thm-cbc-finite-level-proetale identifies the compact-support
exchange; Step 2 identifies both counits. Transposing both exchanges gives the same
v*ε composed with inverse Ex_!, so the realized β is the specified pro-etale one.
Step 6 identifies the two thetas. This proves exactly smoothTensorBaseChangeCoherence,
including all monoidal, square and unit comparisons, without a condition on v.

8. Steps 4, 6 and 7 prove the three clauses of IsCohomologicallySmoothCompared.
Apply the same argument separately to g. lem-pur-co-smooth-composition supplies
the object formula, but equality of canonical tensor maps still needs Steps 9--10.

9. thm-sf-comp-composition and the restricted Hom bijections identify (fg)! with
f!g! by pasting adjunctions. The canonical compact-support comparison is constructed
by compatible compactifications and common refinements, as in smoothCompactSupportCompIso.
Its mate is smoothExceptionalCompIso, with pasted counit ε_g composed with g_!ε_f
by lem-weil-pbc-mate-pasting. The map q is theta_(f,W_g) followed by c_A inverse,
exactly smoothDualizingCompMap. Step 4 makes W_g Dctf, so q is invertible by Step 6.
For Dctf K, the exceptional constructible and Tor preservation gives g!K Dctf too.

10. Apply lem-pur-composite-tensor-transpose to these Hom bijections. Strong
monoidality is lem-pur-derived-pullback-tensor-iso; the projection maps are those of
def-exchange-projection, their coefficient/unit coherence is
lem-pur-projection-formula-coefficient-coherence, and their invertibility is
fix-prop-projection-formula. K, W_g and g!K are in the required finite Tor domains.
The tensor inputs have bounded-below etale-origin witnesses, and compact support
preserves bounded constructibility by prop-finite-compact-support-constructibility
and etale origin by thm-sf-comp-composition. Thus the restricted transposes are
available. The two inverse transposes are the same inverse projection followed by
the same two counits in adjunction order. Injectivity gives the displayed equality
in smoothTensorCompositionCoherence, with its associator, monoidal pullback and
pullback-composition maps. Apply V_X to obtain the pro-etale equation; symmetry
recovers the source's pullback-first ordering. No ambient pro-etale adjunction is used.
-/
theorem isCohomologicallySmooth_of_smooth
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f]
    [LocallyOfFiniteType f]
    [QuasiCompact f]
    (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    IsCohomologicallySmoothCompared P f ∧
      comparedSmoothBaseChangeCoherence P f ∧
      ∀ {Z : Scheme.{u}}
        [Z.Over (Spec (.of P.field.k))]
        [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
        [QuasiCompact (Z ↘ Spec (.of P.field.k))]
        (g : Y ⟶ Z)
        [g.IsOver (Spec (.of P.field.k))]
        [IsSeparated g]
        [LocallyOfFiniteType g]
        [QuasiCompact g]
        (e : ℕ)
        [SmoothOfRelativeDimension e g],
        comparedSmoothCompositionCoherence P f g  := by
  let : HasInvertibleExponent P.Coefficient X :=
    P.finiteComparedInvertibleExponent (X ↘ Spec (.of P.field.k))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  let : HasCompactification f :=
    (P.comparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  obtain ⟨L, hL, hs, ⟨eL⟩, hTensor⟩ :=
    Etale.exists_dualizingComplex_iso_and_tensor P.Coefficient f d
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have := hL
    have hω := Etale.DerivedCategory.isInvertible.of_iso eL.symm
      (Etale.isInvertible_shift_singleFunctor_obj_of_isLocallyConstantSheaf L hs
        (2 * (d : ℤ)))
    obtain ⟨M, ⟨a⟩, ⟨b⟩⟩ := hω
    let V := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    let a' : ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
        (V.obj (Etale.dualizingComplex P.Coefficient f))).obj
          (V.obj M) ≅ 𝟙_ _ :=
      (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) _).symm.app M ≪≫
      V.mapIso a ≪≫ ShiftedLineSiteInverse.unitComparison _ X
    let b' : ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj
        (V.obj M)).obj
          (V.obj (Etale.dualizingComplex P.Coefficient f)) ≅ 𝟙_ _ :=
      (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) M).symm.app _ ≪≫
      V.mapIso b ≪≫ ShiftedLineSiteInverse.unitComparison _ X
    let : IsNoetherian X :=
      { toIsLocallyNoetherian :=
          LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
        toCompactSpace :=
          QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k)) }
    exact ⟨V.obj M, DerivedCategory.constructibleFiniteTor_of_isDualizable P.Coefficient
      (isDualizable_of_tensorIso b' a'), ⟨a'⟩, ⟨b'⟩⟩
  · intro K _hK
    have := hTensor K
    infer_instance
  · intro X' Y' _ _ _ _ _ _ u' f' v _ _ _ sq
    let := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
    let : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq
      inferInstance
    have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
      P.Coefficient f d sq
    have := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).mpr
      (by infer_instance)
    infer_instance
  · intro X' Y' _ _ _ _ _ _ u' f' v _ _ _ sq K _hK
    let := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
    let : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq
      inferInstance
    apply congrArg ((comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map)
    simpa only [Etale.derivedTensor, curriedTensor] using
      Etale.CanonicalSmoothBaseChange.dualizing_tensor_base_change P.Coefficient sq K
  · intro Z _ _ _ g _ _ _ _ e _
    let : HasCompactification g :=
      (P.comparedCompactification g (Z ↘ Spec (.of P.field.k))).hasCompactification
    let : HasCompactification (f ≫ g) :=
      (P.comparedCompactification (f ≫ g) (Z ↘ Spec (.of P.field.k))).hasCompactification
    change smoothTensorCompositionCoherence P.Coefficient f g
    refine ⟨?_, ?_⟩
    · have := hTensor (Etale.dualizingComplex P.Coefficient g)
      have : IsIso (smoothDualizingCompMap P.Coefficient f g) := by
        dsimp only [smoothDualizingCompMap]
        infer_instance
      infer_instance
    · intro K _hK
      apply congrArg ((comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map)
      exact smoothTensorCompositionEquation P.Coefficient f g K

end AlgebraicGeometry.ProEtale

end
