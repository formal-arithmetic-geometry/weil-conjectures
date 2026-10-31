/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.AffineSpaceZeroSectionConstructions
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization
public import WeilConjectures.AlgebraicGeometry.ProjectionPurityCoordinates
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.AlgebraicGeometry.ProjectionTensorIntegration
import WeilConjectures.AlgebraicGeometry.AffineSpaceZeroSectionPurity

/-! # The canonical finite-stage smooth dualizing complex

Source: latest blueprint, sec-smooth-purity/sk-cor-sp-all-coefficients,
cor-pur-finite-stage-smooth-dualizing-complex.md
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex).

The inverse of the identification is fixed to be the unit specialization of the
specified smooth purity map. The affine normalization is expressed through the
closed exceptional Hom bijection: composition with `finiteSmoothAffineNormalization` is integration
of a supported class. The coordinate Cartier product is the existing `thom` map.
The ordered Kummer-boundary product is its multiple by `(-1)^d`, since each
Kummer boundary is minus its Cartier class and all factors have even degree.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The source of unit smooth purity, in the recorded intrinsic coefficient coordinates.
This is `La* A(d)[2d]`, with the canonical unit pullback identification already used
by `smoothTrace`; it is a coordinate abbreviation, not another Tate twist construction.
Source: latest blueprint, finite smooth dualizing complex, first display
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex). -/
abbrev finiteSmoothUnitSource (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) : Scheme.proEtaleDerivedCategory X P.Ring :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
    ((shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient))) (2 * (d : ℤ))).obj
        (((smoothPurityTensor P.Coefficient X).obj
          ((P.smoothPurityPullback f).obj
            ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
              (P.coefficientUnit Y)))).obj
          ((shiftFunctor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} P.Coefficient))) (-(2 * (d : ℤ)))).obj
              (P.diagonalTwist X d))))

/-- The existing exceptional inverse image of the coefficient unit, in precisely the
coordinates used by the existing exceptional counit. For a structure map this is
`omega_X = Ra_X^! A`. No exceptional functor or coefficient object is chosen here.
Source: latest blueprint, finite smooth dualizing complex, definition of omega
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex). -/
abbrev finiteSmoothDualizingObject (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Scheme.proEtaleDerivedCategory X P.Ring :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
    ((P.smoothPurityExceptionalOver f aY).obj
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (P.coefficientUnit Y)))

/-- The unit purity arrow appearing in the definition of `smoothTrace`, written out
using its canonical ordinary-etale unit presentation. This is the reassociation
followed by the diagonal-orientation tensor map, with the realization unit as the
presentation isomorphism. It does not select an arbitrary purity isomorphism.
Source: latest blueprint, finite smooth dualizing complex, finite purity identification
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex). -/
def finiteSmoothUnitPurity (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    P.finiteSmoothUnitSource f d ⟶ P.finiteSmoothDualizingObject aY f :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
    (P.smoothPurityReassociation X d
      ((P.smoothPurityPullback f).obj
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
          (P.coefficientUnit Y)))).hom ≫
    (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.map
      (P.smoothPurityTensorMapInPresentation f d aY
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj (P.coefficientUnit Y))
        (Etale.ordinaryFiniteUnit P.Coefficient Y)
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
              (Etale.ordinaryFiniteUnit P.Coefficient Y))))

/-- The existing structural compact-support functor, with the tautological base
compatibility supplied. Source: latest blueprint, Ra_X!
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex). -/
abbrev finiteSmoothStructureCompact (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))] :
    Scheme.proEtaleDerivedCategory X P.Ring ⥤
      Scheme.proEtaleDerivedCategory (Spec (.of P.field.k)) P.Ring :=
  letI : (Spec (.of P.field.k)).Over (Spec (.of P.field.k)) := ⟨𝟙 _⟩
  letI : (X ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) :=
    { comp_over := by
        change (X ↘ Spec (.of P.field.k)) ≫ 𝟙 _ = _
        exact Category.comp_id _ }
  P.smoothCompactSupport (X ↘ Spec (.of P.field.k))

/-- The recorded structural exceptional counit, with no extra base-compatibility
hypothesis. Source: latest blueprint, the counit at A
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex). -/
def finiteSmoothStructureCounit (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))] :
    (P.finiteSmoothStructureCompact X).obj
        (P.finiteSmoothDualizingObject (𝟙 (Spec (.of P.field.k)))
          (X ↘ Spec (.of P.field.k))) ⟶
      P.coefficientUnit (Spec (.of P.field.k)) :=
  letI : (Spec (.of P.field.k)).Over (Spec (.of P.field.k)) := ⟨𝟙 _⟩
  letI : (X ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) :=
    { comp_over := by
        change (X ↘ Spec (.of P.field.k)) ≫ 𝟙 _ = _
        exact Category.comp_id _ }
  P.smoothExceptionalCounit (X ↘ Spec (.of P.field.k))
    (P.coefficientUnit (Spec (.of P.field.k)))

/-- The recorded structural smooth trace. Source: latest blueprint, normalized
integration (blueprint: cor-pur-finite-stage-smooth-dualizing-complex). -/
def finiteSmoothStructureTrace (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (P.finiteSmoothStructureCompact X).obj
        (P.finiteSmoothUnitSource (X ↘ Spec (.of P.field.k)) d) ⟶
      P.coefficientUnit (Spec (.of P.field.k)) :=
  letI : (Spec (.of P.field.k)).Over (Spec (.of P.field.k)) := ⟨𝟙 _⟩
  letI : (X ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) :=
    { comp_over := by
        change (X ↘ Spec (.of P.field.k)) ≫ 𝟙 _ = _
        exact Category.comp_id _ }
  P.smoothTrace (X ↘ Spec (.of P.field.k)) d

/-- Normalized finite integration after the recorded coefficient-point functor.
Its source is exactly finite compact cohomology of the unit purity source; its target
is the coefficient-point realization of the degree-zero constant unit. These are the
existing coordinates for `RΓ_c(X,A_X(d)[2d])` and `A`, respectively.
Source: latest blueprint, finite smooth dualizing complex, integration display
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex). -/
def finiteSmoothIntegration (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (pointFiniteSections P.field.k P.Ring).mapDerivedCategory.obj
        ((P.finiteSmoothStructureCompact X).obj
          (P.finiteSmoothUnitSource (X ↘ Spec (.of P.field.k)) d)) ⟶
      (pointFiniteSections P.field.k P.Ring).mapDerivedCategory.obj
        (P.coefficientUnit (Spec (.of P.field.k))) :=
  (pointFiniteSections P.field.k P.Ring).mapDerivedCategory.map
    (P.finiteSmoothStructureTrace X d)

/-- The canonical smooth dualizing identification, with its actual counit equation.
Source: latest blueprint, sec-smooth-purity/sk-cor-sp-all-coefficients,
cor-pur-finite-stage-smooth-dualizing-complex, first two sentences
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex).

Proof:
1. Use the canonical ordinary degree-zero unit presentation already recorded in
   finiteSmoothUnitPurity. The ordinary smooth tensor theorem makes its tensor
   comparison invertible. The site-comparison unit is invertible on this bounded
   below unit, so all factors of smoothPurityTheta are invertible.
2. Tensoring the inverse normalized diagonal orientation and applying the canonical
   reassociation and realization preserve invertibility. Invert this very purity
   map to obtain theta; its inverse equation is definitional.
3. The recorded smooth trace is compact support of that purity map followed by the
   counit. Functoriality and the inverse equations give the displayed counit identity.
   Applying the existing coefficient-point functor gives finiteSmoothIntegration.
-/
theorem finiteStage_smoothDualizingComplex (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    ∃ θ : P.finiteSmoothDualizingObject (𝟙 (Spec (.of P.field.k)))
          (X ↘ Spec (.of P.field.k)) ≅
        P.finiteSmoothUnitSource (X ↘ Spec (.of P.field.k)) d,
      θ.inv = P.finiteSmoothUnitPurity (𝟙 (Spec (.of P.field.k)))
        (X ↘ Spec (.of P.field.k)) d ∧
        P.finiteSmoothStructureCounit X =
          (P.finiteSmoothStructureCompact X).map θ.hom ≫ P.finiteSmoothStructureTrace X d := by
  let : (Spec (.of P.field.k)).Over (Spec (.of P.field.k)) := ⟨𝟙 _⟩
  let : (X ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) :=
    ⟨Category.comp_id _⟩
  let := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of P.field.k))
  let : HasCompactification (X ↘ Spec (.of P.field.k)) := inferInstance
  let : HasInvertibleExponent P.Coefficient X :=
    P.finiteComparedInvertibleExponent (X ↘ Spec (.of P.field.k))
  let U := Etale.ordinaryFiniteUnit P.Coefficient (Spec (.of P.field.k))
  obtain ⟨_, _, _, _, ht⟩ :=
    Etale.exists_dualizingComplex_iso_and_tensor P.Coefficient (X ↘ Spec (.of P.field.k)) d
  have := ht U
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) (Spec (.of P.field.k)) U
      (show DerivedCategory.TStructure.t.plus U from ⟨0, inferInstance⟩)
  have htheta : IsIso (P.smoothPurityTheta (X ↘ Spec (.of P.field.k))
      ((Scheme.sfIntrinsicDerivedEquivalence (Spec (.of P.field.k)) P.Ring).inverse.obj
        (P.coefficientUnit (Spec (.of P.field.k)))) U
      ((Scheme.sfIntrinsicDerivedEquivalence (Spec (.of P.field.k)) P.Ring).unitIso.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
          (Spec (.of P.field.k))).mapDerivedCategory.obj U))) := by
    dsimp only [smoothPurityTheta, smoothPurityEtaleTheta]
    simp only [Functor.map_comp]
    infer_instance
  have hgamma : IsIso (P.finiteSmoothUnitPurity (𝟙 (Spec (.of P.field.k)))
      (X ↘ Spec (.of P.field.k)) d) := by
    dsimp only [finiteSmoothUnitPurity, smoothPurityTensorMapInPresentation]
    infer_instance
  let γ := asIso (P.finiteSmoothUnitPurity (𝟙 (Spec (.of P.field.k)))
    (X ↘ Spec (.of P.field.k)) d)
  refine ⟨γ.symm, rfl, ?_⟩
  change P.finiteSmoothStructureCounit X =
    (P.finiteSmoothStructureCompact X).map γ.inv ≫
      ((P.finiteSmoothStructureCompact X).map γ.hom ≫ P.finiteSmoothStructureCounit X)
  rw [← Category.assoc, ← Functor.map_comp, γ.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Integration in closed exceptional coordinates, using the specified smooth
purity map itself. At positive dimension we change from the existing ordered
Cartier-product target to the smooth-purity source, apply that purity map, and
collapse the composite exceptional inverse image along p composed with zero = id.
The target-coordinate map is canonical and independent of either purity arrow.
At dimension zero this is the identity-adjunction normalization.
Source: latest blueprint, finite smooth dualizing complex, affine-fibre clause
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex). -/
def finiteSmoothAffineNormalization (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :
    (c : ℕ) →
      (ProEtale.rightDerivedUpperShriek (ProEtale.AffineZeroPurity.setting P n).Coefficient
        (ProEtale.AffineZeroPurity.zero B c)).obj
          (ProEtale.AffineZeroPurity.target P n
            (iteratedAffineLine B c) c) ⟶ ProEtale.AffineZeroPurity.unit P n B
  | 0 => ProEtale.AffineZeroPurity.normalization P n B aB 0
  | c + 1 => by
    letI := (ProEtale.AffineSpacePurity.projection_geometry B (c + 1)).1
    letI := (ProEtale.AffineSpacePurity.projection_geometry B (c + 1)).2
    letI := projection_smooth B (c + 1)
    have γ := ((ProEtale.AffineZeroPurity.targetSourceIso P n B (c + 1)).hom ≫
        (projectionSourceIso P.field P.coefficients P.extension n B aB
          (ProEtale.AffineZeroPurity.unit P n B) (c + 1)).inv ≫
        ((ProEtale.AffineZeroPurity.setting P n).smoothPurityReassociation
          (iteratedAffineLine B (c + 1)) (c + 1)
          (((ProEtale.AffineZeroPurity.setting P n).smoothPurityPullback
            (iteratedAffineLineProj B (c + 1))).obj
              (ProEtale.AffineZeroPurity.unit P n B))).hom ≫
        (ProEtale.AffineZeroPurity.setting P n).smoothPurityTensorMapInPresentation
          (iteratedAffineLineProj B (c + 1)) (c + 1) aB
          (ProEtale.AffineZeroPurity.unit P n B)
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ProEtale.AffineZeroPurity.setting P n).constantEtale B))
          ((Functor.mapDerivedCategorySingleFunctor
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (ProEtale.AffineZeroPurity.setting P n).Coefficient) B)
            0).app ((ProEtale.AffineZeroPurity.setting P n).constantEtale B) ≪≫
              (eqToIso (ProEtale.AffineZeroPurity.unit_single_eq P n B)).symm) ≫
        projectionTargetMap P.field P.coefficients P.extension n B aB
          (ProEtale.AffineZeroPurity.unit P n B) (c + 1))
    unfold ProEtale.AffineSpacePurity.exceptional at γ
    exact (ProEtale.rightDerivedUpperShriek
      (ProEtale.AffineZeroPurity.setting P n).Coefficient
      (ProEtale.AffineZeroPurity.zero B (c + 1))).map γ ≫
        ProEtale.AffineZeroPurity.collapse P n B aB (c + 1)

attribute [local implicit_reducible] ProEtale.AffineOrderedIntegration.proCategory
  ProEtale.AffineOrderedIntegration.etaleCategory
attribute [local irreducible] ProEtale.rightDerivedUpperShriek

set_option maxHeartbeats 2000000 in
-- Comparing the canonical endpoint transports needs the cached category instances.
/-- Affine-fibre normalization of the same finite integration map, in its closed
exceptional-adjunction coordinates. The first input is the actual ordered Cartier
product. The second is the ordered Kummer-boundary product: each factor is minus
its Cartier class, so multilinearity gives the displayed integer scalar `(-1)^d`.
Here `n` indexes the positive coefficient level `n+1`, covering every allowed level.
Source: latest blueprint, finite smooth dualizing complex, final sentence
(blueprint: cor-pur-finite-stage-smooth-dualizing-complex).

Proof:
1. Apply projection_presentation_coordinate at the canonical ordinary unit
   presentation. Cancel the invertible source and target coordinate comparisons.
   Applying the closed exceptional functor after targetSourceIso and then collapse
   identifies finiteSmoothAffineNormalization with AffineZeroPurity.normalization.
   At dimension zero these are definitionally identical.
2. The normalized zero-section purity equation gives thom followed by this
   normalization equal to the identity. Its thom is the actual Cartier product.
3. Integer scalar multiplication commutes with composition, so the prescribed
   (-1)^d multiple representing the ordered Kummer product integrates to (-1)^d.
   This also includes the empty product at d=0; no coordinates are permuted.
-/
theorem finiteStage_smoothDualizingComplex_affineNormalization
    (P : PurityFiniteSetting.{u}) (n d : ℕ) :
    ProEtale.AffineZeroPurity.thom P n (Spec (.of P.field.k)) (𝟙 _) d ≫
        finiteSmoothAffineNormalization P n (Spec (.of P.field.k)) (𝟙 _) d =
      𝟙 (ProEtale.AffineZeroPurity.unit P n (Spec (.of P.field.k))) ∧
    ((-1 : ℤ) ^ d •
        ProEtale.AffineZeroPurity.thom P n (Spec (.of P.field.k)) (𝟙 _) d) ≫
        finiteSmoothAffineNormalization P n (Spec (.of P.field.k)) (𝟙 _) d =
      (-1 : ℤ) ^ d • 𝟙 (ProEtale.AffineZeroPurity.unit P n (Spec (.of P.field.k))) := by
  have hn : finiteSmoothAffineNormalization P n (Spec (.of P.field.k)) (𝟙 _) d =
      ProEtale.AffineZeroPurity.normalization P n (Spec (.of P.field.k)) (𝟙 _) d := by
    cases d with
    | zero => rfl
    | succ c =>
      let B := Spec (.of P.field.k)
      let Q := ProEtale.AffineZeroPurity.setting P n
      let K : ProEtale.AffineSpacePurity.Plus Q.Coefficient B :=
        ⟨ProEtale.AffineZeroPurity.unit P n B,
          (ProEtale.AffineZeroPurity.unit_origin P n B).plus⟩
      let Ke := (DerivedCategory.singleFunctor _ 0).obj (Q.constantEtale B)
      let eK := (Functor.mapDerivedCategorySingleFunctor
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient) B) 0).app
          (Q.constantEtale B) ≪≫
        (eqToIso (ProEtale.AffineZeroPurity.unit_single_eq P n B)).symm
      let : B.Over (Spec (.of P.field.k)) := ⟨𝟙 B⟩
      have hc := projection_presentation_coordinate P.field P.coefficients P.extension n B
        (𝟙 _) K Ke (ProEtale.AffineZeroPurity.unit_finiteTor P n B) eK (c + 1)
      let := (ProEtale.AffineSpacePurity.projection_geometry B (c + 1)).1
      let := (ProEtale.AffineSpacePurity.projection_geometry B (c + 1)).2
      let := projection_smooth B (c + 1)
      let := projectionTarget_isIso P.field P.coefficients P.extension n B (𝟙 _)
        K Ke (ProEtale.AffineZeroPurity.unit_finiteTor P n B) eK (c + 1)
      have hc' := congrArg (fun z ↦
        (projectionSourceIso P.field P.coefficients P.extension n B (𝟙 _)
          K.obj (c + 1)).inv ≫ z ≫
        projectionTargetMap P.field P.coefficients P.extension n B (𝟙 _) K.obj (c + 1)) hc
      simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.inv_hom_id,
        Category.comp_id] at hc'
      have hg :
          (projectionSourceIso P.field P.coefficients P.extension n B (𝟙 _)
            K.obj (c + 1)).inv ≫
          (Q.smoothPurityReassociation (iteratedAffineLine B (c + 1)) (c + 1)
            ((Q.smoothPurityPullback (iteratedAffineLineProj B (c + 1))).obj K.obj)).hom ≫
          Q.smoothPurityTensorMapInPresentation (iteratedAffineLineProj B (c + 1))
            (c + 1) (𝟙 B) K.obj Ke eK ≫
          projectionTargetMap P.field P.coefficients P.extension n B (𝟙 _) K.obj (c + 1) =
          ProEtale.AffineZeroPurity.gamma P n B (𝟙 _) (c + 1) := by
        simp only [ProEtale.AffineZeroPurity.gamma]
        convert hc' using 1; try rfl
      let N : ProEtale.AffineSpacePurity.ComparisonHom Q B K.obj (c + 1) →
          ((ProEtale.rightDerivedUpperShriek Q.Coefficient
            (ProEtale.AffineZeroPurity.zero B (c + 1))).obj
              (ProEtale.AffineZeroPurity.target P n (iteratedAffineLine B (c + 1))
                (c + 1)) ⟶ ProEtale.AffineZeroPurity.unit P n B) := fun z ↦ by
        unfold ProEtale.AffineSpacePurity.ComparisonHom
          ProEtale.AffineSpacePurity.exceptional at z
        exact (ProEtale.rightDerivedUpperShriek Q.Coefficient
          (ProEtale.AffineZeroPurity.zero B (c + 1))).map
            ((ProEtale.AffineZeroPurity.targetSourceIso P n B (c + 1)).hom ≫ z) ≫
          ProEtale.AffineZeroPurity.collapse P n B (𝟙 _) (c + 1)
      have hn := congrArg N hg
      unfold finiteSmoothAffineNormalization ProEtale.AffineZeroPurity.normalization
      apply (conj_eqToHom_iff_heq' _ _ _ _).2
      unfold ProEtale.AffineZeroPurity.normalizationRaw
      dsimp +instances only [N, B, Q, K, Ke, eK,
        ProEtale.AffineOrderedIntegration.proCategory,
        ProEtale.AffineOrderedIntegration.etaleCategory, ProEtale.cupHasDerivedCategory] at hn ⊢
      delta ProEtale.AffineSpacePurity.exceptional at hn ⊢
      exact heq_of_eq hn
  have h := (ProEtale.AffineZeroPurity.zeroSection_purity P n
    (Spec (.of P.field.k)) (𝟙 _) d).2.1
  rw [hn]
  exact ⟨h, by rw [Preadditive.zsmul_comp, h]⟩

end WeilConjectures.PurityFiniteSetting
