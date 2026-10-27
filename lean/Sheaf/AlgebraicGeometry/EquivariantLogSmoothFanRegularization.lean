/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.StrictLogBlowupProcedure
public import Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogFanChartBlowup
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.FreeCharacteristicRelativeNCCriterion
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.FiniteTypeExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import Sheaf.AlgebraicGeometry.FSLogSmoothCompositionStrictBaseChange
import Sheaf.AlgebraicGeometry.ProjectiveBundleComposition
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.FunctorialFanDesingularization
import Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent
import Sheaf.AlgebraicGeometry.LogBlowupNormalization
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison

/-! # Equivariant log smooth fan regularization

Source: ILO, Travaux de Gabber, VIII 3.3.13--3.3.15, 3.4.4--3.4.9 and 4.1.1;
X Lemma 2.2, p.149, smooth-pair-over-a-field refinement
(blueprint: lem-sfb-equivariant-log-smooth-fan-regularization).

The structure packages the clauses of the conclusion for the specified tower. Its
scheme maps are the actual composites of that tower. The procedure in the theorem
retains the ordered log centers and the strict etale composition laws, including the
component inclusions of finite disjoint unions. No global labels for boundary branches
are chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The geometric and equivariant clauses for one fan-regularization tower.
Normalization uses the ordinary blowup's function field; its dense-open identification
with the previous integral stage makes this the common function field of the tower.
The boundary is the radical pullback ideal, and all chart branches pass through the
specified geometric point. Source: ILO VIII 3.3.15, 3.4.4--3.4.9; X 2.2, p.149
(blueprint: lem-sfb-equivariant-log-smooth-fan-regularization). -/
structure EquivariantLogSmoothFanRegularization
    {F : Type u} [Field F] {X : FineSaturatedLogScheme.{u}}
    {N : EtaleLogStructure (Spec (.of F))} {hN : N.IsFineSaturated}
    (s : EtaleLogHom X ⟨Spec (.of F), inferInstance, N, hN⟩)
    (B : Closeds X.scheme) (U : X.scheme.Opens)
    {J : Type v} [Group J] (ρ : J →* (F ≃+* F)) (a : J →* Aut X.scheme)
    (A : LogBlowupTowerOver X) where
  originalAction : FSLogGroupAction J X
  originalBase : originalAction.baseAction = a
  action : ∀ i, FSLogGroupAction J (A.tower.level i)
  equivariant : ∀ i, (action i).IsEquivariant originalAction (A.toBase i)
  stepEquivariant : ∀ i : Fin A.tower.length,
    (action i.succ).IsEquivariant (action i.castSucc) (A.tower.arrow i)
  centersInvariant : ∀ (i : Fin A.tower.length) (g : J),
    ((action i.castSucc).logMap g).pullbackIdeal (A.tower.center i) = A.tower.center i
  semilinear : ∀ i g,
    ((action i).baseAction g).hom ≫ (A.toBase i).base ≫ s.base =
      (A.toBase i).base ≫ s.base ≫ Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom)
  integral : ∀ i, IsIntegral (A.tower.level i).scheme
  noetherian : ∀ i, IsNoetherian (A.tower.level i).scheme
  finiteType : ∀ i,
    LocallyOfFiniteType ((A.toBase i).base ≫ s.base) ∧
      QuasiCompact ((A.toBase i).base ≫ s.base)
  logRegular : ∀ i, (A.tower.level i).IsLogRegular
  logSmooth : ∀ i, ((A.toBase i).comp s).IsLogSmooth
  triviality : ∀ i,
    (A.tower.level i).logStructure.trivialityLocus = (A.toBase i).base ⁻¹' (U : Set X.scheme)
  unchangedOpen : ∀ i, IsIso ((A.toBase i).base ∣_ U)
  normalized : ∀ i : Fin A.tower.length,
    ∃ I : (A.tower.level i.castSucc).scheme.IdealSheafData,
      I ≠ ⊥ ∧ I.ofFiniteType ∧
      (∀ (V : (A.tower.level i.castSucc).scheme.affineOpens)
        (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ (A.tower.level i.castSucc).scheme)
        (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk V.1.ι)),
        (I.ideal V).map
          ((strictLocalGerm _ t (Scheme.Etale.mk V.1.ι) w).hom.comp V.1.topIso.inv.hom) =
          Ideal.span ((A.tower.level i.castSucc).logStructure.toEtalePrelogStructure.stalkAlpha t ''
            (A.tower.level i.castSucc).logStructure.idealStalk (A.tower.center i) t)) ∧
      ∃ hI : IsIntegral I.blowup,
        IsFinite (@Scheme.fromNormalization I.blowup hI) ∧
        ∃ e : (A.tower.level i.succ).scheme ≅ @Scheme.normalization I.blowup hI,
          e.hom ≫ @Scheme.fromNormalization I.blowup hI ≫ I.blowupMap =
            (A.tower.arrow i).base
  projective : IsProjectiveBundle (A.toBase (Fin.last A.tower.length)).base
  denseOpen : Dense
    (((A.toBase (Fin.last A.tower.length)).base ⁻¹ᵁ U :
      (A.tower.level (Fin.last A.tower.length)).scheme.Opens) :
      Set (A.tower.level (Fin.last A.tower.length)).scheme)
  freeCharacteristic : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ (A.tower.level (Fin.last A.tower.length)).scheme),
    ∃ r : ℕ, Nonempty
      ((A.tower.level (Fin.last A.tower.length)).logStructure.characteristic t ≃*
        Multiplicative (Fin r → ℕ))
  regular : IsRegularScheme (A.tower.level (Fin.last A.tower.length)).scheme
  smooth : Smooth ((A.toBase (Fin.last A.tower.length)).base ≫ s.base)
  boundary :
    ((Scheme.IdealSheafData.vanishingIdeal B).comap
      (A.toBase (Fin.last A.tower.length)).base).radical =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨(((A.toBase (Fin.last A.tower.length)).base ⁻¹ᵁ U :
          (A.tower.level (Fin.last A.tower.length)).scheme.Opens) :
          Set (A.tower.level (Fin.last A.tower.length)).scheme)ᶜ,
          ((A.toBase (Fin.last A.tower.length)).base ⁻¹ᵁ U).isOpen.isClosed_compl⟩
  charts : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ (A.tower.level (Fin.last A.tower.length)).scheme),
    ∃ C : RelativeNormalCrossingsChart
      ((A.toBase (Fin.last A.tower.length)).base ≫ s.base)
      ((A.toBase (Fin.last A.tower.length)).base ⁻¹ᵁ U) t,
      (∀ i : ULift.{u} (Fin C.r), C.point.left (default : Spec (.of Ω)) ∈
        C.W.left.zeroLocus {C.comparison.appTop (AffineSpace.coord (Spec (.of F)) i)}) ∧
      ∀ z : Finset (ULift.{u} (Fin C.r)),
        Smooth ((C.intersectionIdeal z).subschemeι ≫ C.W.hom ≫
          (A.toBase (Fin.last A.tower.length)).base ≫ s.base) ∧
        ∀ (V : C.W.left.affineOpens) (p : Ideal Γ(C.W.left, V.1)),
          p ∈ ((C.intersectionIdeal z).ideal V).minimalPrimes → p.height = (z.card : ℕ∞)

/-- A finite equivariant saturated fan regularization, with projective normalized
blowups and pointed relative smooth normal-crossings charts over an arbitrary field.
Source: ILO VIII 3.3.13--3.3.15, 3.4.4--3.4.9, 4.1.1; X 2.2, p.149
(blueprint: lem-sfb-equivariant-log-smooth-fan-regularization).

Proof:
1. Finite type over a field makes X Noetherian and hence quasi-separated. Sharp fs
characteristics have torsion-free finite-rank group completions by sharp charts and
face sharpening. Fix the smooth-functorial saturated fan resolution.
2. For a global chart, shrink the target fan to a finite union of affine localization
neighbourhoods covering the image. Face sharpening makes this fan torsion free.
Lift its ordered resolution with log_fan_chart_blowup and remove exactly whole-monoid
centers, whose log blowups are identities by their universal property.
3. Strict fan-chart local comparison and fan functoriality identify these ordered
centers independently of the chart. Universal log blowups give unique comparisons,
so their identity and composition laws hold, also on finite disjoint unions.
4. Apply functorial_log_blowup_etale_descent. Terminal characteristics are the stalks
of the smooth terminal fan, hence free, including rank zero; strict etale covers
remain jointly surjective after each pullback.
5. Preservation of B lifts each original automorphism to a strict divisorial log
automorphism. The canonical tower comparisons lift it at every level. Their identity
and composition laws give the group law. This works for semilinear automorphisms.
6. Inductively apply exists_saturatedLogBlowup_normalization. Its generated ring
ideal is nonzero and finite type. The ordinary blowup is integral and projective;
its normalization is finite and integral in the common function field.
7. Finite maps are projective in the bundle sense. Compose projective-bundle maps
over the Noetherian, hence qcqs, targets. Properness gives finite type, closing the
Noetherian induction. The composite is projective, including a length-zero tower.
8. Each blowup is an isomorphism on the triviality open, and its new triviality
locus is the full inverse image. These opens are dense in the integral stages;
the resulting identification of dense opens proves birationality.
9. Saturated log blowups are log etale. Log smooth composition preserves the given
log smoothness over the trivial log field at every stage.
10. Log regularity identifies the last log structure with the divisorial structure
of the pulled open. The free-characteristic relative NC criterion supplies the
pointed smooth coordinate maps, reduced product boundary and smooth intersections
of the expected codimension. The regular-boundary criterion gives regularity.
Empty boundary has rank zero and empty coordinate product one. No separatedness,
perfection or global non-self-intersection assumption is used.
-/
theorem exists_equivariant_log_smooth_fan_regularization
    (F : Type u) [Field F] (X : FineSaturatedLogScheme.{u}) [IsIntegral X.scheme]
    (N : EtaleLogStructure (Spec (.of F))) (hN : N.IsFineSaturated)
    (hNtriv : N.trivialityLocus = Set.univ)
    (s : EtaleLogHom X ⟨Spec (.of F), inferInstance, N, hN⟩)
    [LocallyOfFiniteType s.base] [QuasiCompact s.base] (hs : s.IsLogSmooth)
    (B : Closeds X.scheme) (U : X.scheme.Opens)
    (hUB : (U : Set X.scheme) = (B : Set X.scheme)ᶜ) (hU : DenseRange U.ι)
    (hpair : @IsDivisorialFineSaturatedLogRegularPair X.scheme U.toScheme U.ι
      inferInstance X.locallyNoetherian hU)
    (hdiv : ∃ e : X.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι,
      e.hom ≫ divisorialStructuralMap U.ι = X.logStructure.alpha)
    (htriv : X.logStructure.trivialityLocus = (U : Set X.scheme))
    (J : Type v) [Group J] [Finite J] (ρ : J →* (F ≃+* F)) (a : J →* Aut X.scheme)
    (hscalar : ∀ g, (a g).hom ≫ s.base =
      s.base ≫ Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom))
    (hB : ∀ g, (a g).hom '' (B : Set X.scheme) = B) :
    ∃ (R : FineFan.SmoothFunctorialDesingularization.{u})
      (P : StrictEtaleLogBlowupProcedure
        (fun Y ↦ ∃ q : EtaleLogHom Y X, q.IsStrict ∧ Etale q.base))
      (hX : ∃ q : EtaleLogHom X X, q.IsStrict ∧ Etale q.base),
      (∀ (Y : FineSaturatedLogScheme.{u})
        (hY : ∃ q : EtaleLogHom Y X, q.IsStrict ∧ Etale q.base),
        ∀ (H : FineFan.ResolutionInput.{u})
          (c : LogFanChart Y ((R.resolution H).tower.level 0)),
        ∃ (L : LogFanTower (R.resolution H).tower) (h : L.level 0 = Y),
          HEq (L.chart 0) c ∧
          Nonempty (LogBlowupComparison (EtaleLogHom.id Y)
            { tower :=
                { length := (R.resolution H).length
                  level := L.level
                  arrow := L.arrow
                  center := fun i ↦ (L.chart i.castSucc).pullbackIdeal
                    ((R.resolution H).tower.center i)
                  isBlowup := L.blowup }
              initial := h }
            (P.tower Y hY))) ∧
      Nonempty (EquivariantLogSmoothFanRegularization s B U ρ a (P.tower X hX)) := by
  sorry

end AlgebraicGeometry
