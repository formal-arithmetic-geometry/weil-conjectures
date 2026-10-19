/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Sheaf.AlgebraicGeometry.DominantReducedPart

import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.RingTheory.NagataDomainN2
import Sheaf.RingTheory.JapaneseDomain
import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange
import Sheaf.RingTheory.RegularRingNormal
import Sheaf.RingTheory.EtaleNormalRing
import Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen
import WeilConjectures.AlgebraicGeometry.FiniteEtaleClopenRestrictionRank
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Sheaf.SixFunctors.TraceFormula.ProjectiveNodalFamilyGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.AlgebraicGeometry.AdmissibleQuotientAffineIntegralCharts
import Sheaf.AlgebraicGeometry.AlterationCoverCalculus
import Sheaf.AlgebraicGeometry.ProjectiveFiniteGroupQuotient

/-!
# Normalized base refinement of marked nodal quotients

Source: ILO, Travaux de Gabber, Expose IX 1.4, printed p. 133, and II 1.2.5--1.2.8
(blueprint: lem-per-nodal-quotient-normalized-base-refinement).

The input record only packages the hypotheses. Quotient maps are characterized by their
universal property; finiteness is not an extra hypothesis on the original base quotient.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The marked nodal quotient data before refinement. The closed boundary on the quotient
has its exact inverse image on the cover. The torsor and its action are identified with that
actual complement, rather than with an unrelated isomorphic cover.
Source: ILO IX 1.4, p. 133 (blueprint: lem-per-nodal-quotient-normalized-base-refinement). -/
structure MarkedNodalQuotientModel (ell : ℕ) (G : Type v) [Group G] [Finite G]
    (Y Y' C X : Scheme.{u}) [IsIntegral Y'] where
  ell_group : ∃ n : ℕ, Nat.card G = ell ^ n
  integral_base : IsIntegral Y
  affine_base : IsAffine Y
  noetherian_base : IsNoetherian Y
  noetherian_cover : IsNoetherian Y'
  integral_curve : IsIntegral C
  noetherian_curve : IsNoetherian C
  separated_curve : C.IsSeparated
  excellent_base : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U)
  excellent_cover : ∀ U : Y'.affineOpens, IsExcellent Γ(Y', U)
  excellent_curve : ∀ U : C.affineOpens, IsExcellent Γ(C, U)
  ell_unit : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y)
  b : Y' ⟶ Y
  f : C ⟶ Y'
  π : C ⟶ X
  p : X ⟶ Y
  square : π ≫ p = f ≫ b
  aY : G →* Aut Y'
  aC : G →* Aut C
  over_base : ∀ g : G, (aY g).hom ≫ b = b
  equivariant : ∀ g : G, (aC g).hom ≫ f = f ≫ (aY g).hom
  admissible_base : ∀ y : Y', ∃ U : Y'.affineOpens, ∀ g : G, (aY g).hom y ∈ U.1
  admissible_curve : ∀ c : C, ∃ U : C.affineOpens, ∀ g : G, (aC g).hom c ∈ U.1
  invariant_curve : ∀ g : G, (aC g).hom ≫ π = π
  quotient_base : ∀ (W : Scheme.{u}) (m : Y' ⟶ W),
    (∀ g : G, (aY g).hom ≫ m = m) → ∃! q : Y ⟶ W, b ≫ q = m
  quotient_curve : ∀ (W : Scheme.{u}) (m : C ⟶ W),
    (∀ g : G, (aC g).hom ≫ m = m) → ∃! q : X ⟶ W, π ≫ q = m
  T : TopologicalSpace.Closeds Y
  rare : IsNowhereDense (b ⁻¹' (T : Set Y))
  torsor : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.compl)
  torsor_iso : torsor.Z ≅ (b ⁻¹ᵁ T.compl).toScheme
  torsor_map : torsor_iso.hom ≫ (b ∣_ T.compl) = torsor.π
  torsor_action : ∀ g : G,
    torsor.smul g ≫ torsor_iso.hom ≫ (b ⁻¹ᵁ T.compl).ι =
      torsor_iso.hom ≫ (b ⁻¹ᵁ T.compl).ι ≫ (aY g).hom
  [projective : IsHProjective f]
  [flat : Flat f]
  [finite_presentation : LocallyOfFinitePresentation f]
  nodal : HasNodalGeometricFibres f
  smooth_off : ∀ c : C, b (f c) ∉ T → c ∈ f.smoothLocus
  smooth_generic : Smooth (f.fiberToSpecResidueField (genericPoint Y'))
  integral_generic : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y'))
  D : C.IdealSheafData
  marking_cartier : D.IsInvertible
  marking_stable : ∀ g : G, D.comap (aC g).hom = D
  marking_finite : IsFinite (D.subschemeι ≫ f)
  marking_etale : Etale (D.subschemeι ≫ f)
  marking_smooth : ∀ c : C, c ∈ D.support → c ∈ f.smoothLocus
  E : X.IdealSheafData
  boundary_cartier : E.IsInvertible
  boundary_support : π ⁻¹' (E.support : Set X) ⊆
    (D.support : Set C) ∪ (f ≫ b) ⁻¹' (T : Set Y)

/-- The actual base-change endomorphism induced by an element of the base action.
Source: ILO IX 1.4, p. 133 (blueprint: lem-per-nodal-quotient-normalized-base-refinement). -/
noncomputable def MarkedNodalQuotientModel.baseChangeActionMap
    {ell : ℕ} {G : Type v} [Group G] [Finite G]
    {Y Y' C X Y₁ : Scheme.{u}} [IsIntegral Y']
    (Q : MarkedNodalQuotientModel ell G Y Y' C X) (u₁ : Y₁ ⟶ Y) (g : G) :
    pullback Q.b u₁ ⟶ pullback Q.b u₁ :=
  pullback.map Q.b u₁ Q.b u₁ (Q.aY g).hom (𝟙 Y₁) (𝟙 Y)
    (by simpa using (Q.over_base g).symm) (by simp)

/-- The map from the normalized selected reduced component to the original base cover.
Source: ILO IX 1.4, p. 133 (blueprint: lem-per-nodal-quotient-normalized-base-refinement). -/
noncomputable abbrev normalizedNodalComponentMap
    {Y Y' Y₁ F : Scheme.{u}} [IsIntegral F] (b : Y' ⟶ Y) (u₁ : Y₁ ⟶ Y)
    (j : F ⟶ pullback b u₁) : F.normalization ⟶ Y' :=
  F.fromNormalization ≫ j ≫ pullback.fst b u₁

/-- The structure map from the normalized selected reduced component to the new base.
Source: ILO IX 1.4, p. 133 (blueprint: lem-per-nodal-quotient-normalized-base-refinement). -/
noncomputable abbrev normalizedNodalComponentBaseMap
    {Y Y' Y₁ F : Scheme.{u}} [IsIntegral F] (b : Y' ⟶ Y) (u₁ : Y₁ ⟶ Y)
    (j : F ⟶ pullback b u₁) : F.normalization ⟶ Y₁ :=
  F.fromNormalization ≫ j ≫ pullback.snd b u₁

/-- All conclusions for one chosen reduced dominant component. The component is supplied as
an integral closed subscheme with the specified irreducible-component support. This uniquely
specifies its reduced induced structure. Both the normalized base and the curve are actual
canonical constructions. All actions and quotient comparisons are pinned by commuting diagrams.
Source: ILO IX 1.4, p. 133 (blueprint: lem-per-nodal-quotient-normalized-base-refinement). -/
structure NormalizedNodalQuotientRefinement
    {ell : ℕ} {G : Type v} [Group G] [Finite G]
    {Y Y' C X Y₁ F : Scheme.{u}} [IsIntegral Y'] [IsIntegral F] [IsIntegral Y₁]
    (Q : MarkedNodalQuotientModel ell G Y Y' C X) (u₁ : Y₁ ⟶ Y)
    (j : F ⟶ pullback Q.b u₁) (Z : Set ↥(pullback (C := Scheme.{u}) Q.b u₁)) where
  H : Subgroup G
  decomposition : ∀ g : G, g ∈ H ↔ Q.baseChangeActionMap u₁ g '' Z = Z
  X₁ : Scheme.{u}
  model : MarkedNodalQuotientModel ell H Y₁ F.normalization
    (pullback Q.f (normalizedNodalComponentMap Q.b u₁ j)) X₁
  base_map : model.b = normalizedNodalComponentBaseMap Q.b u₁ j
  curve_map : model.f = pullback.snd Q.f (normalizedNodalComponentMap Q.b u₁ j)
  boundary_set : (model.T : Set Y₁) = u₁ ⁻¹' (Q.T : Set Y)
  marking : model.D = Q.D.comap (pullback.fst Q.f (normalizedNodalComponentMap Q.b u₁ j))
  lifted_base_action : ∀ g : H,
    (model.aY g).hom ≫ normalizedNodalComponentMap Q.b u₁ j =
      normalizedNodalComponentMap Q.b u₁ j ≫ (Q.aY g.val).hom
  lifted_curve_action : ∀ g : H,
    (model.aC g).hom ≫ pullback.fst Q.f (normalizedNodalComponentMap Q.b u₁ j) =
      pullback.fst Q.f (normalizedNodalComponentMap Q.b u₁ j) ≫ (Q.aC g.val).hom
  normal_base : IsNormalScheme F.normalization
  finite_base : IsFinite model.b
  base_quotient : IsAdmissibleFiniteSchemeQuotient model.aY model.b
  connected_torsor : ConnectedSpace model.torsor.Z
  function_field_algebra : Algebra Y₁.functionField F.normalization.functionField
  field_map : @Spec.map _ _ (CommRingCat.ofHom
    (@algebraMap Y₁.functionField F.normalization.functionField _ _ function_field_algebra)) ≫
      Y₁.fromSpecFunctionField = F.normalization.fromSpecFunctionField ≫ model.b
  normalization_iso : F.normalization ≅
    @Scheme.normalizationIn Y₁ _ F.normalization.functionField _ function_field_algebra
  normalization_map : normalization_iso.hom ≫
    @Scheme.fromNormalizationIn Y₁ _ F.normalization.functionField _ function_field_algebra =
      model.b
  integral_quotient : IsIntegral X₁
  noetherian_quotient : IsNoetherian X₁
  excellent_quotient : ∀ U : X₁.affineOpens, IsExcellent Γ(X₁, U)
  finite_quotient : IsAdmissibleFiniteSchemeQuotient model.aC model.π
  toOriginal : X₁ ⟶ X
  quotient_square : model.π ≫ toOriginal =
    pullback.fst Q.f (normalizedNodalComponentMap Q.b u₁ j) ≫ Q.π
  base_square : toOriginal ≫ Q.p = model.p ≫ u₁
  boundary_pullback : model.E = Q.E.comap toOriginal
  comparison : X₁ ⟶ (dominantReducedPartIdeal (pullback.snd Q.p u₁)).subscheme
  comparison_original : comparison ≫
    (dominantReducedPartIdeal (pullback.snd Q.p u₁)).subschemeι ≫ pullback.fst Q.p u₁ =
      toOriginal
  comparison_base : comparison ≫
    (dominantReducedPartIdeal (pullback.snd Q.p u₁)).subschemeι ≫ pullback.snd Q.p u₁ =
      model.p
  proper_comparison : IsProper comparison
  birational_comparison : ∃ U :
      (dominantReducedPartIdeal (pullback.snd Q.p u₁)).subscheme.Opens,
    Dense (U : Set (dominantReducedPartIdeal (pullback.snd Q.p u₁)).subscheme) ∧
    Dense (comparison ⁻¹' (U : Set
      (dominantReducedPartIdeal (pullback.snd Q.p u₁)).subscheme)) ∧ IsIso (comparison ∣_ U)

/-- Normalizing any reduced component dominating the regular new base gives the
specified decomposition-group model and proper birational quotient comparison.
Source: ILO IX 1.4, p. 133 (blueprint: lem-per-nodal-quotient-normalized-base-refinement).

Proof plan, following the sixteen steps of the node:
1. Admissible quotient charts identify the base rings A = B^G. Excellence makes A Nagata;
   its integral closure in K(Y') is finite. Noetherian submodule finiteness makes B finite.
2. The averaging idempotent splits the invariants. Its scalar extension shows that invariants
   commute with arbitrary base change because the group order is a unit.
3. The pulled-back torsor over the dense open has clopen normal integral components.
4. Its components are permuted transitively; the selected component has stabilizer H.
5. Excellence makes the normalization finite and excellent; normalization lifting gives H.
6. Generic full faithfulness for finite etale schemes extends the H-torsor identity.
7. Integral closure in its actual function field identifies the normalization over the base.
8. Invariants of the transitive product give L^H = K(Y1); normality gives N/H = Y1.
9. Nodal-family base change preserves projectivity, flatness, nodal fibres and generic geometry.
10. Flatness injects affine rings into the integral generic fibre, proving total integrality.
11. Finite-over-projective composition and projective finite-group quotients give admissibility,
    separatedness and excellence of the new total spaces and quotient.
12. The finite etale marking is relative Cartier, hence remains Cartier after base change.
13. The quotient universal property gives the comparison. The coset decomposition and averaging
    identify it with an isomorphism over the dense torsor open.
14. Reducedness factors it through the reduced dominant part; proper-over-separated gives
    properness and the dense-open isomorphism gives birationality.
15. Dominance preserves nonzero local Cartier equations; the boundary inclusion pulls back.
16. The family assertion below uses alteration cover calculus and proper birational covers. -/
theorem exists_normalizedNodalQuotientRefinement
    (ell : ℕ) [Fact ell.Prime] (G : Type v) [Group G] [Finite G]
    (Y Y' C X : Scheme.{u}) [IsIntegral Y']
    (Q : MarkedNodalQuotientModel ell G Y Y' C X)
    (Y₁ : Scheme.{u}) [IsIntegral Y₁] [IsAffine Y₁] [IsNoetherian Y₁]
    (hregular : IsRegularScheme Y₁)
    (hexcellent : ∀ U : Y₁.affineOpens, IsExcellent Γ(Y₁, U))
    (u₁ : Y₁ ⟶ Y) [IsDominant u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (H₁ : Y₁.IdealSheafData) (hsnc : IsStrictNormalCrossingsBoundary H₁)
    (hsupport : (H₁.support : Set Y₁) = u₁ ⁻¹' (Q.T : Set Y))
    (Z : Set ↥(pullback (C := Scheme.{u}) Q.b u₁))
    (hZ : Z ∈ irreducibleComponents ↥(pullback (C := Scheme.{u}) Q.b u₁))
    (hdominant : Dense (pullback.snd Q.b u₁ '' Z))
    (F : Scheme.{u}) [IsIntegral F] (j : F ⟶ pullback Q.b u₁) [IsClosedImmersion j]
    (hcomponent : Set.range j = Z) :
    Nonempty (NormalizedNodalQuotientRefinement Q u₁ j Z) := by
  sorry

/-- A finite alteration cover of the base by regular pairs induces a cover by the
normalized decomposition-group quotients. Every refinement is the one specified above;
no assertion is made that an individual arbitrary dominant base change is a cover.
Source: ILO IX 1.4, p. 133; II 1.2.5--1.2.8 and 2.3.1
(blueprint: lem-per-nodal-quotient-normalized-base-refinement).

Proof: apply Step 16 of the node. Pull back the base covering using alteration cover
calculus, taking reduced dominant products. Generic geometric integrality identifies these
products with the dominant parts in the refinement records. Their proper birational
comparison maps are singleton alteration covers of degree one. Compose these covers and
the pulled-back family. The equalities in the conclusion retain the actual quotient maps. -/
theorem normalizedNodalQuotientRefinements_cover
    (ell : ℕ) [Fact ell.Prime] (G : Type v) [Group G] [Finite G]
    (Y Y' C X : Scheme.{u}) [IsIntegral Y'] [IsNoetherian Y]
    (Q : MarkedNodalQuotientModel ell G Y Y' C X)
    (n : ℕ) (baseY : PrimeToEllAlteration.Alt Y)
    (hbaseY : baseY.obj = Over.mk (𝟙 Y))
    (B : Fin n → PrimeToEllAlteration.Alt Y) (q : ∀ i, B i ⟶ baseY)
    (hcover : PrimeToEllAlteration.IsCoveringFamily ell B q)
    [hIntegral : ∀ i, IsIntegral (B i).obj.left]
    (hregular : ∀ i, IsRegularScheme (B i).obj.left)
    (hsnc : ∀ i, ∃ D : (B i).obj.left.IdealSheafData,
      IsStrictNormalCrossingsBoundary D ∧
        (D.support : Set (B i).obj.left) = (B i).obj.hom ⁻¹' (Q.T : Set Y))
    (Z : ∀ i, Set ↥(pullback (C := Scheme.{u}) Q.b (B i).obj.hom))
    (hZ : ∀ i, Z i ∈ irreducibleComponents ↥(pullback (C := Scheme.{u}) Q.b (B i).obj.hom))
    (hdominant : ∀ i, Dense (pullback.snd Q.b (B i).obj.hom '' Z i))
    (F : Fin n → Scheme.{u}) [hF : ∀ i, IsIntegral (F i)]
    (j : ∀ i, F i ⟶ pullback Q.b (B i).obj.hom)
    [hClosed : ∀ i, IsClosedImmersion (j i)]
    (hcomponent : ∀ i, Set.range (j i) = Z i)
    (R : ∀ i, NormalizedNodalQuotientRefinement Q (B i).obj.hom (j i) (Z i)) :
    ∃ hX : IsNoetherian X,
      ∃ baseX : @PrimeToEllAlteration.Alt X hX,
        baseX.obj = Over.mk (𝟙 X) ∧
        ∃ (V : Fin n → @PrimeToEllAlteration.Alt X hX) (r : ∀ i, V i ⟶ baseX),
          (∀ i, (V i).obj = Over.mk (R i).toOriginal) ∧
          @PrimeToEllAlteration.IsCoveringFamily X hX ell inferInstance (Fin n) baseX V r := by
  sorry

end AlgebraicGeometry
