/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
- Stage-2 statement packet refreshed by group NV.
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import Sheaf.Paper.IntegralProperConstructibleHeartBound
import Sheaf.Paper.ContinuousIntegralLocalizationContinuity
import Sheaf.Paper.ContinuousIntegralScalarExact
import Sheaf.Paper.ContinuousConstructibleIntegralStratum
import Sheaf.Paper.ContinuousConstructibleIntegralGluing
import Sheaf.Paper.AdicConstructibilityPredicateComparison

import Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisSections
import Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts
import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
import Sheaf.Paper.CoefficientFiniteDescentObjects
import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts

/-!
# Proper direct-image bound for rational constructible module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound/
sk-lem-proper-heart-bound-rational.md (blueprint: det-proper-heart-bound-rational).

The two statements are the finite rational and algebraic-closure coefficient cases.
The integer dimension bound uses bottom for negative integers, since every nonempty
space has nonnegative Krull dimension. Thus negative bounds retain the empty-fibre case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CondensedRing

-- Keep scalar extension abstract while comparing coefficient-module functors.
attribute [local irreducible] Mod.extendScalars
  Functor.leftDerivedFunctorIsoMapDerivedCategory Functor.CommShift.ofIso
  Functor.mapDerivedCategorySingleFunctor CondensedRing.derivedComapLowerStarIso
  Mod.extendRestrictAdjunction
  CondensedRing.lowerStar Functor.rightDerivedFunctor Functor.mapDerivedCategory

private theorem source_empty_of_geometric_fibers_empty
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ ⊥) : IsEmpty X := by
  refine ⟨fun x ↦ ?_⟩
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (Y.residueField (p x)) (AlgebraicClosure (Y.residueField (p x))))) ≫
      Y.fromSpecResidueField (p x)
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := g) x
    (IsLocalRing.closedPoint (AlgebraicClosure (Y.residueField (p x)))) (by
      exact (Y.fromSpecResidueField_apply (p x) _).symm)
  have he : IsEmpty (TopologicalSpace.IrreducibleCloseds (pullback p g : Scheme.{u})) :=
    Order.krullDim_eq_bot_iff.mp (le_antisymm (hd (p x)) bot_le)
  exact he.false ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩

private theorem module_zero_of_empty {X : Scheme.{u}} [IsEmpty X]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : IsZero M := by
  have hX : IsZero M.X := by
    apply Sheaf.isZero_of_isZero_obj
    rintro ⟨T⟩
    have : IsEmpty T.left := ⟨fun t ↦ (inferInstance : IsEmpty X).false (T.hom t)⟩
    exact (isZero_zero _).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X T).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  exact (IsZero.iff_id_eq_zero _).2 (Mod.hom_ext _ _ (hX.eq_of_src _ _))

private theorem localization_preserves_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)))
    (hK : DerivedCategory.TStructure.t.plus K) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.lowerStar (integralCoeff ℓ E) p).rightDerivedFunctor.obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        ((integralScalarExtension ℓ E X).obj K))) := by
  let U : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y) :=
    Mod.comap (coefficientMap (integralScalarMap ℓ E) Y)
  apply U.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  have e := (derivedComapLowerStarIso (integralScalarMap ℓ E) p).app
    ((integralScalarExtension ℓ E X).obj K)
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor _ q).mapIso e)
  obtain ⟨hc⟩ := integralLocalization_push_homology_isColimit ℓ E p K hK q
  apply (IsZero.iff_id_eq_zero _).2
  apply hc.hom_ext
  intro i
  exact hq.eq_of_src _ _

private theorem qbar_scalar_preserves_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))
    (q : ℤ) (hq : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N)))) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N)))) := by
  classical
  obtain ⟨I, b, _, _, hcopower⟩ := exists_condensedQbar_scalar_basis_sections.{u} ℓ E
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)
  let B := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicSubfieldRingObj Y ℓ E)
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasColimitsOfSize.{u + 1, u + 1} B := IsGrothendieckAbelian.hasColimits B
  let : HasCoproducts.{u + 1} A := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  let : HasCoproducts.{u + 1} B := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  let : HasCoproducts.{u + 1} (DerivedCategory A) := derived_hasCoproducts
  let : HasCoproducts.{u + 1} (DerivedCategory B) := derived_hasCoproducts
  let F := (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor
  let T := DerivedCategory.singleFunctor A 0 ⋙ F ⋙ DerivedCategory.homologyFunctor B q
  let : PreservesColimit (Discrete.functor
      ((DerivedCategory.singleFunctor A 0).obj ∘ (fun _ : I ↦ N))) F :=
    condensed_boundedBelow_preservesCoproduct (Profinite.continuousMapRingObj E) p I 0
      (fun _ ↦ (DerivedCategory.singleFunctor A 0).obj N) (fun _ ↦ inferInstance)
  have : PreservesColimit (Discrete.functor (fun _ : I ↦ N) ⋙
      DerivedCategory.singleFunctor A 0) F :=
    preservesColimit_of_iso_diagram F (Discrete.compNatIsoDiscrete
      (fun _ : I ↦ N) (DerivedCategory.singleFunctor A 0)).symm
  have hz : IsZero (T.obj (∐ fun _ : I ↦ N)) := by
    apply (isColimitOfPreserves T (coproductIsCoproduct (fun _ : I ↦ N))).isZero_pt
    apply (CategoryTheory.Functor.isZero_iff _).mpr
    intro i
    exact hq
  have hi := hcopower X N
  -- Reuse the certified map, avoiding reconstruction of its scalar-action formula.
  let e := @asIso _ _ _ _ _ hi
  have he := hz.of_iso (T.mapIso e).symm
  let U : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClRingObj Y ℓ) ⥤ B :=
    Mod.comap (padicSubfieldRingObjToPadicAlgCl Y ℓ E)
  apply U.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  let K := (DerivedCategory.singleFunctor _ 0).obj
    ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N)
  let UX : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClRingObj X ℓ) ⥤ A :=
    Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  let es := (UX.mapDerivedCategorySingleFunctor 0).app
    ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N)
  let ep := (derivedComapLowerStarIso
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p).app K
  exact he.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    (ep ≪≫ F.mapIso es))

/-- The rational proper direct-image bound over a Noetherian source, with no base field.
Source: blueprint det-proper-heart-bound-rational, finite-field case; the base field of
`isZero_higherDirectImage_rational_of_isProper` only makes the source Noetherian
(blueprint: det-proper-heart-bound-rational). -/
theorem isZero_higherDirectImage_rational_of_isProper_of_isNoetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Y) [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))
    (hM : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let : NormedField E := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  by_cases hn : d < 0
  · let : IsEmpty X := source_empty_of_geometric_fibers_empty p (fun y ↦ by
      simpa only [if_pos hn] using hd y)
    exact ((DerivedCategory.singleFunctor _ 0 ⋙
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q).map_isZero (module_zero_of_empty _ M))
  have hd' (y : Y) : topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d.toNat : WithBot ℕ∞) := by
    simpa only [if_neg hn] using hd y
  -- Glue ordinary integral models, then reuse the integral completeness/torsion/Milnor bound.
  have hM' := ((adicConstructibilityPredicateComparison ℓ X
    (Profinite.continuousMapRingObj E) (.continuous E)).1 M).mpr hM
  obtain ⟨S, hS⟩ := hM'
  have hmodels := fun a ↦ continuousConstructible_integral_stratum ℓ E X
    (S.immersion a) _ (hS a)
  obtain ⟨N, hN, ⟨eN⟩⟩ := continuousConstructible_integral_gluing ℓ E X M S hmodels
  have hN' : IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X N :=
    ((adicConstructibilityPredicateComparison ℓ X
      (Profinite.padicIntegersRingObj ℓ E) (.integral E)).1 N).mp hN
  have hb := integralProperConstructibleHeartBound_of_isNoetherian ℓ E p d.toNat hd' N hN'
  have hv := DerivedCategory.isZero_of_isLE _ (2 * (d.toNat : ℤ) + 1) q
    (by omega) (hX := hb)
  -- The localization unit telescope transfers the same bound to E coefficients.
  have hl := localization_preserves_vanishing ℓ E p
    ((DerivedCategory.singleFunctor _ 0).obj N) (by
      exact ⟨0, inferInstance⟩) q hv
  let e := (Functor.singleFunctorCompLeftDerivedFunctorIso
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X))).app N ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eN
  exact hl.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.mapIso
      e)).symm


set_option linter.unusedVariables false in
/-- The proper direct-image bound for a finite subextension of Qbar_ell.
Source: blueprint main-20261015, sk-lem-proper-heart-bound-rational, finite rational case
(blueprint: det-proper-heart-bound-rational).

Proof plan, following the node:
1. If d < 0, all geometric fibres are empty. Surjectivity of field-extension spectra
   (lem-pc-field-extension-surjective) and its stability under base change
   (lem-weil-pbc-surjective-base-change) make every ordinary fibre empty, hence X empty.
   The empty-cover sheaf axiom makes all module sheaves and direct images zero.
   Otherwise put c = 2d+1. By det-proper-heart-bound-reduction it suffices to treat
   locally closed extensions by zero of lisse finite free integral lattices over every
   finite coefficient extension, their localizations, and their Qbar scalar extensions.
2. The internal-abelian-sheaf-module equivalence identifies the module-object and
   ring-sheaf-module categories, preserving underlying sheaves and injective resolutions
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence). Grothendieck abelianness
   and enough injectives (lem-pur-ringed-site-grothendieck-abelian,
   lem-sp-grothendieck-enough-injectives) give nonnegative injective resolutions, which
   are K-injective (lem-sp-kinjective-computes). On an affine weakly contractible V over
   Y, exact evaluation and exact module forgetting identify sections of R^q p_* N with
   H^q of the section complex (det-pe-wc-sections-exact,
   lem-weil-pbc-module-sheaves-colimits-forgetful). Injective module sheaves are
   abelian-acyclic (lem-sc-injective-module-abelian-acyclic-zariski); the acyclic
   resolution criterion (lemma-weil-pbc-leray-acyclicity) and localization
   (lem-weil-pbc-cohomology-over-object-localization,
   lem-weil-proetale-weakly-etale-localization, clause 1) identify this with
   H^q(X_V,N restricted to X_V). This calculation is unchanged under scalar restriction.
3. Apply det-proper-heart-bound-lattice to each locally closed integral lattice.
   Its bound makes the groups of step 2 zero above c. Detection on weakly contractible
   sections (det-pe-sections-conservative, clause 3) gives zero higher direct images.
4. Properness implies qcqs: finite type is quasi-compact and the closed-immersion
   diagonal is quasi-compact (def-weil-proper-morphism, def-weil-finite-type-morphism,
   def-weil-closed-immersion, def-weil-quasi-separated-morphism). Apply
   det-proper-heart-continuity-direct-image through the module equivalence of step 2.
   Restriction along the coefficient unit is exact and colimit-preserving
   (sk-def-sfb-change-of-scalars), so continuity also holds for module-object images.
5. By sk-prop-sfb-qlbar-colimit-x and the balanced-tensor universal property
   (sk-def-sfb-change-of-scalars), inverting ell in a lattice is the filtered colimit
   of its multiplication-by-ell sequence. Continuity and step 3 give zero higher
   images above c. Step 2 identifies this with vanishing in rational coefficients.
6. For a finite extension F/K, det-prop-sfb-cartesian-coefficients-finite-free
   identifies F_X tensor N with a finite sum of copies of N as K_X-modules.
   Finite-sum continuity gives vanishing; step 2 detects it as F-module vanishing.
7. Finite extensions containing K are cofinal by finite composita. Hence Qbar_X is
   their filtered colimit (sk-prop-sfb-qlbar-colimit-x). Module forgetting creates this
   colimit (lem-weil-pbc-module-sheaves-colimits-forgetful); the balanced-tensor
   universal property commutes tensor with it. Continuity and step 6 give vanishing
   for Qbar scalar extension, with step 2 detecting it in Qbar-modules. All conditions
   of det-proper-heart-bound-reduction now hold, giving the assertion for every M.
   In the Qbar case the auxiliary initial field is Q_ell. -/
theorem isZero_higherDirectImage_rational_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (k : Type u) [Field k]
    (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))
    (hM : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  exact isZero_higherDirectImage_rational_of_isProper_of_isNoetherian ℓ E p d hd M hM q hq

/-- The algebraic-closure proper direct-image bound over a Noetherian source, with no base
field. Source: blueprint det-proper-heart-bound-rational, Qbar case; the base field only made
the source Noetherian (blueprint: det-proper-heart-bound-rational). -/
theorem isZero_higherDirectImage_padicAlgCl_of_isProper_of_isNoetherian
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Y) [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have hcomp := adicConstructibilityPredicateComparison ℓ X
    (Profinite.padicAlgClRingObj ℓ) .algebraicClosure
  have hm := (hcomp.1 M).mpr hM
  let K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj M, by
      rw [← hcomp.2]
      refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · exact isConstructibleModuleObject_of_isZero _
          (DerivedCategory.isZero_of_isGE _ 0 n hn)
      · exact IsConstructibleModuleObject.of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hm
      · exact isConstructibleModuleObject_of_isZero _
          (DerivedCategory.isZero_of_isLE _ 0 n hn)⟩
  -- Exact finite-coefficient descent of M[0] gives an ordinary model after taking H⁰.
  obtain ⟨E, L, ⟨eL⟩⟩ :=
    (coefficient_finite_descent_objects_of_isNoetherian ℓ X).1 K
  let N := (DerivedCategory.homologyFunctor _ 0).obj L.obj
  have hN : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X N :=
    L.property.2 0
  let eN : (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj N ≅ M :=
    (Functor.leftDerivedFunctorHomologyFunctorIso
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)) 0).app L.obj ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso eL ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M
  have hz := qbar_scalar_preserves_vanishing ℓ E p N q
    (isZero_higherDirectImage_rational_of_isProper_of_isNoetherian ℓ E p d hd N hN q hq)
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
    ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso eN))).symm


set_option linter.unusedVariables false in
/-- The proper direct-image bound for the finite-subextension-valued condensed ring Qbar_ell.
Source: blueprint main-20261015, sk-lem-proper-heart-bound-rational, Qbar case
(blueprint: det-proper-heart-bound-rational).

Proof plan, following the node:
1. If d < 0, all geometric fibres are empty. Surjectivity of field-extension spectra
   (lem-pc-field-extension-surjective) and its stability under base change
   (lem-weil-pbc-surjective-base-change) make every ordinary fibre empty, hence X empty.
   The empty-cover sheaf axiom makes all module sheaves and direct images zero.
   Otherwise put c = 2d+1. By det-proper-heart-bound-reduction it suffices to treat
   locally closed extensions by zero of lisse finite free integral lattices over every
   finite coefficient extension, their localizations, and their Qbar scalar extensions.
2. The internal-abelian-sheaf-module equivalence identifies the module-object and
   ring-sheaf-module categories, preserving underlying sheaves and injective resolutions
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence). Grothendieck abelianness
   and enough injectives (lem-pur-ringed-site-grothendieck-abelian,
   lem-sp-grothendieck-enough-injectives) give nonnegative injective resolutions, which
   are K-injective (lem-sp-kinjective-computes). On an affine weakly contractible V over
   Y, exact evaluation and exact module forgetting identify sections of R^q p_* N with
   H^q of the section complex (det-pe-wc-sections-exact,
   lem-weil-pbc-module-sheaves-colimits-forgetful). Injective module sheaves are
   abelian-acyclic (lem-sc-injective-module-abelian-acyclic-zariski); the acyclic
   resolution criterion (lemma-weil-pbc-leray-acyclicity) and localization
   (lem-weil-pbc-cohomology-over-object-localization,
   lem-weil-proetale-weakly-etale-localization, clause 1) identify this with
   H^q(X_V,N restricted to X_V). This calculation is unchanged under scalar restriction.
3. Apply det-proper-heart-bound-lattice to each locally closed integral lattice.
   Its bound makes the groups of step 2 zero above c. Detection on weakly contractible
   sections (det-pe-sections-conservative, clause 3) gives zero higher direct images.
4. Properness implies qcqs: finite type is quasi-compact and the closed-immersion
   diagonal is quasi-compact (def-weil-proper-morphism, def-weil-finite-type-morphism,
   def-weil-closed-immersion, def-weil-quasi-separated-morphism). Apply
   det-proper-heart-continuity-direct-image through the module equivalence of step 2.
   Restriction along the coefficient unit is exact and colimit-preserving
   (sk-def-sfb-change-of-scalars), so continuity also holds for module-object images.
5. By sk-prop-sfb-qlbar-colimit-x and the balanced-tensor universal property
   (sk-def-sfb-change-of-scalars), inverting ell in a lattice is the filtered colimit
   of its multiplication-by-ell sequence. Continuity and step 3 give zero higher
   images above c. Step 2 identifies this with vanishing in rational coefficients.
6. For a finite extension F/K, det-prop-sfb-cartesian-coefficients-finite-free
   identifies F_X tensor N with a finite sum of copies of N as K_X-modules.
   Finite-sum continuity gives vanishing; step 2 detects it as F-module vanishing.
7. Finite extensions containing K are cofinal by finite composita. Hence Qbar_X is
   their filtered colimit (sk-prop-sfb-qlbar-colimit-x). Module forgetting creates this
   colimit (lem-weil-pbc-module-sheaves-colimits-forgetful); the balanced-tensor
   universal property commutes tensor with it. Continuity and step 6 give vanishing
   for Qbar scalar extension, with step 2 detecting it in Qbar-modules. All conditions
   of det-proper-heart-bound-reduction now hold, giving the assertion for every M.
   In the Qbar case the auxiliary initial field is Q_ell. -/
theorem isZero_higherDirectImage_padicAlgCl_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  exact isZero_higherDirectImage_padicAlgCl_of_isProper_of_isNoetherian ℓ p d hd M hM q hq

end AlgebraicGeometry.ProEtale
