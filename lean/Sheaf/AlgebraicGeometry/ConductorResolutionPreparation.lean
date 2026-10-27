/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.SmoothNormalizedResolutionRule
public import Sheaf.TraceFormula.ConductorSmoothBaseChange
public import Sheaf.AlgebraicGeometry.NormalizedBlowup
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Extending a normal-input resolution by the conductor stage

Source: ILO, Exposé VIII, 2.2.3--2.2.9, 2.3.4--2.3.5(i), 2.3.12(i),
pp.90--93; conductor-prepending refinement using Stacks Tag 07T8
(blueprint: lem-trf-conductor-extension-of-normalized-resolution).

Preparation uses the actual normalized blowup of the published conductor ideal.
The extension specification records every tail level, arrow and ordered center.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite type over the rational field implies Noetherianity.
Source: Stacks Tag 01T6
(blueprint: lem-trf-conductor-extension-of-normalized-resolution). -/
private theorem rationalInput_noetherian (X : RationalResolutionInput.{u}) :
    IsNoetherian X.scheme := by
  have := X.finiteType
  have := X.quasiCompact
  have : IsLocallyNoetherian X.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian X.structureMap
  have : CompactSpace X.scheme :=
    QuasiCompact.compactSpace_of_compactSpace X.structureMap
  exact ⟨⟩

/-- Every affine ideal of a rational input is finitely generated.
Source: Stacks Tag 01T6 and the definition of a Noetherian ring
(blueprint: lem-trf-conductor-extension-of-normalized-resolution). -/
private theorem rationalInput_ideal_fg (X : RationalResolutionInput.{u})
    (J : X.scheme.IdealSheafData) (U : X.scheme.affineOpens) : (J.ideal U).FG := by
  have := rationalInput_noetherian X
  have := IsLocallyNoetherian.component_noetherian U
  exact IsNoetherian.noetherian _

/-- Properties of the conductor and its preparation on a reduced finite-type rational
scheme. Normality means normal-domain stalks, including the empty and disconnected cases.
Source: ILO VIII 2.2.3--2.2.9 and Stacks 07T8
(blueprint: lem-trf-conductor-extension-of-normalized-resolution). -/
structure RationalConductorGeometry (X : RationalResolutionInput.{u}) : Prop where
  coherent : RingedSpace.IsCoherent X.scheme.toRingedSpace (conductorIdeal X.scheme).toModules
  nowhereDense : IsNowhereDense ((conductorIdeal X.scheme).support : Set X.scheme)
  unit_iff : conductorIdeal X.scheme = ⊤ ↔ ∀ x : X.scheme,
    IsDomain (X.scheme.presheaf.stalk x) ∧ IsIntegrallyClosed (X.scheme.presheaf.stalk x)
  normal : ∀ x : (conductorIdeal X.scheme).normalizedBlowup,
    IsDomain ((conductorIdeal X.scheme).normalizedBlowup.presheaf.stalk x) ∧
      IsIntegrallyClosed ((conductorIdeal X.scheme).normalizedBlowup.presheaf.stalk x)
  reduced : IsReduced (conductorIdeal X.scheme).normalizedBlowup
  finiteType : LocallyOfFiniteType
    ((conductorIdeal X.scheme).normalizedBlowupMap ≫ X.structureMap)
  quasiCompact : QuasiCompact
    ((conductorIdeal X.scheme).normalizedBlowupMap ≫ X.structureMap)

/-- The conductor is coherent and nowhere dense, is unit exactly on a normal input,
and its normalized blowup is normal, reduced and finite type over the rationals.
Source: ILO VIII 2.2.3--2.2.9 and Stacks 07T8
(blueprint: lem-trf-conductor-extension-of-normalized-resolution).

Proof (node steps 1--2): Spec ℚ is Noetherian; finite-type inputs are Noetherian by
lem-weil-pbc-finite-type-over-noetherian. Apply lem-trf-conductor-smooth-base-change
to its normalization cokernel and annihilator. Its coherence and nowhere density are
exactly the hypotheses of lem-trf-normalized-blowup-calculus, which gives the normal,
reduced finite-type preparation. The unit case identifies preparation with the input. -/
theorem rationalConductor_geometry (X : RationalResolutionInput.{u}) :
    RationalConductorGeometry X := by
  have := X.reduced
  have := X.finiteType
  have := X.quasiCompact
  obtain ⟨_, _, _, hc, _, hd, hu, _⟩ :=
    conductor_smooth_base_change X.scheme X.structureMap
  have hdense : Dense ((conductorIdeal X.scheme).support.compl : Set X.scheme) :=
    interior_eq_empty_iff_dense_compl.mp
      ((conductorIdeal X.scheme).support.isClosed.isNowhereDense_iff.mp hd)
  obtain ⟨hn, hr, hf, hq, _⟩ :=
    Scheme.IdealSheafData.normalizedBlowup_calculus X.scheme X.structureMap
      (conductorIdeal X.scheme) (rationalInput_ideal_fg X _) hdense
  exact ⟨hc, hd, hu, hn, hr, hf, hq⟩

/-- The preparation has the actual normalized conductor blowup and composite rational
structure map. Only its properties, not its data, use the preceding theorem.
Source: ILO VIII 2.2.3, conductor-prepending refinement
(blueprint: lem-trf-conductor-extension-of-normalized-resolution). -/
noncomputable def conductorPreparedRationalInput (X : RationalResolutionInput.{u}) :
    RationalResolutionInput.{u} where
  scheme := (conductorIdeal X.scheme).normalizedBlowup
  structureMap := (conductorIdeal X.scheme).normalizedBlowupMap ≫ X.structureMap
  reduced := (rationalConductor_geometry X).reduced
  finiteType := (rationalConductor_geometry X).finiteType
  quasiCompact := (rationalConductor_geometry X).quasiCompact

/-- Preparation is a normal input for the given rule.
Source: ILO VIII 2.2.3--2.2.4
(blueprint: lem-trf-conductor-extension-of-normalized-resolution). -/
noncomputable def normalConductorPreparedRationalInput (X : RationalResolutionInput.{u}) :
    NormalRationalResolutionInput.{u} :=
  ⟨conductorPreparedRationalInput X, (rationalConductor_geometry X).normal⟩

/-- Conductor extension and the canonical smooth preparation square.
Source: ILO VIII 2.2.9 and Stacks 07T8
(blueprint: lem-trf-conductor-extension-of-normalized-resolution).

Proof (node steps 1 and 4): a smooth map between these inputs is quasi-compact:
its source is Noetherian, and the inverse image of every affine is quasi-compact by
lem-weil-pbc-noetherian-open-subscheme-noetherian. Thus
lem-trf-conductor-smooth-base-change gives the ideal equality. Apply
lem-trf-normalized-blowup-calculus to obtain the cartesian comparison, its smoothness
and uniqueness over the base. This uniqueness gives identities and composition. -/
theorem rationalConductor_smoothBaseChange (X Y : RationalResolutionInput.{u})
    (h : Y.scheme ⟶ X.scheme) (hh : Smooth h) :
    conductorIdeal Y.scheme = (conductorIdeal X.scheme).comap h ∧
      ∃! k : (conductorPreparedRationalInput Y).scheme ⟶
          (conductorPreparedRationalInput X).scheme,
        IsPullback k (conductorIdeal Y.scheme).normalizedBlowupMap
          (conductorIdeal X.scheme).normalizedBlowupMap h ∧ Smooth k := by
  have := X.reduced
  have := X.finiteType
  have := X.quasiCompact
  have := hh
  have := rationalInput_noetherian Y
  obtain ⟨_, _, _, _, _, hd, _, hbase, _⟩ :=
    conductor_smooth_base_change X.scheme X.structureMap
  have heq := hbase Y.scheme h inferInstance hh
  refine ⟨heq, ?_⟩
  have hdense : Dense ((conductorIdeal X.scheme).support.compl : Set X.scheme) :=
    interior_eq_empty_iff_dense_compl.mp
      ((conductorIdeal X.scheme).support.isClosed.isNowhereDense_iff.mp hd)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ :=
    Scheme.IdealSheafData.normalizedBlowup_calculus X.scheme X.structureMap
      (conductorIdeal X.scheme) (rationalInput_ideal_fg X _) hdense
  obtain ⟨_, _, _, _, hb, hbSquare⟩ := hs Y.scheme h
  change ∃! k : (conductorIdeal Y.scheme).normalizedBlowup ⟶
      (conductorIdeal X.scheme).normalizedBlowup,
    IsPullback k (conductorIdeal Y.scheme).normalizedBlowupMap
      (conductorIdeal X.scheme).normalizedBlowupMap h ∧ Smooth k
  rw [heq]
  obtain ⟨b, hbfac, hbuniq⟩ := hb
  refine ⟨b, hbSquare b hbfac, ?_⟩
  intro b' hb'
  exact hbuniq b' hb'.1.w

/-- The number of conductor stages is zero exactly for the unit ideal, otherwise one.
Source: ILO VIII 2.3.4, conductor-prepending refinement
(blueprint: lem-trf-conductor-extension-of-normalized-resolution). -/
noncomputable def rationalConductorStageCount (X : RationalResolutionInput.{u}) : ℕ :=
  @ite ℕ (conductorIdeal X.scheme = ⊤) (Classical.propDecidable _) 0 1

/-- Exact conductor-prepending specification. The order embeddings identify all tail
levels and centers, shifted by the conductor stage count. The length equation excludes
extra stages. In the unit case the base is transported through P(X) ≅ X. Otherwise
the first center and arrow are precisely the conductor and its normalized blowup.
This is the finite-type rational version of the quasi-excellent input specification;
the latter cannot be applied to a merely smooth-functorial rule.
Source: ILO VIII 2.2.3, 2.3.2--2.3.4, conductor-prepending refinement
(blueprint: lem-trf-conductor-extension-of-normalized-resolution). -/
structure IsRationalConductorResolutionExtension (X : RationalResolutionInput.{u})
    (A : QENormalizedResolutionTower (conductorPreparedRationalInput X).scheme)
    (B : QENormalizedResolutionTower X.scheme) where
  levelIndex : Fin (A.length + 1) ↪o Fin (B.length + 1)
  stageIndex : Fin A.length ↪o Fin B.length
  length : B.length = A.length + rationalConductorStageCount X
  levelValue : ∀ i, (levelIndex i).val =
    i.val + rationalConductorStageCount X
  stageValue : ∀ i, (stageIndex i).val =
    i.val + rationalConductorStageCount X
  before : ∀ i : Fin A.length, levelIndex i.castSucc = (stageIndex i).castSucc
  after : ∀ i : Fin A.length, levelIndex i.succ = (stageIndex i).succ
  tailIso : ∀ i, B.tower.level (levelIndex i) ≅ A.tower.level i
  tailArrow : ∀ i : Fin A.length,
    eqToHom (congrArg B.tower.level (after i)) ≫ B.tower.arrow (stageIndex i) ≫
      eqToHom (congrArg B.tower.level (before i).symm) ≫ (tailIso i.castSucc).hom =
        (tailIso i.succ).hom ≫ A.tower.arrow i
  tailCenter : ∀ i : Fin A.length,
    B.tower.center (stageIndex i) = (A.tower.center i).comap
      (eqToHom (congrArg B.tower.level (before i).symm) ≫ (tailIso i.castSucc).hom)
  unitBase : conductorIdeal X.scheme = ⊤ → ∃ hi : levelIndex 0 = 0,
    eqToHom (congrArg B.tower.level hi.symm) ≫ (tailIso 0).hom ≫ A.initial.hom ≫
      (conductorIdeal X.scheme).normalizedBlowupMap = B.initial.hom
  conductorStage : conductorIdeal X.scheme ≠ ⊤ →
    ∃ (j : Fin B.length) (hj : j.castSucc = 0) (hk : levelIndex 0 = j.succ),
      (B.tower.center j).comap (eqToHom (congrArg B.tower.level hj.symm)) =
        (conductorIdeal X.scheme).comap B.initial.hom ∧
      B.tower.arrow j ≫ eqToHom (congrArg B.tower.level hj) ≫ B.initial.hom =
        eqToHom (congrArg B.tower.level hk.symm) ≫ (tailIso 0).hom ≫ A.initial.hom ≫
          (conductorIdeal X.scheme).normalizedBlowupMap

end AlgebraicGeometry
