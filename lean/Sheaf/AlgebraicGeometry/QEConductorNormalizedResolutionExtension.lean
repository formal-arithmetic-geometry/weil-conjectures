/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.AlgebraicGeometry.QENormalizedResolutionRule
public import Sheaf.TraceFormula.ConductorSmoothBaseChange
public import Sheaf.AlgebraicGeometry.NormalizedBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.NagataRing
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationProperties
import Sheaf.RingTheory.AnnihilatorFiniteFlatBaseChange
import Sheaf.AlgebraicGeometry.FiniteNormalizationQuotientLocalCriterion
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.RingTheory.RegularBaseChange
import WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Conductor-first extension of a normal-input resolution rule

Source: ILO, Travaux de Gabber, VIII 2.2.1--2.2.4, Lemma 2.2.9,
2.3.2--2.3.5 and Remark 2.3.12(i), pp.89--94; Stacks Tags 07QV and 07T8
(blueprint: lem-per-qe-conductor-normalized-resolution-extension).

The preparation scheme is the existing normalized blowup of the existing conductor
ideal. Its input record has that actual scheme and the composite rational structure
map; only its properties are postponed. Extension is specified by all tail levels,
arrows and ideals, and by the conductor stage exactly when the conductor is nonunit.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Monoscheme

/-- The geometric assertions about the normalization conductor and its normalized blowup.
Normality means normal-domain stalks, including on disconnected or empty schemes.
Source: ILO VIII 2.2.1--2.2.4; Stacks 07QV, 035S and 07T8
(blueprint: lem-per-qe-conductor-normalized-resolution-extension). -/
structure QEConductorGeometry (X : QEResolutionInput.{u}) : Prop where
  finite : IsFinite X.scheme.fromReducedNormalization
  coherent : RingedSpace.IsCoherent X.scheme.toRingedSpace (conductorIdeal X.scheme).toModules
  support : ∀ x : X.scheme, x ∈ ((conductorIdeal X.scheme).support : Set X.scheme) ↔
    ¬ (IsDomain (X.scheme.presheaf.stalk x) ∧ IsIntegrallyClosed (X.scheme.presheaf.stalk x))
  nowhereDense : IsNowhereDense ((conductorIdeal X.scheme).support : Set X.scheme)
  unit_iff : conductorIdeal X.scheme = ⊤ ↔ ∀ x : X.scheme,
    IsDomain (X.scheme.presheaf.stalk x) ∧ IsIntegrallyClosed (X.scheme.presheaf.stalk x)
  normal : ∀ x : (conductorIdeal X.scheme).normalizedBlowup,
    IsDomain ((conductorIdeal X.scheme).normalizedBlowup.presheaf.stalk x) ∧
      IsIntegrallyClosed ((conductorIdeal X.scheme).normalizedBlowup.presheaf.stalk x)
  reduced : IsReduced (conductorIdeal X.scheme).normalizedBlowup
  noetherian : IsNoetherian (conductorIdeal X.scheme).normalizedBlowup
  quasiExcellent : ∀ U : (conductorIdeal X.scheme).normalizedBlowup.affineOpens,
    IsQuasiExcellent Γ((conductorIdeal X.scheme).normalizedBlowup, U.1)
  finiteType : LocallyOfFiniteType (conductorIdeal X.scheme).normalizedBlowupMap
  quasiCompact : QuasiCompact (conductorIdeal X.scheme).normalizedBlowupMap

/-- Geometry of conductor preparation on every reduced Noetherian quasi-excellent input.
Source: ILO VIII 2.2.1--2.2.4; Stacks 07QV, 035S and 07T8
(blueprint: lem-per-qe-conductor-normalized-resolution-extension).

Proof (node steps 1--4):
1. By lem-exc-quasi-excellent-nagata every affine ring is Nagata. Its minimal-prime
quotients are N-2, hence N-1 by the degree-one extension in
 def-weil-pbc-japanese-domain. The finite product description in
lem-per-componentwise-normalization-affine-charts makes the normalization finite.
2. Apply lem-trf-finite-normalization-quotient-local-criterion: the normalization
cokernel is coherent and vanishes at a point exactly when the stalk is a normal domain.
3. By lem-weil-pbc-scheme-theoretic-support its annihilator cuts out precisely this
support. Affine Noetherianity makes the ideal finitely generated, so
pqf-lem-coherent-ft-locnoeth gives coherence. At generic points the reduced local
rings are fields, and lem-per-componentwise-normalization-properties identifies the
normalization there. The closed support thus misses all generic points and is nowhere
dense. It is empty exactly when the ideal is unit, exactly when X is normal.
4. By lem-per-reduced-noetherian-blowup-geometry the ordinary blowup is reduced,
Noetherian and finite type over X. Apply lem-per-quasi-excellent-finite-type-stability;
step 1 now makes its normalization finite. A finite algebra is finite type using its
module generators, and finite-type maps compose. Apply finite-type stability again.
Normality is lem-per-componentwise-normalization-properties, and normal-domain stalks
are reduced. The rational structure map is the composite through X. -/
theorem qeConductor_geometry (X : QEResolutionInput.{u}) : QEConductorGeometry X := by
  sorry

/-- The actual conductor preparation, with rational structure map composed through X.
Its scheme data is the prescribed normalized blowup, not an existence choice.
Source: ILO VIII 2.2.3 and 2.3.12(i)
(blueprint: lem-per-qe-conductor-normalized-resolution-extension). -/
noncomputable def conductorPreparedInput (X : QEResolutionInput.{u}) :
    QEResolutionInput.{u} where
  scheme := (conductorIdeal X.scheme).normalizedBlowup
  structureMap := (conductorIdeal X.scheme).normalizedBlowupMap ≫ X.structureMap
  reduced := (qeConductor_geometry X).reduced
  noetherian := (qeConductor_geometry X).noetherian
  quasiExcellent := (qeConductor_geometry X).quasiExcellent

/-- Conductor preparation as a normal input for the supplied resolution rule.
Source: ILO VIII 2.2.3 and 2.3.12(i)
(blueprint: lem-per-qe-conductor-normalized-resolution-extension). -/
noncomputable def normalConductorPreparedInput (X : QEResolutionInput.{u}) :
    NormalQEResolutionInput.{u} :=
  ⟨conductorPreparedInput X, (qeConductor_geometry X).normal⟩

/-- The canonical conductor preparation square for a regular morphism. The square
characterizes the comparison uniquely, and its top map is regular and preserves
surjectivity. There is no finite-type hypothesis on h.
Source: ILO VIII Lemma 2.2.9; Stacks 07T8 and 07C1
(blueprint: lem-per-qe-conductor-normalized-resolution-extension).

Proof (node steps 6--7): normalization commutes with regular base change by
lem-per-normalized-tower-regular-pullback. Use
lem-weil-pbc-affine-pushforward-base-change on the finite normalization and
lem-weil-pbc-flat-tensor-exact to identify its quotient after pullback. The affine
criterion lem-weil-pbc-flat-morphism-affine-criterion and
lem-trf-annihilator-finite-flat-base-change then give the conductor equality; these
canonical local identifications glue. Apply the same normalized tower comparison to
the single conductor stage. Regularity of the top projection is
lem-weil-pbc-regular-base-change, applied along the finite-type map P(X) → X,
not along h. Surjectivity is lem-weil-pbc-surjective-base-change. Uniqueness is
uniqueness of the normalized blowup comparison over the common dense open; it makes
the squares compatible with identities and composition. -/
theorem qeConductor_regularBaseChange (X Y : QEResolutionInput.{u})
    (h : Y.scheme ⟶ X.scheme) (hr : IsRegularSchemeMorphism h) :
    conductorIdeal Y.scheme = (conductorIdeal X.scheme).comap h ∧
      ∃! k : (conductorPreparedInput Y).scheme ⟶ (conductorPreparedInput X).scheme,
        IsPullback k (conductorIdeal Y.scheme).normalizedBlowupMap
          (conductorIdeal X.scheme).normalizedBlowupMap h ∧
        IsRegularSchemeMorphism k ∧ (Surjective h → Surjective k) := by
  sorry

/-- The initial conductor stage is absent exactly for the unit conductor.
The explicit classical decision is part of this real construction, not a local instance.
Source: ILO VIII 2.2.3, 2.3.2 and 2.3.4, conductor-first assembly
(blueprint: lem-per-qe-conductor-normalized-resolution-extension). -/
noncomputable def conductorStageCount (X : QEResolutionInput.{u}) : ℕ :=
  @ite ℕ (conductorIdeal X.scheme = ⊤) (Classical.propDecidable _) 0 1

/-- Exact conductor-prepending specification. The ordered embeddings identify every
level and center of N(P(X)) with the tail. Their values are shifted by one exactly
when D_X is nonunit. The length equation leaves no other stages. The first center and
map are precisely the conductor and P(X) → X. In the unit case the entire tail is
identified over X through that same map, so its omission uses P(X) ≅ X.
Source: ILO VIII 2.2.3, 2.3.2 and 2.3.4, conductor-first assembly
(blueprint: lem-per-qe-conductor-normalized-resolution-extension). -/
structure IsConductorResolutionExtension (X : QEResolutionInput.{u})
    (A : QENormalizedResolutionTower (conductorPreparedInput X).scheme)
    (B : QENormalizedResolutionTower X.scheme) where
  levelIndex : Fin (A.length + 1) ↪o Fin (B.length + 1)
  stageIndex : Fin A.length ↪o Fin B.length
  length : B.length = A.length + conductorStageCount X
  levelValue : ∀ i, (levelIndex i).val =
    i.val + conductorStageCount X
  stageValue : ∀ i, (stageIndex i).val =
    i.val + conductorStageCount X
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

/-- A regular-functorial normalized resolution on normal quasi-excellent rational
inputs extends to all reduced Noetherian quasi-excellent rational inputs by the
specified conductor preparation, omitting its first stage exactly for unit conductor.
Source: ILO VIII 2.2.1--2.2.4, Lemma 2.2.9, 2.3.2--2.3.5, Remark 2.3.12(i),
pp.89--94; Stacks 07QV and 07T8
(blueprint: lem-per-qe-conductor-normalized-resolution-extension).

Proof (node steps 1--10):
1--4. Apply qeConductor_geometry (the first four node steps, detailed above) to
obtain finite normalization, the coherent conductor and its nowhere dense nonnormal
locus, and the normal quasi-excellent finite-type preparation P(X).
5. Prepend P(X) → X to N(P(X)). If the conductor is unit, X is normal. The ordinary
unit blowup is an isomorphism by cor-nagata-blowup-cartier-iso; normalization of a
normal scheme is an isomorphism by lem-per-componentwise-normalization-properties.
Omit exactly this stage. Otherwise its zero scheme is nonempty and nowhere dense.
The tail has the required centers and regular last level by the hypothesis on N.
For the empty input its conductor is unit, its preparation is empty, and N is trivial.
6--7. Apply qeConductor_regularBaseChange (node steps 6--7, detailed above) to a
regular h:Y → X: the conductor extends, the preparation square is cartesian, and
the normal-input map is regular, and surjective when h is.
8. Compare the initial conductor stages in the three cases: conductor unit on X;
nonunit on both inputs; nonunit on X but unit on Y. In the last case delete the
unit normalized blowup on the normal scheme Y. Apply N's comparison to the regular
normal-input map. Induct on the finite tail: the extended ideals agree in order,
and their normalized blowups give the next identified levels. Unit tail centers
have normal bases and are isomorphisms; delete precisely these stages.
9. Identity comparisons are identities. For a composite, extending an ideal twice
is extending along the composite, and unit ideals remain unit. The two successive
ordered deletions therefore equal deletion once over the final base. Combine this
with the identity and composition laws supplied by N on the normal-input maps.
10. If h is surjective, a point in the nonempty conductor locus has a preimage;
the local homomorphism sends its proper conductor stalk into the maximal ideal.
The extended conductor is nonunit, so the initial stage survives. The top normal-input
map is surjective, so N deletes no tail stage. This also covers the unit-conductor
and empty-to-empty cases. All input quantifiers include finite disjoint unions;
there is no synchronization or equidimensionality assumption. -/
theorem qeConductor_normalizedResolution_extension
    (N : RegularNormalizedResolutionRule NormalQEResolutionInput.{u}
      (fun X ↦ X.val.scheme)) :
    ∃ H : RegularNormalizedResolutionRule QEResolutionInput.{u} (fun X ↦ X.scheme),
      ∀ X : QEResolutionInput.{u}, Nonempty (IsConductorResolutionExtension X
        (N.tower (normalConductorPreparedInput X)) (H.tower X)) := by
  sorry

end AlgebraicGeometry
