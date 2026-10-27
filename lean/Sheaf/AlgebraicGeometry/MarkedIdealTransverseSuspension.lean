/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Transverse suspension of a marked ideal

Source: ILO, Travaux de Gabber, VIII 2.3.11--2.3.13, pp. 93--94, and VIII 4.2.9,
p. 121; the explicit transverse-coordinate argument in the DAG
(blueprint: lem-trf-marked-ideal-transverse-suspension).

The split presentation is local data, not a global retraction hypothesis. The global
statement below assumes these data only on etale neighborhoods of the support, and the
unit ideal away from it. The separate chart statement gives the controlled-transform
formula with the actual ratios of the original transverse parameters.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.MarkedIdeal

open HilbertSamuel

/-- The displayed suspension ideal, constructed from the actual normal-coordinate powers
and the extended base ideal. Source: the displayed formula for J in the suspension node
(blueprint: lem-trf-marked-ideal-transverse-suspension). -/
def suspension {N Z : Scheme.{u}} (p : Z ⟶ N) {r : ℕ}
    (z : Fin r → Γ(Z, ⊤)) (I : N.IdealSheafData) (b : ℕ) : Z.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range fun j ↦ z j ^ b)) ⊔ I.comap p

/-- A split etale zero-section chart, compatible with each ordered boundary entry.
The cartesian zero-section square rules out additional zero fibers. Source: the etale
localization hypothesis in the suspension node
(blueprint: lem-trf-marked-ideal-transverse-suspension). -/
structure SuspensionChart {N Z : Scheme.{u}} (i : N ⟶ Z)
    (E : List Z.IdealSheafData) (r : ℕ) where
  retraction : Z ⟶ N
  parameters : Fin r → Γ(Z, ⊤)
  retracts : i ≫ retraction = 𝟙 N
  etale : Etale (AffineSpace.homOfVector retraction
    (fun j : ULift.{u} (Fin r) ↦ parameters j.down))
  zeroFiber : IsPullback i (𝟙 N)
    (AffineSpace.homOfVector retraction
      (fun j : ULift.{u} (Fin r) ↦ parameters j.down))
    (AffineSpace.homOfVector (𝟙 N) (fun _ : ULift.{u} (Fin r) ↦ 0))
  boundary : List N.IdealSheafData
  boundary_eq : E = boundary.map (fun D ↦ D.comap retraction)

/-- Etale-local split suspension of marked data on the full ambient. The isomorphism is
required to be the specified embedding of Q, so the ambient ideal is its actual transport.
Near every point of N the ideal has the displayed formula in a cartesian zero-section chart;
o global retraction is assumed. Outside N it is the unit ideal stalkwise.
Source: suspension-node Steps 1, 2 and 11
(blueprint: lem-trf-marked-ideal-transverse-suspension). -/
def IsLocallySuspended {k : Type u} [Field k] {S : Embedded k}
    (M Q : Marked S) (r : ℕ) : Prop :=
  ∃ e : Q.N ≅ S.Z, e.hom = Q.j ∧ Q.marking = M.marking ∧
    (∀ x : S.Z, x ∉ Set.range M.j → stalkIdeal (Q.ideal.comap e.inv) x = ⊤) ∧
    ∀ x : S.Z, x ∈ Set.range M.j →
      ∃ (W : Scheme.{u}) (v : W ⟶ S.Z) (_hv : Etale v) (w : W) (_hw : v w = x)
        (c : SuspensionChart (pullback.snd M.j v)
          (S.boundary.map (fun D ↦ D.comap v)) r),
        (Q.ideal.comap e.inv).comap v = suspension c.retraction c.parameters
          (M.ideal.comap (pullback.fst M.j v)) M.marking

/-- The smooth support regarded as an ambient for computing its ordered boundary transform.
Only the ambient and boundary fields enter `blowupBoundary`; the identity embedding carries
along the same formal retained level. Source: suspension-node Steps 6--8
(blueprint: lem-trf-marked-ideal-transverse-suspension). -/
def supportAmbient {k : Type u} [Field k] {S : Embedded k} (M : Marked S)
    (E : List M.N.IdealSheafData) : Embedded k where
  Z := M.N
  p := M.j ≫ S.p
  smooth := M.smooth
  X := M.N
  i := 𝟙 M.N
  closed := inferInstance
  level := S.level
  boundary := E

/-- Formula for the actual marked transforms of an admissible `Step`. The subsidiary theorem
requires `Step.Transforms` for both marked data, so their ideals are the controlled transforms
characterized by multiplication by the exceptional power. On the open charts, `e*z'=z`
specifies the ratios and the new suspended ideal uses the actual transformed base ideal.
Outside the strict support its ambient cosupport is empty. Ordered boundaries use the shared
`blowupBoundary`, on the original ambient and on the base blowup respectively.
Source: suspension-node Steps 6--8; ILO VIII 4.2.9, p.121
(blueprint: lem-trf-marked-ideal-transverse-suspension). -/
def HasAdmissibleChartFormula {k : Type u} [Field k] {S T : Embedded k}
    (M : Marked S) (M' Q' : Marked T) (s : Step S T) {r : ℕ}
    (c : SuspensionChart M.j S.boundary r) : Prop :=
  T.boundary = blowupBoundary s.π s.center ∧
  ∃ (f : s.center.subscheme ⟶ M.N) (_hf : f ≫ M.j = s.center.subschemeι)
    (a : M'.N ≅ f.ker.blowup),
    a.hom ≫ f.ker.blowupMap ≫ M.j = M'.j ≫ s.π ∧
    ∀ y : T.Z,
      (y ∉ Set.range M'.j → y ∉ Q'.cosupport) ∧
      (y ∈ Set.range M'.j →
        ∃ (U : T.Z.Opens) (_hy : y ∈ U) (q : U.toScheme ⟶ Q'.N)
          (p' : U.toScheme ⟶ M'.N) (e : Γ(U.toScheme, ⊤))
          (z' : Fin r → Γ(U.toScheme, ⊤)),
          q ≫ Q'.j = U.ι ∧
          s.center.comap (U.ι ≫ s.π) =
            Scheme.IdealSheafData.ofIdealTop (Ideal.span {e}) ∧
          (∀ j, e * z' j = (U.ι ≫ s.π).appTop (c.parameters j)) ∧
          e ∈ nonZeroDivisors (Γ(U.toScheme, ⊤)) ∧
          Q'.ideal.comap q = suspension p' z' M'.ideal M.marking ∧
          p' ≫ a.hom ≫ f.ker.blowupMap = U.ι ≫ s.π ≫ c.retraction ∧
          Etale (AffineSpace.homOfVector p'
            (fun j : ULift.{u} (Fin r) ↦ z' j.down)) ∧
          T.boundary.map (fun D ↦ D.comap U.ι) =
            (blowupBoundary (S := supportAmbient M c.boundary)
              f.ker.blowupMap f.ker).map (fun D ↦ D.comap (p' ≫ a.hom)))

/-- Transverse suspension preserves the order cosupport and every finite test sequence,
and has exact order b when the transverse rank is positive. The rank-zero assertion is
only equivalence; in a split chart the displayed ideal is the original ideal transported
by the retraction. Source: ILO VIII 2.3.11--2.3.13, pp. 93--94; explicit argument in the
DAG (blueprint: lem-trf-marked-ideal-transverse-suspension).

Proof plan, with all twelve steps of the node:
1. Etale stalk maps are flat by [lem-trf-etale-local-ring-flatness], faithfully flat by
   [lem-weil-pbc-flat-local-hom-faithfully-flat], and their maximal ideals are extended
   by [lem-weil-pbc-etale-prime-generates-maximal]. Contraction
   [lem-weil-pbc-faithfully-flat-ideal-contraction] preserves every order threshold.
2. Off the zero section a normal coordinate is a unit. On it apply the retraction to
   ideal containment in the bth maximal-ideal power to obtain the converse containment.
3. Work in the local polynomial zero-section model. Degree b shows z_1^b is not in the
   next maximal-ideal power. Flat base change of cotangent spaces gives the full regular
   parameter system, using [lem-weil-pbc-smooth-scheme-over-field-regular] and
   [lem-weil-pbc-regular-local-generators-regular-sequence].
4. A smooth center in cosupport factors through the support because it is reduced
   [lem-sc-regular-local-domain]. Use [lem-pur-smooth-pair-local-coordinates]; exchange
   cotangent-space basis members while retaining all boundary members to transfer normal
   crossings in both directions.
5. The center ideal is regular [lem-pur-smooth-pair-regular-immersion]. Its associated
   graded pieces are free over the regular domain of the center
   [lem-pur-regular-sequence-graded-polynomial]. A finite filtration, testing at the
   center's generic points, proves I is contained in its bth power, so division is regular.
6. Use [prop-nagata-affine-blowup-chart-cover], [lem-trf-permissible-coordinate-chart]
   and [thm-nagata-blowup-flat-base-change]. On a base-coordinate chart set z'=z/e;
   saturation by the nonzerodivisor e identifies the strict transform with z'=0. On a
   normal-coordinate chart it is empty. Smoothness follows from etale base change,
   [lem-weil-pbc-etale-smooth-zero-dimensional-fibres], [sbc-lem-affine-space-smooth]
   and [lem-trf-smooth-composition].
7. The principal extended center [lemma-nagata-chart-extended-ideal-principal] and its
   regular generator [lemma-nagata-chart-generator-regular] give e^(-b)J=(z'^b)+p'^*I'.
   Normal charts contain 1, hence have empty cosupport.
8. Strict boundary equations are ratios of center coordinates or unchanged coordinates;
   append the exceptional component, preserving order and transversality.
9. A line product pulls back every normal parameter and appends the horizontal zero
   section. The same calculation applies.
10. The shared Step uses two distinct labelled boundary components (the usual convention
    explicitly included in the node). Their intersection has only base coordinates.
    The projection is flat
    [lem-pc-smooth-flat]; blowup flat base change leaves z unchanged and pulls back I
    without division. Boundary chart substitutions preserve the product presentation.
11. Induct on the finite depth in EquivalentThrough. The same next centers are permitted
    and the same split
    invariant persists. Unit-ideal regions stay harmless. Glue the local calculations;
    [lem-trf-strict-transform-flat-etale-base-change] compares the actual schematic strict
    transforms, its generic-point condition following from faithful flatness.
12. For rank zero the split retraction is an isomorphism and J is transported I. Do not
    claim exact finite order for the zero ideal. Empty supports and empty centers cause
    no exception to the argument.
-/
theorem transverse_suspension
    {k : Type u} [Field k] [CharZero k] {S : Embedded k}
    (M Q : Marked S) (hfinite : QuasiCompact S.p)
    (hNfinite : QuasiCompact (M.j ≫ S.p))
    (hE : HasAdaptedNormalCrossingsCenter (⊥ : S.Z.IdealSheafData)
      (fun a ↦ S.boundary.get a))
    (htrans : HasAdaptedNormalCrossingsCenter (⊥ : M.N.IdealSheafData)
      (fun a ↦ (S.boundary.get a).comap M.j))
    (hEsmooth : ∀ D ∈ S.boundary, Smooth (D.subschemeι ≫ S.p))
    (r : ℕ) (hJ : IsLocallySuspended M Q r) :
    M.cosupport = Q.cosupport ∧ Equivalent M Q ∧ (0 < r → FullMaximalOrder Q) := by
  sorry

/-- The admissible-chart part of transverse suspension, on any specified split etale
neighborhood. Source: ILO VIII 4.2.9, p. 121, and suspension-node Steps 4--8
(blueprint: lem-trf-marked-ideal-transverse-suspension).

Proof: factor the smooth reduced center through N by cosupport equality (Step 4).
The regular-sequence filtration gives I in the bth center power (Step 5). On the
base-generator charts use the substitutions z'=z/e, with e a nonzerodivisor; saturation
identifies the strict transform, and division gives the asserted ideal (Steps 6--7).
The normal-generator charts have unit controlled transform and miss that support.
The boundary formulas preserve the split presentation (Step 8). These are the same
calculations and dependencies detailed in transverse_suspension's proof plan above.
-/
theorem transverse_suspension_admissible_charts
    {k : Type u} [Field k] [CharZero k] {S T : Embedded k}
    (M Q : Marked S) (M' Q' : Marked T) (s : Step S T)
    (hfinite : QuasiCompact S.p) (hNfinite : QuasiCompact (M.j ≫ S.p))
    (hE : HasAdaptedNormalCrossingsCenter (⊥ : S.Z.IdealSheafData)
      (fun a ↦ S.boundary.get a))
    (htrans : HasAdaptedNormalCrossingsCenter (⊥ : M.N.IdealSheafData)
      (fun a ↦ (S.boundary.get a).comap M.j))
    (hEsmooth : ∀ D ∈ S.boundary, Smooth (D.subschemeι ≫ S.p))
    (r : ℕ) (c : SuspensionChart M.j S.boundary r)
    (e : Q.N ≅ S.Z) (he : e.hom = Q.j) (hmark : Q.marking = M.marking)
    (hformula : Q.ideal.comap e.inv = suspension c.retraction c.parameters M.ideal M.marking)
    (hkind : s.kind = .admissibleBlowup) (hadm : s.Admissible M.cosupport)
    (hM' : s.Transforms M M') (hQ' : s.Transforms Q Q') :
    HasAdmissibleChartFormula M M' Q' s c := by
  sorry

/-- In rank zero the displayed ideal is just the original ideal under the split
retraction, without an exact-order assertion. Source: Step 12 of the suspension node
(blueprint: lem-trf-marked-ideal-transverse-suspension).

Proof: the coordinate index set is empty, so the generated normal ideal is zero;
its sum with the extended ideal is the extended ideal, as checked on every affine open.
The affine-space projection in dimension zero is an isomorphism. Its zero section is
an isomorphism since their composite is the identity. Pulling back this zero section
in `c.zeroFiber` makes `i` an isomorphism. Finally `i ≫ c.retraction = 𝟙 N`
makes the retraction the inverse of `i`.
-/
theorem transverse_suspension_rank_zero
    {N Z : Scheme.{u}} (i : N ⟶ Z) (E : List Z.IdealSheafData)
    (c : SuspensionChart i E 0) (I : N.IdealSheafData) (b : ℕ) :
    IsIso c.retraction ∧ suspension c.retraction c.parameters I b = I.comap c.retraction := by
  let z : N ⟶ AffineSpace (ULift.{u} (Fin 0)) N :=
    AffineSpace.homOfVector (𝟙 N) (fun _ ↦ 0)
  have hz : IsIso z := by
    have : IsIso (z ≫ (AffineSpace (ULift.{u} (Fin 0)) N ↘ N)) := by
      rw [show z ≫ (AffineSpace (ULift.{u} (Fin 0)) N ↘ N) = 𝟙 N from
        AffineSpace.homOfVector_over _ _]
      infer_instance
    exact IsIso.of_isIso_comp_right z (AffineSpace (ULift.{u} (Fin 0)) N ↘ N)
  have hi : IsIso i := c.zeroFiber.isIso_fst_of_isIso hz
  refine ⟨isIso_of_hom_comp_eq_id i c.retracts, ?_⟩
  have hzero : Scheme.IdealSheafData.ofIdealTop
      (Ideal.span (Set.range fun j : Fin 0 ↦ c.parameters j ^ b)) =
      (⊥ : Z.IdealSheafData) := by
    ext U
    simp
  unfold suspension
  rw [hzero, bot_sup_eq]

end AlgebraicGeometry.MarkedIdeal
