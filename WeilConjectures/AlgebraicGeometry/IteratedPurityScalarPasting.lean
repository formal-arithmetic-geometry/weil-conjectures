/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalTwistedPullbackCompositor
public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonData
public import WeilConjectures.AlgebraicGeometry.AdicPurityScalarNaturality
public import WeilConjectures.AlgebraicGeometry.NormalizedPurityScalarFamily
import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonIdentification
import WeilConjectures.AlgebraicGeometry.HorizontalScalarPasting

/-! # Scalar pasting for iterated smooth purity

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport,
composition-coherence transport; DAG proof Steps 1--8
(blueprint: lem-pur-iterated-purity-scalar-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures.IteratedPurityScalarPasting
open AdicPurityScalarNaturality RationalScalarComparisonIdentification
attribute [local irreducible] H G T Q alpha unit
  SourceLocalizationNormalization

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

/-- Unit, successive-extension and shift laws with the existing scalar associators.
This abbreviates the already recorded comparison-equation predicates.
Source: purity transport, final coherence clause
(blueprint: lem-pur-iterated-purity-scalar-pasting). -/
@[irreducible] def Coherent {V W : Scheme.{u}}
    (F : ∀ E : AdicPurityScalarNaturality.Field D C, RCat D C E V ⥤ RCat D C E W)
    (w : ∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
      F E ⋙ T D C E L h W ≅ T D C E L h V ⋙ F L)
    (s : ∀ E : AdicPurityScalarNaturality.Field D C, (F E).CommShift ℤ) : Prop :=
  (∀ E : AdicPurityScalarNaturality.Field D C,
    UnitEquation (w E E le_rfl) (unit D C E W) (unit D C E V)) ∧
  (∀ (E L M : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) (k : L ≤ M),
    CompositionEquation (w E L h) (w L M k) (w E M (h.trans k))
      (alpha D C E L M h k W) (alpha D C E L M h k V)) ∧
  (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
    ShiftCompatibility (F E ⋙ T D C E L h W) (T D C E L h V ⋙ F L)
      (composeShift _ _ (s E) (tShift D C E L h W))
      (composeShift _ _ (tShift D C E L h V) (s L)) (w E L h))

section SingleCoherence
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (I : Data D C f d S)

/-- The specified single-morphism coefficient laws and exceptional counit mate.
Source: purity transport, the comparison normalizations retained in both squares
(blueprint: lem-pur-iterated-purity-scalar-pasting). -/
@[irreducible] def SingleCoherent : Prop :=
  Coherent D C (H D C f d) (family D C f d S I).a (family D C f d S I).shift ∧
  Coherent D C (G D C f S) (b D C f S) (gShift D C f S) ∧
  (∀ E : AdicPurityScalarNaturality.Field D C,
    ShiftCompatibility (H D C f d E) (G D C f S E)
      ((family D C f d S I).shift E) (gShift D C f S E)
      ((family D C f d S I).gamma E)) ∧
  (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) (K : RCat D C E Y),
    (b D C f S E L h).hom.app K = coefficientTranspose D C f S E L h K)

private theorem single_laws :
    SingleCoherent D C f d S I ∧
    ∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L),
      PuritySquares ((family D C f d S I).gamma E) ((family D C f d S I).gamma L)
        ((family D C f d S I).a E L h) (b D C f S E L h) := by
  obtain ⟨s, _, loc, hn, hs, _, sloc, _, _, _, _, _, gam, hgam, hg, a,
    haS, hbS, haN, _, _, hbM, hSq, haU, hbU, haC, hbC⟩ :=
      rationalScalarComparisonIdentification D C f d S I
  let V : Family D C f d S I := ⟨s, loc, hn, hs, gam, hg, a, haN⟩
  have he : V = family D C f d S I := by
    unfold family
    exact (family_existsUnique D C f d S I).unique trivial
      (family_existsUnique D C f d S I).exists.choose_spec
  have hv :
      (Coherent D C (H D C f d) V.a V.shift ∧
        Coherent D C (G D C f S) (b D C f S) (gShift D C f S) ∧
        (∀ E, ShiftCompatibility (H D C f d E) (G D C f S E)
          (V.shift E) (gShift D C f S E) (V.gamma E)) ∧
        (∀ E L h K, (b D C f S E L h).hom.app K =
          coefficientTranspose D C f S E L h K)) ∧
      ∀ E L h, PuritySquares (V.gamma E) (V.gamma L) (V.a E L h)
        (b D C f S E L h) := by
    unfold Coherent
    exact ⟨⟨⟨haU, haC, haS⟩, ⟨hbU, hbC, hbS⟩, hgam, hbM⟩, hSq⟩
  rw [he] at hv
  unfold SingleCoherent
  exact hv

end SingleCoherence

section Composite
variable {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
  (Sf : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (Sg : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := g))
  (Sc : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f ≫ g))
  (If : Data D C f d Sf) (Ig : Data D C g e Sg) (Ic : Data D C (f ≫ g) (d + e) Sc)

/-- The recorded canonical compositor, in the existing H coordinates.
Source: purity transport, canonical u
(blueprint: lem-pur-iterated-purity-scalar-pasting). -/
@[irreducible] def u (E : AdicPurityScalarNaturality.Field D C) :
    H D C (f ≫ g) (d + e) E ≅ H D C g e E ⋙ H D C f d E := by
  unfold H
  exact RationalTwistedPullback.compositor C.l E.val f g d e

/-- Horizontal composition in the stated order Hf(gamma_g), then gamma_f at Gg.
Source: purity transport, q (blueprint: lem-pur-iterated-purity-scalar-pasting). -/
@[irreducible] def q (E : AdicPurityScalarNaturality.Field D C) :
    H D C g e E ⋙ H D C f d E ≅ G D C g Sg E ⋙ G D C f Sf E :=
  isoWhiskerRight ((family D C g e Sg Ig).gamma E) (H D C f d E) ≪≫
    isoWhiskerLeft (G D C g Sg E) ((family D C f d Sf If).gamma E)

/-- The prescribed horizontal scalar comparison A.
Source: purity transport, A (blueprint: lem-pur-iterated-purity-scalar-pasting). -/
@[irreducible] def A (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) :
    (H D C g e E ⋙ H D C f d E) ⋙ T D C E L h X ≅
      T D C E L h Z ⋙ (H D C g e L ⋙ H D C f d L) :=
  isoWhiskerLeft (H D C g e E) ((family D C f d Sf If).a E L h) ≪≫
    isoWhiskerRight ((family D C g e Sg Ig).a E L h) (H D C f d L)

/-- The prescribed horizontal exceptional scalar comparison beta.
Source: purity transport, beta (blueprint: lem-pur-iterated-purity-scalar-pasting). -/
@[irreducible] def beta (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) :
    (G D C g Sg E ⋙ G D C f Sf E) ⋙ T D C E L h X ≅
      T D C E L h Z ⋙ (G D C g Sg L ⋙ G D C f Sf L) :=
  isoWhiskerLeft (G D C g Sg E) (b D C f Sf E L h) ≪≫
    isoWhiskerRight (b D C g Sg E L h) (G D C f Sf L)

/-- Both pasting equations on every rational object, including the normalized
unit, tower and shift identifications of their horizontal comparisons. Naturality
is retained by using natural isomorphisms for u, q, A and beta.
Source: purity transport, the two coefficient-pasting equations and final clause
(blueprint: lem-pur-iterated-purity-scalar-pasting). -/
@[irreducible] def Result : Prop :=
  SingleCoherent D C f d Sf If ∧
  SingleCoherent D C g e Sg Ig ∧
  SingleCoherent D C (f ≫ g) (d + e) Sc Ic ∧
  (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) (K : RCat D C E Z),
    (T D C E L h X).map ((u D C f g d e E).hom.app K) ≫
        (A D C f g d e Sf Sg If Ig E L h).hom.app K =
      ((family D C (f ≫ g) (d + e) Sc Ic).a E L h).hom.app K ≫
        (u D C f g d e L).hom.app
          ((T D C E L h Z).obj K)) ∧
  (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) (K : RCat D C E Z),
    (T D C E L h X).map ((q D C f g d e Sf Sg If Ig E).hom.app K) ≫
        (beta D C f g Sf Sg E L h).hom.app K =
      (A D C f g d e Sf Sg If Ig E L h).hom.app K ≫
        (q D C f g d e Sf Sg If Ig L).hom.app ((T D C E L h Z).obj K)) ∧
  Coherent D C (fun E ↦ H D C g e E ⋙ H D C f d E)
    (A D C f g d e Sf Sg If Ig)
    (fun E ↦ composeShift _ _ ((family D C g e Sg Ig).shift E)
      ((family D C f d Sf If).shift E)) ∧
  Coherent D C (fun E ↦ G D C g Sg E ⋙ G D C f Sf E)
    (beta D C f g Sf Sg)
    (fun E ↦ composeShift _ _ (gShift D C g Sg E) (gShift D C f Sf E)) ∧
  (∀ E : AdicPurityScalarNaturality.Field D C,
    ShiftCompatibility (H D C (f ≫ g) (d + e) E) (H D C g e E ⋙ H D C f d E)
      ((family D C (f ≫ g) (d + e) Sc Ic).shift E)
      (composeShift _ _ ((family D C g e Sg Ig).shift E) ((family D C f d Sf If).shift E))
      (u D C f g d e E)) ∧
  (∀ E : AdicPurityScalarNaturality.Field D C,
    ShiftCompatibility (H D C g e E ⋙ H D C f d E) (G D C g Sg E ⋙ G D C f Sf E)
      (composeShift _ _ ((family D C g e Sg Ig).shift E) ((family D C f d Sf If).shift E))
      (composeShift _ _ (gShift D C g Sg E) (gShift D C f Sf E))
      (q D C f g d e Sf Sg If Ig E))

/-- All horizontal clauses of iterated purity scalar pasting, independently
of the canonical twisted-pullback compositor.
Source: smooth purity transport, parent Steps 1, 7 and 8
(blueprint: lem-pur-iterated-purity-scalar-pasting).
Proof: transfer the full rational comparison witness to the unique normalized
family. Paste its purity squares by naturality. Apply the horizontal unit, tower
and shift calculations to its constituent comparisons and purity maps. -/
theorem horizontalPurityScalarPasting :
SingleCoherent D C f d Sf If ∧
  SingleCoherent D C g e Sg Ig ∧
  SingleCoherent D C (f ≫ g) (d + e) Sc Ic ∧
  (∀ (E L : AdicPurityScalarNaturality.Field D C) (h : E ≤ L) (K : RCat D C E Z),
    (T D C E L h X).map ((q D C f g d e Sf Sg If Ig E).hom.app K) ≫
        (beta D C f g Sf Sg E L h).hom.app K =
      (A D C f g d e Sf Sg If Ig E L h).hom.app K ≫
        (q D C f g d e Sf Sg If Ig L).hom.app ((T D C E L h Z).obj K)) ∧
  Coherent D C (fun E ↦ H D C g e E ⋙ H D C f d E)
    (A D C f g d e Sf Sg If Ig)
    (fun E ↦ composeShift _ _ ((family D C g e Sg Ig).shift E)
      ((family D C f d Sf If).shift E)) ∧
  Coherent D C (fun E ↦ G D C g Sg E ⋙ G D C f Sf E)
    (beta D C f g Sf Sg)
    (fun E ↦ composeShift _ _ (gShift D C g Sg E) (gShift D C f Sf E)) ∧
  (∀ E : AdicPurityScalarNaturality.Field D C,
    ShiftCompatibility (H D C g e E ⋙ H D C f d E) (G D C g Sg E ⋙ G D C f Sf E)
      (composeShift _ _ ((family D C g e Sg Ig).shift E) ((family D C f d Sf If).shift E))
      (composeShift _ _ (gShift D C g Sg E) (gShift D C f Sf E))
      (q D C f g d e Sf Sg If Ig E)) := by
  have hf := (single_laws D C f d Sf If).1
  have hg := (single_laws D C g e Sg Ig).1
  have hc := (single_laws D C (f ≫ g) (d + e) Sc Ic).1
  refine ⟨hf, hg, hc, ?_, ?_, ?_, ?_⟩
  · intro E L h K
    unfold q beta A
    exact HorizontalScalarPasting.horizontal_purity
      (H D C g e E) (G D C g Sg E) (H D C f d E) (G D C f Sf E)
      (H D C g e L) (G D C g Sg L) (H D C f d L) (G D C f Sf L)
      (T D C E L h Z) (T D C E L h Y) (T D C E L h X)
      ((family D C g e Sg Ig).gamma E) ((family D C f d Sf If).gamma E)
      ((family D C g e Sg Ig).gamma L) ((family D C f d Sf If).gamma L)
      ((family D C g e Sg Ig).a E L h) (b D C g Sg E L h)
      ((family D C f d Sf If).a E L h) (b D C f Sf E L h)
      ((single_laws D C g e Sg Ig).2 E L h)
      ((single_laws D C f d Sf If).2 E L h) K
  · unfold SingleCoherent Coherent at hf hg
    unfold Coherent
    refine ⟨?_, ?_, ?_⟩
    · intro E
      unfold A
      exact HorizontalScalarPasting.horizontal_unit _ _ _ _ _ _ _ _ _ _
        (hg.1.1 E) (hf.1.1 E)
    · intro E L M h k
      unfold A
      exact HorizontalScalarPasting.horizontal_composition _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _
        (hg.1.2.1 E L M h k) (hf.1.2.1 E L M h k)
    · intro E L h
      let := (family D C g e Sg Ig).shift E
      let := (family D C g e Sg Ig).shift L
      let := (family D C f d Sf If).shift E
      let := (family D C f d Sf If).shift L
      let := tShift D C E L h Z
      let := tShift D C E L h Y
      let := tShift D C E L h X
      let := hg.1.2.2 E L h
      let := hf.1.2.2 E L h
      unfold A ShiftCompatibility composeShift
      exact HorizontalScalarPasting.horizontal_shift _ _ _ _ _ _ _ _ _
  · unfold SingleCoherent Coherent at hf hg
    unfold Coherent
    refine ⟨?_, ?_, ?_⟩
    · intro E
      unfold beta
      exact HorizontalScalarPasting.horizontal_unit _ _ _ _ _ _ _ _ _ _
        (hg.2.1.1 E) (hf.2.1.1 E)
    · intro E L M h k
      unfold beta
      exact HorizontalScalarPasting.horizontal_composition _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _
        (hg.2.1.2.1 E L M h k) (hf.2.1.2.1 E L M h k)
    · intro E L h
      let := gShift D C g Sg E
      let := gShift D C g Sg L
      let := gShift D C f Sf E
      let := gShift D C f Sf L
      let := tShift D C E L h Z
      let := tShift D C E L h Y
      let := tShift D C E L h X
      let := hg.2.1.2.2 E L h
      let := hf.2.1.2.2 E L h
      unfold beta ShiftCompatibility composeShift
      exact HorizontalScalarPasting.horizontal_shift _ _ _ _ _ _ _ _ _
  · intro E
    unfold SingleCoherent at hf hg
    let := (family D C g e Sg Ig).shift E
    let := (family D C f d Sf If).shift E
    let := gShift D C g Sg E
    let := gShift D C f Sf E
    let := hg.2.2.1 E
    let := hf.2.2.1 E
    unfold q ShiftCompatibility composeShift
    exact HorizontalScalarPasting.horizontal_iso_shift _ _ _ _ _ _

/-- Scalar extension commutes with the canonical twisted compositor and with the
horizontal composite of the specified rationalizations of integral purity.
Source: current blueprint, smooth purity transport, composition paragraph;
DAG lem-pur-iterated-purity-scalar-pasting, proof Steps 1--8
(blueprint: lem-pur-iterated-purity-scalar-pasting).
STATEMENT-DISPUTED: the three exceptional systems retain independently chosen
localization shift structures, without a cross-morphism normalization. The canonical
u shift clause therefore needs an identification absent from the stated data.
Proof: identify the normalized families with the rational comparison-identification
witnesses, by their uniqueness. Those witnesses give the single-purity squares,
the adjoint transpose defining b, and the naturality, unit, tower and shift laws.
For u, first use the whole-system pullback-composition scalar square, before taking
its total limit. The tensor-pullback scalar square is the balanced identity sending
b tensor (x tensor y) to (b tensor x) tensor (1 tensor y). Reassociation preserves
this identity. The root-line maps are restrictions of root systems and ordered
power splitting; their scalar squares follow by recursion, with scalar multiplication
at exponent zero. The one-term shifted line models identify this splitting with
product above. All Tate degrees are even: the tensor-shift signs and the block
symmetry sign are one. Thus the tensor, line, pullback and shift factors of the
specified compositor each commute with scalar extension. Paste their squares,
cancelling the internal comparisons, to obtain T(u_E) followed by A equals a_gf
followed by u_L. Conjugating strict-tower scalars by the completion comparison chi
preserves these equations by naturality and cancels the internal chi factors.
For the second square, expand beta and q. Apply the f-purity square at Gg(K), then
naturality of a_f at gamma_g. Move b_g through gamma_f by naturality of gamma_f,
and use the g-purity square inside Hf. Functoriality identifies the result with
A followed by q_L. Each constituent is natural, hence these are equations of
natural transformations. Substitute the unit and tower equations for a_f,a_g
and b_f,b_g into their horizontal composites; naturality moves the middle factors
and the intermediate scalar associators cancel. Finally paste the shift squares;
even Tate degrees give the same sign on both routes, also for an extra input shift.
This proves the two displayed equations and all specified coherence clauses. -/
theorem iteratedPurityScalarPasting : Result D C f g d e Sf Sg Sc If Ig Ic := by
  sorry

end Composite
end WeilConjectures.IteratedPurityScalarPasting
