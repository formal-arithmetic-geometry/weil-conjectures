module

public import Sheaf.Paper.RationalTwistedPullbackCompositor
public import Sheaf.Paper.RationalScalarComparisonData
public import Sheaf.Paper.AdicPurityScalarNaturality

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

section Single
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

/-- A bundling of the existing normalized rational comparison data. The localization
is fixed on all good representatives; gamma is literally the localization of I.gamma;
a is fixed componentwise to the canonical sourceScalar. This adds no new choices of
purity, scalar maps or source coordinates to the recorded comparison-identification node.
Source: purity transport, rationalization of the simultaneous integral family
(blueprint: lem-pur-iterated-purity-scalar-pasting). -/
structure Family where
  shift : ∀ E : AdicPurityScalarNaturality.Field D C, (H D C f d E).CommShift ℤ
  localization : ∀ E : AdicPurityScalarNaturality.Field D C,
    source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E
  localization_normalization : ∀ E : AdicPurityScalarNaturality.Field D C,
    SourceLocalizationNormalization D C f d E (localization E)
  localization_shift : ∀ E : AdicPurityScalarNaturality.Field D C,
    ShiftCompatibility (source D C f d E ⋙ Q D C E X) (Q D C E Y ⋙ H D C f d E)
      (composeShift _ _ (sourceShift D C f d E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (shift E)) (localization E)
  gamma : ∀ E : AdicPurityScalarNaturality.Field D C, H D C f d E ≅ G D C f S E
  gamma_localization : ∀ (E : AdicPurityScalarNaturality.Field D C) (K : Cat D C E Y),
    (localization E).hom.app K ≫ (gamma E).hom.app ((Q D C E Y).obj K) =
      (Q D C E X).map ((I.gamma E).hom.app K) ≫
        (gLocalization D C f S E).hom.app K
  a : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
    H D C f d E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ H D C f d F
  a_normalization : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
    (K : RCat D C E Y), HEq ((a E F h).app K)
      (RationalSmoothPurityCanonical.sourceScalar C.l E.val F.val
        (IntermediateField.inclusion h) f d K)

/-- The normalized rational family is uniquely determined by the integral family.
Source: purity transport, rationalization and normalized source identifications
(blueprint: lem-pur-iterated-purity-scalar-pasting).
Proof: take shift, localization, eta and a from the recorded
rationalScalarComparisonIdentification. Its normalization, shift and eta equations
are exactly the fields above. Every good resolution of an integral pullback has
the prescribed source comparison. Resolving localization is essentially surjective
and natural transformations out of it are determined on good representatives,
so the localization is unique. The displayed gamma equation then determines gamma
on every rational object, since each has an integral representative and the source
localization is invertible. The a normalization fixes every component, so it fixes
a as a natural isomorphism. Finally the localization shift equation determines the
source shift on all rational objects, since the integral shifts and localization
shifts are fixed. Structure extensionality and proof irrelevance give uniqueness. -/
theorem family_existsUnique : ∃! V : Family D C f d S I, True := by
  sorry

/-- The unique normalized family, rather than an arbitrary endpoint isomorphism.
Source: purity transport, gamma and a
(blueprint: lem-pur-iterated-purity-scalar-pasting). -/
@[irreducible] def family : Family D C f d S I := (family_existsUnique D C f d S I).exists.choose

end Single

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

/-- Scalar extension commutes with the canonical twisted compositor and with the
horizontal composite of the specified rationalizations of integral purity.
Source: current blueprint, smooth purity transport, composition paragraph;
DAG lem-pur-iterated-purity-scalar-pasting, proof Steps 1--8
(blueprint: lem-pur-iterated-purity-scalar-pasting).
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
