/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.DerivedPullbackTensorHom

/-! # Naturality of the normalized common-stage compositor

Source: Stacks Tag 099N(5), blueprint composition proof, first paragraph.
(blueprint: lem-zl-common-stage-pullback-comp-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]


/-- The prescribed pullback object on an arbitrary literal common-stage pair.
Source: blueprint common-stage pullback convention
(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/
theorem commonStagePullbackIntegralObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω f).obj P =
      (GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
        ((sfRationalConstructibleLocalization l _ X).obj
          ((constructibleIntegralPullback l _ f).obj P.obj.obj)) := by
  refine ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 P).trans ?_
  change (GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
    ((rationalDerivedPullback l _ f).obj P.obj) = _
  exact congrArg (GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
    ((rationalDerivedPullback_existsUnique l _ f).exists.choose_spec.2.1 P.obj)

/-- The component obtained from the specified integral compositor and object equalities.
Source: Stacks 099N(5), blueprint common-stage composition convention
(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/
def commonStagePullbackCompComponent {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (commonStageDerivedPullback l Ω (f ≫ g)).obj P ≅
      (commonStageDerivedPullback l Ω f).obj ((commonStageDerivedPullback l Ω g).obj P) :=
  eqToIso (commonStagePullbackIntegralObject l Ω (f ≫ g) P) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).mapIso
      ((sfRationalConstructibleLocalization l _ X).mapIso
        (((integralPullbackComposition l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)).choose f g).app
            P.obj.obj)) ≪≫
    (eqToIso ((congrArg (commonStageDerivedPullback l Ω f).obj
      (commonStagePullbackIntegralObject l Ω g P)).trans
        (commonStagePullbackIntegralObject l Ω f
          ((GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
            ((sfRationalConstructibleLocalization l _ Y).obj
              ((constructibleIntegralPullback l _ g).obj P.obj.obj)))))).symm

attribute [local irreducible] commonStagePullbackCompComponent
  commonStageDerivedPullback constructibleIntegralPullback

/-- The component arrow is exactly the localized integral compositor up to object equality.
Source: blueprint normalized composition convention
(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/
theorem commonStagePullbackCompComponent_heq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    HEq (commonStagePullbackCompComponent l Ω f g P).hom
      ((GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).map
        ((sfRationalConstructibleLocalization l _ X).map
          (((integralPullbackComposition l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)).choose f g).hom.app
              P.obj.obj))) := by
  unfold commonStagePullbackCompComponent
  apply (conj_eqToHom_iff_heq _ _ (commonStagePullbackIntegralObject l Ω (f ≫ g) P)
    ((congrArg (commonStageDerivedPullback l Ω f).obj
      (commonStagePullbackIntegralObject l Ω g P)).trans
        (commonStagePullbackIntegralObject l Ω f
          ((GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
            ((sfRationalConstructibleLocalization l _ Y).obj
              ((constructibleIntegralPullback l _ g).obj P.obj.obj)))))).1
  simp only [Iso.trans_hom, eqToIso.hom]
  rfl

/-- Naturality for one explicit common-stage representative.
The representative formula is expanded at a common coefficient stage.  One first
uses the scalar-extension tower coherence to transport the integral compositor to
that stage, then applies the naturality square of the integral pullback compositor
and cancels the comparison isomorphisms.  The proof is the finite-stage core of
`commonStagePullbackCompComponent_naturality`.
Source: Stacks 099N(5), coefficient-compatibility argument in residue-compatible
pullback, Step 10.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative). -/
theorem commonStagePullbackCompComponent_naturality_ofHom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Z}
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (r : P.toStage hP ⟶ Q.toStage hQ) :
    (commonStageDerivedPullback l Ω (f ≫ g)).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ r) ≫
        (commonStagePullbackCompComponent l Ω f g Q).hom =
      (commonStagePullbackCompComponent l Ω f g P).hom ≫
        (commonStageDerivedPullback l Ω f).map
          ((commonStageDerivedPullback l Ω g).map
            (GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ r)) := by
  sorry

/-- The normalized integral components descend naturally to common-stage morphisms.
Source: Stacks 099N(5); blueprint composition proof, first paragraph, and the
coefficient-compatibility argument in residue-compatible pullback, Step 10
(blueprint: lem-zl-common-stage-pullback-comp-naturality).
Proof: represent the arrow at a common coefficient stage L. The recorded pullback
map formula conjugates its rational pullback by the normalized scalar comparisons.
The integral scalar/composition square reduces at each finite coefficient quotient
to tensor reassociation and multiplication; fully faithful normalized reduction
reflects that square. Rationalize it on pure tensors. Additivity extends naturality
from pure tensors to every rational morphism. Use the scalar square to move both
component comparisons to L, cancel their invertible boundary comparisons, and apply
rational naturality there. The two recorded object-equality transports cancel by
proof irrelevance. Identity stages keep their normalized transition comparisons;
empty schemes and arbitrary semilinear scheme morphisms need no extra hypothesis. -/
theorem commonStagePullbackCompComponent_naturality {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Z} (a : P ⟶ Q) :
    (commonStageDerivedPullback l Ω (f ≫ g)).map a ≫
        (commonStagePullbackCompComponent l Ω f g Q).hom =
      (commonStagePullbackCompComponent l Ω f g P).hom ≫
        (commonStageDerivedPullback l Ω f).map ((commonStageDerivedPullback l Ω g).map a) := by
  induction a using StageSystem.PairCategory.hom_induction with
  | h L hP hQ r =>
    exact commonStagePullbackCompComponent_naturality_ofHom l Ω f g L hP hQ r


end WeilConjectures
