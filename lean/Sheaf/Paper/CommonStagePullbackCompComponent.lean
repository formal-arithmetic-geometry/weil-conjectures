/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.DerivedPullbackTensorHom

/-! # Common-stage pullback composition component

(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/

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

section
attribute [local irreducible] ScalarLocalization.category

/-- Object representation for the selected common-stage pullback functor.
Source: the defining universal property of common-stage pullback.
Proof: the object clause of `commonStageDerivedPullback_existsUnique`.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative). -/
theorem commonStageDerivedPullback_object_representation
    {V W : Scheme.{u}} (k : V ⟶ W)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    (commonStageDerivedPullback l Ω k).obj M = commonStagePullbackObject l Ω k M :=
  (commonStageDerivedPullback_existsUnique l Ω k).exists.choose_spec.1 M

/-- Map representation for a common-stage pullback on one stage representative.
Source: the defining universal property of common-stage pullback.
Proof: the representative clause of `commonStageDerivedPullback_existsUnique`.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative). -/
theorem commonStageDerivedPullback_map_representation
    {V W : Scheme.{u}} (k : V ⟶ W)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hM : M.stage ≤ L) (hN : N.stage ≤ L)
    (s : M.toStage hM ⟶ N.toStage hN) :
    HEq ((commonStageDerivedPullback l Ω k).map
      (GeneralAlgebraicallyClosedCoefficients.ofHom M N L hM hN s))
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject l Ω k M) (commonStagePullbackObject l Ω k N)
        L hM hN
        ((commonStagePullbackComparison l Ω k M L hM).hom ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k).map s ≫
          (commonStagePullbackComparison l Ω k N L hN).inv)) :=
  (commonStageDerivedPullback_existsUnique l Ω k).exists.choose_spec.2 M N L hM hN s

end

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


/-- The rational pullback compositor at a fixed coefficient stage, obtained by
transporting the selected integral compositor through the canonical pullback objects.
Source: Stacks 099N(5), finite-stage representative convention.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative). -/
def commonStagePullbackRationalComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
    (hM : M.stage ≤ L) :
    (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).obj
        (M.toStage hM) ≅
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).obj
            (M.toStage hM)) :=
  eqToIso ((rationalDerivedPullback_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).exists.choose_spec.2.1
        (M.toStage hM)) ≪≫
    (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).mapIso
      (((integralPullbackComposition l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).choose f g).app
          (M.toStage hM).obj) ≪≫
    (eqToIso ((congrArg
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).exists.choose_spec.2.1
          (M.toStage hM))).trans
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).exists.choose_spec.2.1
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y).obj
              ((constructibleIntegralPullback l
                (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).obj
                (M.toStage hM).obj))))).symm


/-- Naturality of the fixed-stage rational compositor on localized representatives.
Source: Stacks 099N(5), coefficient-compatibility calculation on pure tensors and additivity.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
The proof expands the chosen integral compositor on pure tensors, applies its integral
naturality, and extends by additivity. -/
theorem commonStagePullbackRationalComposition_naturality
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    {K J : generalAlgebraicallyClosedConstructibleCategory l Ω Z}
    (hK : K.stage ≤ L) (hJ : J.stage ≤ L)
    (v : K.toStage hK ⟶ J.toStage hJ) :
    (commonStagePullbackRationalComposition l Ω f g L K hK).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).map v) =
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).map v ≫
        (commonStagePullbackRationalComposition l Ω f g L J hJ).hom := by
  sorry


/-- Cancellation of the inserted comparison isomorphisms in a conjugated square. -/
private theorem stage_square_cancel {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {A B A' B' W W' : D} {U U' V V' : C}
    (x : A ⟶ B) (m : B ⟶ B') (y : A' ≅ B') (ρP : B ⟶ G.obj U) (ρQ : B' ⟶ G.obj U')
    (zP : V ≅ U) (zQ : V' ≅ U') (wP : W ≅ G.obj V) (wQ : W' ≅ G.obj V') (n : U ⟶ U')
    (h : ρP ≫ G.map n = m ≫ ρQ) :
    (x ≫ m ≫ y.inv) ≫ (y.hom ≫ ρQ ≫ G.map zQ.inv ≫ wQ.inv) =
      (x ≫ ρP ≫ G.map zP.inv ≫ wP.inv) ≫
        (wP.hom ≫ G.map (zP.hom ≫ n ≫ zQ.inv) ≫ wQ.inv) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp,
    Iso.map_inv_hom_id_assoc, reassoc_of% h]

/-- The conjugated fixed-stage square underlying common-stage naturality.
Source: Stacks 099N(5), finite-stage cancellation after coefficient compatibility.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
This is the stage-category equality obtained after inserting the three pullback
comparison isomorphisms; the common-stage wrapper is handled by the parent theorem.
Proof: cancel the inner comparison of `f ≫ g` at `Q` and the comparison of `f` at the
pullback of `P`, expand the pullback of the composite map by functoriality, and apply the
fixed-stage rational naturality. -/
theorem commonStagePullbackCompComponent_stage_square
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Z}
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (r : P.toStage hP ⟶ Q.toStage hQ) :
    ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).map r ≫
      (commonStagePullbackComparison l Ω (f ≫ g) Q L hQ).inv) ≫
      ((commonStagePullbackComparison l Ω (f ≫ g) Q L hQ).hom ≫
        (commonStagePullbackRationalComposition l Ω f g L Q hQ).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g Q L hQ).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g Q) L hQ).inv) =
      ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
        (commonStagePullbackRationalComposition l Ω f g L P hP).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g P L hP).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g P) L hP).inv) ≫
      ((commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g P) L hP).hom ≫
        (rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
          ((commonStagePullbackComparison l Ω g P L hP).hom ≫
            (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).map r ≫
            (commonStagePullbackComparison l Ω g Q L hQ).inv) ≫
        (commonStagePullbackComparison l Ω f
          (commonStagePullbackObject l Ω g Q) L hQ).inv) := by
  exact stage_square_cancel _ _ _ _ _ _ _ _ _ _ _
    (commonStagePullbackRationalComposition_naturality l Ω f g L hP hQ r)

/-- The selected common-stage component is represented at every larger coefficient stage.
Source: Stacks 099N(5), coefficient-compatibility argument in residue-compatible pullback.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative).
This is the scalar-extension transport of the chosen integral compositor; it is the
finite-stage calculation used by the naturality proof.
Proof: by the object representation both sides are arrows of the pair category between the
same literal objects. The left side is represented at `P.stage` by the localized integral
compositor at `P.stage`. Enlarging that representative to `L` applies the coefficient
transition `P.stage ≤ L`, conjugated by the recorded stage-transition identifications.
The scalar-extension compatibility of integral pullback (pullback identities and scalar
extension) carries the `P.stage` compositor to the `L` compositor conjugated by the rational
pullback scalar comparisons of `f ≫ g`, `f` and `g`; the compositor is pinned by its finite
reductions, which are jointly faithful, so the two compositors agree. These comparisons,
with the transition identifications, are exactly the three `commonStagePullbackComparison`
factors, and the literal equality transports cancel by proof irrelevance. -/
theorem commonStagePullbackCompComponent_stage_representation
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hP : P.stage ≤ L) :
    HEq (commonStagePullbackCompComponent l Ω f g P).hom
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject l Ω (f ≫ g) P)
        (commonStagePullbackObject l Ω f
          (commonStagePullbackObject l Ω g P)) L hP hP
        ((commonStagePullbackComparison l Ω (f ≫ g) P L hP).hom ≫
          (commonStagePullbackRationalComposition l Ω f g L P hP).hom ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map
            ((commonStagePullbackComparison l Ω g P L hP).inv) ≫
          (commonStagePullbackComparison l Ω f
            (commonStagePullbackObject l Ω g P) L hP).inv)) := by
  sorry

end WeilConjectures
