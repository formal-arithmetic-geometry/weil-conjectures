/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.PodHomChainCounitFormula
public import Sheaf.Paper.PodCtfPairingMaps
public import Sheaf.Paper.ExceptionalAdjointAdmissibility
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Normalized coefficient comparisons and canonical Gamma representatives

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction.proof.md, coefficient-comparison and field-stage paragraphs
(blueprint: def-sf-coefficient-gamma-representatives).

The chain is the published `PodHomChain.homEquiv`. Its fourth arrow is
precomposition with the forward, compactification-normalized projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v a b
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite TensorProduct
open CategoryTheory.SuppliedExchangeProjection
namespace WeilConjectures.TensorHomCoefficientTransposes

attribute [local instance 2000] Algebra.toModule

attribute [local irreducible] PodHomChain.homEquiv PodHomChain.projectionIso
  PodCtfAdjunctionData.ordinaryAdjunction PodCtfAdjunctionData.exceptionalAdjunction
  PodCtfAdjunctionData.tensorAdjunctionX PodCtfAdjunctionData.tensorAdjunctionY
  PodCoefficientStage.operations

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
  [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}

/-- A supplied full domain for the five bijections, using exactly the recorded operations.
Source: the full-domain hypothesis (blueprint: def-sf-coefficient-gamma-representatives). -/
abbrev Domain (S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  PodCtfAdjunctionData (PodCoefficientStage.operations S s)
    (PodCoefficientStage.domain S s) (PodCoefficientStage.homPairs (S := S) s)
    (PodCoefficientStage.internalHom (S := S) s) (PodCoefficientStage.tensor S s) f c

/-- The tensor functor in the chosen, normalized left-factor closed presentation.
Source: the second and fifth arrows
(blueprint: def-sf-coefficient-gamma-representatives). -/
abbrev tensorLeft {A : Type a} [Category.{b} A]
    (m : MonoidalCategory A) (K : A) := @MonoidalCategory.tensorLeft A _ m K

/-- Optional ambient admissibility, exactly as the dependency states it, at the
selected coefficient stage. All base maps are the canonical over-category maps.
Source: initial hypothesis (blueprint: def-sf-coefficient-gamma-representatives). -/
def Admissible (_S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    Prop :=
  ∃ hS : ∀ z : Spec (.of D.k), IsUnit (C.l : (Spec (.of D.k)).presheaf.stalk z),
    match s with
    | .finite => IsExceptionalAdjointAdmissibleAtFiniteStage C.l E n hn
        (Spec (.of D.k)) X.obj.left Y.obj.left hS f.hom.left c
    | .integral => IsExceptionalAdjointAdmissibleAtIntegral C.l E
        (Spec (.of D.k)) X.obj.left Y.obj.left hS f.hom.left c
    | .rational => IsExceptionalAdjointAdmissibleAtRational C.l E
        (Spec (.of D.k)) X.obj.left Y.obj.left hS f.hom.left c
    | .common => IsExceptionalAdjointAdmissibleAtAlgebraicallyClosed C.l C.Qbar
        (Spec (.of D.k)) X.obj.left Y.obj.left hS f.hom.left c

/-- Index only the finite and integral clauses for coefficient changes.
Source: the first paragraph (blueprint: def-sf-coefficient-gamma-representatives). -/
def ringStage (i : Bool) : PodCoefficientStage := if i then .integral else .finite

/-- The actual finite or completed coefficient sheaves of this stage.
Source: the coefficient list (blueprint: def-sf-coefficient-gamma-representatives). -/
def coefficients (_S : SixFunctorOperationDatum D C E n hn) (i : Bool) :
    PurCompactSupport.Coefficients.{u} :=
  if i then PurCompactSupport.completed C.l E else PurCompactSupport.finite C.l E n hn

/-- The canonical full inclusion into the corresponding ringed derived category.
Source: full-domain clause (blueprint: def-sf-coefficient-gamma-representatives). -/
def inclusion (S : SixFunctorOperationDatum D C E n hn) (i : Bool)
    (W : SixFunctorSpace D) : (PodCoefficientStage.domain S (ringStage i) W).FullSubcategory ⥤
      DerivedCategory (pbcModules W.obj.left ((coefficients S i).ring W.obj.left)) := by
  cases i
  · exact (PodCoefficientStage.domain S .finite W).ι ⋙
      (AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible
        C.l E n hn W.obj.left).ι
  · exact (PodCoefficientStage.domain S .integral W).ι ⋙
      (sfIntegralConstructible C.l E W.obj.left).ι

/-- Exactly the three requested kinds of ring change, specified on actual ring-sheaf
maps. The quotient and integral-reduction clauses require the same coefficient field.
The completed extension is along the displayed finite coefficient-field embedding.
Source: the three changes T (blueprint: def-sf-coefficient-gamma-representatives). -/
def Permitted (S : SixFunctorOperationDatum D C E n hn) (i : Bool)
    (S' : SixFunctorOperationDatum D C E' n' hn') (j : Bool)
    (a : PurCompactSupport.Change (coefficients S i) (coefficients S' j)) : Prop :=
  (i = false ∧ j = false ∧ ∃ h : n' ≤ n,
    HEq E E' ∧ ∀ W : Scheme.{u},
      HEq (a.map W) ((PurCompactSupport.finiteQuotientChange C.l E n n' hn hn' h).map W)) ∨
  (i = true ∧ j = false ∧ HEq E E' ∧ ∀ W : Scheme.{u},
    HEq (a.map W) ((PurCompactSupport.reduction C.l E n' hn').map W)) ∨
  (i = true ∧ j = true ∧ ∃ e : E →ₐ[Padic C.l] E', ∀ W : Scheme.{u},
    HEq (a.map W) ((PurCompactSupport.completedChange C.l E E' e).map W))

/-- A tensor-Hom coefficient comparison need not be invertible. Its right-hand
map is the evaluation transpose, fixed by its counit equation; only the tensor
comparison is an isomorphism. This includes non-site-perfect finite-Tor inputs.
Source: proof step 1 and the no-perfectness clause
(blueprint: def-sf-coefficient-gamma-representatives). -/
structure TensorComparison
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{v} B]
    {F H : A ⥤ A} {F' H' : B ⥤ B} (adj : F ⊣ H) (adj' : F' ⊣ H')
    (T : A ⥤ B) where
  left : F ⋙ T ≅ T ⋙ F'
  right : H ⋙ T ⟶ T ⋙ H'
  counit (Q : A) :
    F'.map (right.app Q) ≫ adj'.counit.app (T.obj Q) =
      left.inv.app (H.obj Q) ≫ T.map (adj.counit.app Q)

section Comparison
variable (S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
  (S' : SixFunctorOperationDatum D C E' n' hn') (t : PodCoefficientStage)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : Domain S s f c) (R' : Domain S' t f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]

/-- The specified operation comparisons, on the supplied full domains. Tensor-Hom
comparisons retain their evaluation/counit normalization, and projection compatibility
is for the actual forward PF. Thus none of the five intermediate bijections is replaced
by an arbitrary equivalence. This interface applies to each of the three coefficient
changes in the statement, with its prescribed coefficient functors.
Source: coefficient-comparison paragraph and proof steps 1--5
(blueprint: def-sf-coefficient-gamma-representatives). -/
structure Comparison
    (TX : (PodCoefficientStage.domain S s X).FullSubcategory ⥤
      (PodCoefficientStage.domain S' t X).FullSubcategory)
    (TY : (PodCoefficientStage.domain S s Y).FullSubcategory ⥤
      (PodCoefficientStage.domain S' t Y).FullSubcategory) where
  ordinary : ExchangeProjectionAdjunctionComparison R.ordinaryAdjunction
    R'.ordinaryAdjunction TY TX
  exceptional : ExchangeProjectionAdjunctionComparison R.exceptionalAdjunction
    R'.exceptionalAdjunction TX TY
  tensorX (M : (PodCoefficientStage.domain S s X).FullSubcategory) :
    TensorComparison (R.tensorAdjunctionX M)
      (R'.tensorAdjunctionX (TX.obj M)) TX
  tensorYBase (K : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    TensorComparison (R.tensorAdjunctionY K)
      (R'.tensorAdjunctionY (TY.obj K)) TY
  tensorY (M : (PodCoefficientStage.domain S s X).FullSubcategory) :
    TensorComparison (R.tensorAdjunctionY (R.support.obj M))
      (R'.tensorAdjunctionY (R'.support.obj (TX.obj M))) TY
  tensorY_normalization (M : (PodCoefficientStage.domain S s X).FullSubcategory)
      (L : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (tensorY M).left.hom.app L =
      (tensorYBase (R.support.obj M)).left.hom.app L ≫
        (@MonoidalCategory.whiskerRight _ _ R'.closedY.closed.monoidal.toMonoidalCategoryStruct
          _ _ (exceptional.left.hom.app M) (TY.obj L))
  projection (M : (PodCoefficientStage.domain S s X).FullSubcategory)
      (L : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    TY.map (PodCtfPairing.projection S s f c R M L) ≫
        exceptional.left.hom.app ((tensorLeft R.closedX.closed.monoidal M).obj
          (R.pull.obj L)) ≫
        R'.support.map ((tensorX M).left.hom.app (R.pull.obj L) ≫
          (tensorLeft R'.closedX.closed.monoidal (TX.obj M)).map
            (ordinary.left.hom.app L)) =
      (tensorY M).left.hom.app L ≫
        PodCtfPairing.projection S' t f c R' (TX.obj M) (TY.obj L)

variable {S s S' t f c R R'}
  {TX : (PodCoefficientStage.domain S s X).FullSubcategory ⥤
    (PodCoefficientStage.domain S' t X).FullSubcategory}
  {TY : (PodCoefficientStage.domain S s Y).FullSubcategory ⥤
    (PodCoefficientStage.domain S' t Y).FullSubcategory}

/-- The endpoint comparison alpha_A is ordinary direct image, internal-Hom evaluation
transpose, then exceptional comparison in the second Hom variable.
Source: alpha_A and proof steps 2--4
(blueprint: def-sf-coefficient-gamma-representatives). -/
def Comparison.source (d : Comparison S s S' t f c R R' TX TY)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    TY.obj ((PodHomChain.sourceFunctor S s f c R M).obj N) ⟶
      (PodHomChain.sourceFunctor S' t f c R' (TX.obj M)).obj (TY.obj N) :=
  d.ordinary.right.hom.app ((PodCtfPairing.homX S s f c R M).obj (R.exceptional.obj N)) ≫
    R'.direct.map ((d.tensorX M).right.app (R.exceptional.obj N)) ≫
    R'.direct.map ((PodCtfPairing.homX S' t f c R' (TX.obj M)).map
      (d.exceptional.right.hom.app N))

/-- The endpoint comparison alpha_B is the normalized target tensor-Hom comparison;
its left tensor comparison already includes the compact-support input comparison.
Source: alpha_B and proof step 5
(blueprint: def-sf-coefficient-gamma-representatives). -/
def Comparison.target (d : Comparison S s S' t f c R R' TX TY)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    TY.obj ((PodHomChain.targetFunctor S s f c R M).obj N) ⟶
      (PodHomChain.targetFunctor S' t f c R' (TX.obj M)).obj (TY.obj N) :=
  (d.tensorY M).right.app N

/-- The coefficient square is equality of actual arrows, for every test arrow.
There is no perfectness or dualizability assumption on M or its compact-support image.
Source: the displayed Gamma square (blueprint: def-sf-coefficient-gamma-representatives). -/
def Square (d : Comparison S s S' t f c R R' TX TY) : Prop :=
  ∀ (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N L : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (z : L ⟶ (PodHomChain.sourceFunctor S s f c R M).obj N),
    TY.map (PodHomChain.homEquiv S s f c R M N L z) ≫ d.target M N =
      PodHomChain.homEquiv S' t f c R' (TX.obj M) (TY.obj N) (TY.obj L)
        (TY.map z ≫ d.source M N)

end Comparison

attribute [local irreducible] PodHomChain.sourceFunctor PodHomChain.targetFunctor
  PodHomChain.homX PodHomChain.homY

private theorem homEquiv_representative_laws
    {A : Type a} [Category.{v} A] {P Q : A}
    (e : ∀ T : A, (T ⟶ P) ≃ (T ⟶ Q))
    (hnat : ∀ (T T' : A) (a : T' ⟶ T) (t : T ⟶ P),
      e T' (a ≫ t) = a ≫ e T t) :
    e P (𝟙 P) ≫ (e Q).symm (𝟙 Q) = 𝟙 P ∧
      (e Q).symm (𝟙 Q) ≫ e P (𝟙 P) = 𝟙 Q := by
  constructor
  · apply (e P).injective
    calc
      e P (e P (𝟙 P) ≫ (e Q).symm (𝟙 Q)) =
          e P (𝟙 P) ≫ e Q ((e Q).symm (𝟙 Q)) := hnat _ _ _ _
      _ = e P (𝟙 P) := by rw [Equiv.apply_symm_apply, Category.comp_id]
  · simpa only [Category.comp_id, Equiv.apply_symm_apply] using
      (hnat P Q ((e Q).symm (𝟙 Q)) (𝟙 P)).symm

section Localization
variable (S : SixFunctorOperationDatum D C E n hn)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (R : Domain S .integral f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]

/-- The integral chain, in the ambient integral Hom groups via full inclusion.
Source: raw rationalization paragraph
(blueprint: def-sf-coefficient-gamma-representatives). -/
def integralHomEquiv
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N L : (PodCoefficientStage.domain S .integral Y).FullSubcategory) :
    (L.obj ⟶ ((PodHomChain.sourceFunctor S .integral f c R M).obj N).obj) ≃
      (L.obj ⟶ ((PodHomChain.targetFunctor S .integral f c R M).obj N).obj) :=
  ((PodCoefficientStage.domain S .integral Y).fullyFaithfulι.homEquiv).symm.trans
    ((PodHomChain.homEquiv S .integral f c R M N L).trans
      (PodCoefficientStage.domain S .integral Y).fullyFaithfulι.homEquiv)

/-- The two canonical Yoneda representatives of the specified chain are inverse.
Source: inverse-pair passage (blueprint: def-sf-coefficient-gamma-representatives).
Proof: naturality in the test object identifies Gamma(z) with z;Gamma(1_A).
Apply the same argument to the inverse chain. The two inverse-bijection equations
at identity arrows then give the two displayed inverse equations. This uses the
five specified bijections, not an arbitrary chosen equivalence of endpoints. -/
theorem integral_representative_laws
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory) :
    (PodHomChain.homEquiv S .integral f c R M N _ (𝟙 _)) ≫
        (PodHomChain.homEquiv S .integral f c R M N _).symm (𝟙 _) = 𝟙 _ ∧
    (PodHomChain.homEquiv S .integral f c R M N _).symm (𝟙 _) ≫
        (PodHomChain.homEquiv S .integral f c R M N _ (𝟙 _)) = 𝟙 _ := by
  exact homEquiv_representative_laws
    (PodHomChain.homEquiv S .integral f c R M N)
    ((PodHomChain.counit_formula S .integral f c R M).2.1 N)

/-- The representing isomorphism has the actual Gamma(1_A) as its forward map and
Gamma^{-1}(1_B) as its inverse. Only their inverse proofs are postponed.
Source: representing inverse maps (blueprint: def-sf-coefficient-gamma-representatives). -/
def integralGammaIso
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory) :
    (PodHomChain.sourceFunctor S .integral f c R M).obj N ≅
      (PodHomChain.targetFunctor S .integral f c R M).obj N where
  hom := PodHomChain.homEquiv S .integral f c R M N _ (𝟙 _)
  inv := (PodHomChain.homEquiv S .integral f c R M N _).symm (𝟙 _)
  hom_inv_id := (integral_representative_laws S f c R M N).1
  inv_hom_id := (integral_representative_laws S f c R M N).2

attribute [local irreducible] integralGammaIso

/-- Raw localization of the fixed full-domain inclusion. No idempotent completion.
Source: raw rationalization paragraph
(blueprint: def-sf-coefficient-gamma-representatives). -/
def rationalization (W : SixFunctorSpace D) :
    (PodCoefficientStage.domain S .integral W).FullSubcategory ⥤
      sfRationalConstructibleCategory C.l E W.obj.left :=
  (PodCoefficientStage.domain S .integral W).ι ⋙
    sfRationalConstructibleLocalization C.l E W.obj.left


/-- The rational representative is the image of Gamma(1_A), with its fixed inverse.
Source: localized inverse pair (blueprint: def-sf-coefficient-gamma-representatives). -/
def rationalGammaIso
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory) :
    (rationalization S Y).obj ((PodHomChain.sourceFunctor S .integral f c R M).obj N) ≅
      (rationalization S Y).obj ((PodHomChain.targetFunctor S .integral f c R M).obj N) :=
  (rationalization S Y).mapIso (integralGammaIso S f c R M N)

attribute [local irreducible] rationalGammaIso rationalization

/-- The rational Gamma on every fractional test arrow, using the localized canonical
representative. Its pure-tensor formula below identifies it with localized Gamma.
Source: rational Hom bijections (blueprint: def-sf-coefficient-gamma-representatives). -/
def rationalGamma
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory)
    (L : sfRationalConstructibleCategory C.l E Y.obj.left) :
    (L ⟶ (rationalization S Y).obj ((PodHomChain.sourceFunctor S .integral f c R M).obj N)) ≃
      (L ⟶ (rationalization S Y).obj ((PodHomChain.targetFunctor S .integral f c R M).obj N)) :=
  Iso.homCongr (Iso.refl L) (rationalGammaIso S f c R M N)

end Localization
section CommonStages
open GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (W : Scheme.{u})

/-- A common field for the three endpoints of the Hom bijection. This uses the
recorded finite coefficient fields, with their original inclusions and composita.
Source: common finite field paragraph
(blueprint: def-sf-coefficient-gamma-representatives). -/
abbrev CommonTriple (L A B : Pair l Ω W) :=
  {F : AlgebraicallyClosedCoefficients.Index l Ω //
    L.stage ≤ F ∧ A.stage ≤ F ∧ B.stage ≤ F}

/-- The source Hom group at one common coefficient field, with its actual transitions.
Source: common-stage representative formula
(blueprint: def-sf-coefficient-gamma-representatives). -/
abbrev SourceHom {L A B : Pair l Ω W} (F : CommonTriple l Ω W L A B) :=
  StageHom L A ⟨F.val, F.property.1, F.property.2.1⟩

/-- The target Hom group at the same common coefficient field.
Source: common-stage representative formula
(blueprint: def-sf-coefficient-gamma-representatives). -/
abbrev TargetHom {L A B : Pair l Ω W} (F : CommonTriple l Ω W L A B) :=
  StageHom L B ⟨F.val, F.property.1, F.property.2.2⟩

end CommonStages

section CommonChain
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (F : Index C.l C.Qbar)
  (SF : SixFunctorOperationDatum D C (Coefficient.{u} C.l C.Qbar F) n hn)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (RF : Domain SF .integral f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
  (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory)

/-- The common source is the localization and inclusion of the actual integral A.
Source: node step 8 (blueprint: def-sf-coefficient-gamma-representatives). -/
def commonSource : Pair C.l C.Qbar Y.obj.left :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion F).obj
    ((rationalization SF Y).obj ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N))

/-- The common target is the localization and inclusion of the actual integral B.
Source: node step 8 (blueprint: def-sf-coefficient-gamma-representatives). -/
def commonTarget : Pair C.l C.Qbar Y.obj.left :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion F).obj
    ((rationalization SF Y).obj ((PodHomChain.targetFunctor SF .integral f c RF M).obj N))


/-- The common-stage representative is the inclusion of localized Gamma(1_A).
Source: node step 8 (blueprint: def-sf-coefficient-gamma-representatives). -/
def commonGammaIso : commonSource F SF f c RF M N ≅ commonTarget F SF f c RF M N :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion F).mapIso
    (rationalGammaIso SF f c RF M N)

attribute [local irreducible] commonGammaIso

/-- The actual common Gamma acts by its canonical localized representative.
Source: common-stage bijections (blueprint: def-sf-coefficient-gamma-representatives). -/
def commonGamma (L : Pair C.l C.Qbar Y.obj.left) :
    (L ⟶ commonSource F SF f c RF M N) ≃ (L ⟶ commonTarget F SF f c RF M N) :=
  Iso.homCongr (Iso.refl L) (commonGammaIso F SF f c RF M N)

/-- Extend the SAME localized Gamma representative by the specified scalar transition.
Source: representative formula, step 8
(blueprint: def-sf-coefficient-gamma-representatives). -/
def stageGamma (L : Pair C.l C.Qbar Y.obj.left)
    (G : CommonTriple C.l C.Qbar Y.obj.left L
      (commonSource F SF f c RF M N) (commonTarget F SF f c RF M N))
    (z : SourceHom C.l C.Qbar Y.obj.left G) : TargetHom C.l C.Qbar Y.obj.left G :=
  z ≫ (stageTransition C.l C.Qbar Y.obj.left F G.val G.property.2.1).map
    (rationalGammaIso SF f c RF M N).hom

/-- The raw common-field localization, for transporting integral structural equations.
Source: steps 7--8 (blueprint: def-sf-coefficient-gamma-representatives). -/
def commonLocalization (_SF : SixFunctorOperationDatum D C
    (Coefficient.{u} C.l C.Qbar F) n hn) (W : SixFunctorSpace D) :
    sfIntegralConstructibleCategory C.l (Coefficient.{u} C.l C.Qbar F) W.obj.left ⥤
      Pair C.l C.Qbar W.obj.left :=
  sfRationalConstructibleLocalization C.l (Coefficient.{u} C.l C.Qbar F) W.obj.left ⋙
    (GeneralAlgebraicallyClosedCoefficients.inclusion F :
      Stage C.l C.Qbar W.obj.left F ⥤ _)

/-- The shifted integral canonical Gamma representative, retaining its integer shift.
Source: signed-shift passage (blueprint: def-sf-coefficient-gamma-representatives). -/
def shiftedIntegralGamma (r : ℤ) :
    (shiftFunctor (sfIntegralConstructibleCategory C.l
      (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).obj
        ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N).obj ⟶
    (shiftFunctor (sfIntegralConstructibleCategory C.l
      (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).obj
        ((PodHomChain.targetFunctor SF .integral f c RF M).obj N).obj :=
  (shiftFunctor (sfIntegralConstructibleCategory C.l
    (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).map
      (integralGammaIso SF f c RF M N).hom.hom

/-- An integral signed-shift equation for the actual Gamma representatives remains
that equation for rational and common Gamma, with the same sign and structural maps.
Source: final sentence, steps 7--8
(blueprint: def-sf-coefficient-gamma-representatives).
Proof: the rational and common representatives are the images of integralGammaIso.
Apply the two additive localization/inclusion functors to the integral equation;
functoriality gives the displayed composites. Their normalized shift comparisons
identify the image of shiftedIntegralGamma with the shifted rational/common map.
Every equation involves finitely many arrows, so common-stage independence follows
from the representative criterion. No reduction-faithfulness is asserted. -/
def ShiftEquationsPassToFields
    (M' : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N' : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) (r k : ℤ)
    (a : ((PodHomChain.sourceFunctor SF .integral f c RF M').obj N').obj ⟶
      (shiftFunctor (sfIntegralConstructibleCategory C.l
        (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).obj
          ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N).obj)
    (b : ((PodHomChain.targetFunctor SF .integral f c RF M').obj N').obj ⟶
      (shiftFunctor (sfIntegralConstructibleCategory C.l
        (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).obj
          ((PodHomChain.targetFunctor SF .integral f c RF M).obj N).obj)
    (_h : (integralGammaIso SF f c RF M' N').hom.hom ≫ b =
      a ≫ (k • shiftedIntegralGamma F SF f c RF M N r)) : Prop :=
    (rationalGammaIso SF f c RF M' N').hom ≫
        (sfRationalConstructibleLocalization C.l
          (Coefficient.{u} C.l C.Qbar F) Y.obj.left).map b =
      (sfRationalConstructibleLocalization C.l
        (Coefficient.{u} C.l C.Qbar F) Y.obj.left).map
          (a ≫ (k • shiftedIntegralGamma F SF f c RF M N r)) ∧
    (commonGammaIso F SF f c RF M' N').hom ≫ (commonLocalization F SF Y).map b =
      (commonLocalization F SF Y).map
        (a ≫ (k • shiftedIntegralGamma F SF f c RF M N r))

end CommonChain

attribute [local irreducible] Comparison.source Comparison.target
  rationalGamma commonGamma

section FieldCoefficientSquare
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (F G : Index C.l C.Qbar) (hFG : F ≤ G)
  (SF : SixFunctorOperationDatum D C (Coefficient.{u} C.l C.Qbar F) n hn)
  (SG : SixFunctorOperationDatum D C (Coefficient.{u} C.l C.Qbar G) n hn)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  (RF : Domain SF .integral f c) (RG : Domain SG .integral f c)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (TX : (PodCoefficientStage.domain SF .integral X).FullSubcategory ⥤
    (PodCoefficientStage.domain SG .integral X).FullSubcategory)
  (TY : (PodCoefficientStage.domain SF .integral Y).FullSubcategory ⥤
    (PodCoefficientStage.domain SG .integral Y).FullSubcategory)
  (d : Comparison SF .integral SG .integral f c RF RG TX TY)
  (rY : TY ⋙ rationalization SG Y ≅ rationalization SF Y ⋙
    stageTransition C.l C.Qbar Y.obj.left F G hFG)

/-- The rational alpha_A is the localized integral endpoint comparison in the
specified scalar-transition coordinates rY. Source: step 7
(blueprint: def-sf-coefficient-gamma-representatives). -/
def rationalSourceComparison
    (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) :
    (stageTransition C.l C.Qbar Y.obj.left F G hFG).obj
      ((rationalization SF Y).obj ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N)) ⟶
    (rationalization SG Y).obj
      ((PodHomChain.sourceFunctor SG .integral f c RG (TX.obj M)).obj (TY.obj N)) :=
  rY.inv.app ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N) ≫
    (rationalization SG Y).map (d.source M N)

/-- The rational alpha_B is the localized integral target comparison.
Source: step 7 (blueprint: def-sf-coefficient-gamma-representatives). -/
def rationalTargetComparison
    (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) :
    (stageTransition C.l C.Qbar Y.obj.left F G hFG).obj
      ((rationalization SF Y).obj ((PodHomChain.targetFunctor SF .integral f c RF M).obj N)) ⟶
    (rationalization SG Y).obj
      ((PodHomChain.targetFunctor SG .integral f c RG (TX.obj M)).obj (TY.obj N)) :=
  rY.inv.app ((PodHomChain.targetFunctor SF .integral f c RF M).obj N) ≫
    (rationalization SG Y).map (d.target M N)


attribute [local irreducible] rationalSourceComparison rationalTargetComparison

/-- The actual rational Gamma coefficient square holds for every fractional arrow;
the actual common Gamma coefficient square holds for every common-stage arrow.
The common endpoint identifications are the normalized transIso for F≤G.
Source: final coefficient/field clauses, steps 7--8
(blueprint: def-sf-coefficient-gamma-representatives).
Proof: localize coefficient_square on integral representatives. The normalization rY
identifies both endpoint maps with the displayed rational comparisons. The pure-tensor
formula rationalGamma_formula and semilinearity extend the equality to all fractional
arrows. Include at G and use naturality of transIso. Represent any common arrow over
a larger common field; the same rational equation there and the representative
criterion prove the second square. This proves compatibility with recalculating the
actual changed chain at G, not merely with transporting a fixed representative. -/
def FieldCoefficientSquare
    (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) : Prop :=
    (∀ (L : Stage C.l C.Qbar Y.obj.left F)
      (z : L ⟶ (rationalization SF Y).obj
        ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N)),
      (stageTransition C.l C.Qbar Y.obj.left F G hFG).map
          (rationalGamma SF f c RF M N L z) ≫
          rationalTargetComparison F G hFG SF SG f c RF RG TX TY d rY M N =
      rationalGamma SG f c RG (TX.obj M) (TY.obj N)
        ((stageTransition C.l C.Qbar Y.obj.left F G hFG).obj L)
        ((stageTransition C.l C.Qbar Y.obj.left F G hFG).map z ≫
          rationalSourceComparison F G hFG SF SG f c RF RG TX TY d rY M N)) ∧
    ∀ (L : Pair C.l C.Qbar Y.obj.left)
      (z : L ⟶ commonSource F SF f c RF M N),
      commonGamma F SF f c RF M N L z ≫
        ((stageSystem C.l C.Qbar Y.obj.left).transIso hFG).inv.app
          ((rationalization SF Y).obj
            ((PodHomChain.targetFunctor SF .integral f c RF M).obj N)) ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion G).map
          (rationalTargetComparison F G hFG SF SG f c RF RG TX TY d rY M N) =
      commonGamma G SG f c RG (TX.obj M) (TY.obj N) L
        (z ≫ ((stageSystem C.l C.Qbar Y.obj.left).transIso hFG).inv.app
          ((rationalization SF Y).obj
            ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N)) ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion G).map
            (rationalSourceComparison F G hFG SF SG f c RF RG TX TY d rY M N))
end FieldCoefficientSquare
end WeilConjectures.TensorHomCoefficientTransposes
