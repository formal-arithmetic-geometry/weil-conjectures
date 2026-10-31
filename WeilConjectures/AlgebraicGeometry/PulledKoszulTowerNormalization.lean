/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralCompletedTowerPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.PrincipalKoszulStrictReplacement

/-! # Canonical generators and normalization for pulled principal Koszul towers

Source: Stacks Project, sites-modules.tex, Tags 03D2, 03EK and 03EL;
sites-cohomology.tex, Tag 07A4; algebraization.tex, Tag 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization).

The index n denotes exponent n+1. These constructions require neither a good
complex nor invertibility of ell on the schemes. They depend only on the recorded
ordinary completed pullback, total tensor generators and principal Koszul tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent

namespace WeilConjectures.PulledKoszulTowerModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical total-tensor generator, in the existing direct-sum totalization.
Source: Stacks 03EK, 06YM
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def tensorGenerator (W : Scheme.{t}) (P Q : CochainComplex (Modules l E W) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k).val.obj U) :=
  coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq U x y

/-- The cone's degree-zero free generator, fixed by the standard cone inclusion.
Source: Stacks 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def koszulZero (W : Scheme.{t}) (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (PrincipalKoszulStrictReplacement.koszul l E W n).X 0 :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))).inv ≫
      (CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor (Modules l E W) 0).map
          (PrincipalKoszulStrictReplacement.multiplication l E W n))).f 0

/-- The cone's degree-minus-one free generator, with the usual Koszul sign convention.
Source: Stacks 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def koszulMinusOne (W : Scheme.{t}) (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (PrincipalKoszulStrictReplacement.koszul l E W n).X (-1) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))).inv ≫
      (CochainComplex.mappingCone.inl
        ((CochainComplex.singleFunctor (Modules l E W) 0).map
          (PrincipalKoszulStrictReplacement.multiplication l E W n))).v 0 (-1) (by decide)

/-- The two actual Koszul degrees, without excluding either summand.
Source: Stacks 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def koszulDegree (negative : Bool) : ℤ := if negative then -1 else 0

/-- The actual Koszul free basis in either of its two degrees.
Source: Stacks 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def koszulBasis (W : Scheme.{t}) (n : ℕ) (negative : Bool) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W) ⟶
      (PrincipalKoszulStrictReplacement.koszul l E W n).X (koszulDegree negative) :=
  match negative with
  | true => koszulMinusOne l E W n
  | false => koszulZero l E W n

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Ordinary G on cochain complexes, with no exactness assumption.
Source: Stacks 03D2
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def G : CochainComplex (Modules l E Y) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  (pull l E g).mapHomologicalComplex (.up ℤ)

/-- The canonical generator of ordinary pullback, fixed by its adjunction unit.
Source: Stacks 03D2
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def generator (M : Modules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((pull l E g).obj M).val.obj (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  ((adjunction l E g).unit.app M).val.app (op V) x

/-- The strict replacement H(P) with transitions id_P tensor (t,1).
Source: Stacks 0A0E
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def H (W : Scheme.{t}) (P : CochainComplex (Modules l E W) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Modules l E W) ℤ :=
  PrincipalKoszulStrictReplacement.sourceTower l E W P

/-- Pull a diagram back term by term, retaining all maps of the diagram.
Source: Stacks 099N(5)
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def diagramPull : (ℕᵒᵖ ⥤ CochainComplex (Modules l E Y) ℤ) ⥤
    (ℕᵒᵖ ⥤ CochainComplex (Modules l E X) ℤ) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (G l E g)

/-- Normalization of G(P tensor Q_n) to GP tensor Q'_n on both Koszul summands.
The scalar b stays in the first factor. Thus the map uses the actual structural
ring map, respects the unit, and has the inverse inserting 1.
Source: Stacks 03EL, 07A4
(blueprint: def-a1-pulled-koszul-tower-normalization). -/
def KoszulNormalization (P : CochainComplex (Modules l E Y) ℤ)
    (e : (diagramPull l E g).obj (H l E Y P) ≅ H l E X ((G l E g).obj P)) : Prop :=
  ∀ (n : ℕ) (negative : Bool) (p k : ℤ)
      (hp : p + koszulDegree negative = k) (V : Y.ProEt)
      (x : (P.X p).val.obj (op V))
      (b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op ((Scheme.proEtaleBaseChange g).obj V))),
    (((e.hom.app (op n)).f k).val.app (op ((Scheme.proEtaleBaseChange g).obj V)))
      (b • generator l E g (((H l E Y P).obj (op n)).X k) V
        (tensorGenerator l E Y P (PrincipalKoszulStrictReplacement.koszul l E Y n)
          p (koszulDegree negative) k hp (op V) x
            ((koszulBasis l E Y n negative).val.app (op V)
              (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))))) =
      tensorGenerator l E X ((G l E g).obj P)
        (PrincipalKoszulStrictReplacement.koszul l E X n)
        p (koszulDegree negative) k hp (op ((Scheme.proEtaleBaseChange g).obj V))
        (b • generator l E g (P.X p) V x)
        ((koszulBasis l E X n negative).val.app
          (op ((Scheme.proEtaleBaseChange g).obj V))
          (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
            (op ((Scheme.proEtaleBaseChange g).obj V))))

end WeilConjectures.PulledKoszulTowerModel
