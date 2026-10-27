/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.AdicLisseCohomologyCalculus
public import Sheaf.Paper.AdicHeartPullbackFibres
public import Sheaf.Paper.LisseRationalRealization
public import Sheaf.Paper.LisseCompletedSystemComparison
public import Sheaf.Paper.ClassicalWeilFiltrationHeartTransport
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
public import Sheaf.DeligneLaumon.SmoothAffineFrontierStratification
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Classical Weil restriction along finite-field frontiers

Source: blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7;
Bhatt--Scholze, Propositions 6.8.4 and 6.8.14, Remark 6.8.15
(blueprint: def-zl-classical-lisse-restriction-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrontier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- The recorded finite-type base, viewed by the scalar-realization interface.
Source: BS 6.8.14 (blueprint: def-zl-classical-lisse-restriction-models). -/
def realizationBase (X : PerAdic.Base D.k) : LisseRealization.Base D l (Fact.out : l ≠ D.p) where
  scheme := X.scheme

/-- Residue invertibility is inherited from the finite-field datum.
Source: BS 6.8 hypotheses (blueprint: def-zl-classical-lisse-restriction-models). -/
instance residueInvertible (X : PerAdic.Base D.k) (x : X.scheme) :
    Invertible (l : X.scheme.residueField x) :=
  LisseRealization.baseInvertible D l (Fact.out : l ≠ D.p) (realizationBase D l X) x

/-- Absolute separatedness follows from separatedness over the affine point.
Source: BS 6.8 hypotheses (blueprint: def-zl-classical-lisse-restriction-models). -/
instance separated (X : PerAdic.Base D.k) : X.scheme.IsSeparated :=
  Scheme.isSeparated_of_isSeparated_hom (X.scheme ↘ Spec (.of D.k))

/-- Stalk units are the unique inverses of the inherited residue units.
Source: BS 6.8 hypotheses (blueprint: def-zl-classical-lisse-restriction-models). -/
instance stalkUnits (X : PerAdic.Base D.k) :
    Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) :=
  ⟨fun x ↦ isUnit_of_map_unit (IsLocalRing.residue (X.scheme.presheaf.stalk x)) _
    (Eq.mp (congrArg IsUnit (map_natCast _ l)).symm
      (@isUnit_of_invertible _ _ _ (residueInvertible D l X x)))⟩

variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The actual finite coefficient base of the completed-system comparison.
Source: BS 6.8.4 (blueprint: def-zl-classical-lisse-restriction-models). -/
def completedBase (X : PerAdic.Base D.k) (E : Padic.FiniteCoefficientFields l Ω) :
    ProEtale.CompletedLisse.Base.{u} l where
  E := E.val
  field := inferInstance
  algebra := inferInstance
  finiteDimensional := inferInstance
  X := X.scheme
  noetherian := inferInstance
  separated := separated D X
  invertible := residueInvertible D l X

/-- Raw realization at a base, with the prescribed inverse-limit and scalar transport.
Source: BS 6.8.4, 6.8.14 (blueprint: def-zl-classical-lisse-restriction-models). -/
structure Realization where
  models : ∀ X : PerAdic.Base D.k, AdicLisseCalculusModels l Ω X.scheme
  fullyFaithful : ∀ X : PerAdic.Base D.k,
    ((models X).realization ⋙ (models X).comparison.functor).FullyFaithful

/-- This is the recorded model functor, not an independently supplied realization.
Source: BS 6.8.14 (blueprint: def-zl-classical-lisse-restriction-models). -/
def Realization.functor (R : Realization D l Ω) (X : PerAdic.Base D.k) :=
  (R.models X).realization ⋙ (R.models X).comparison.functor

/-- Include the actual finite-free rational lattice model into classical coefficients.
Source: Weil II (1.1.1)d (blueprint: def-zl-classical-lisse-restriction-models). -/
def model (X : PerAdic.Base D.k) (E : Padic.FiniteCoefficientFields l Ω) :
    ProEtale.CompletedLisse.RawRational l (completedBase D l Ω X E) ⥤
      LisseAlgebraicSheaf l X.scheme Ω :=
  ObjectProperty.ι _ ⋙ lisseAlgebraicModelFunctor l X.scheme Ω E

/-- The actual pullback/coefficient arrow of the normalized completed-system family.
Source: BS 6.8.4(1),(4)
(blueprint: def-zl-classical-lisse-restriction-models). -/
def systemArrow {X Y : PerAdic.Base D.k} (f : X.scheme ⟶ Y.scheme)
    (E F : Padic.FiniteCoefficientFields l Ω) (a : E.val →ₐ[ℚ_[l]] F.val) :
    ProEtale.CompletedLisse.Arrow l (completedBase D l Ω Y E)
      (completedBase D l Ω X F) := ⟨f, a⟩

/-- Restriction is the specified quotient-normalized system operation, keeping its lattice.
Source: BS 6.8.4(1),(4)
(blueprint: def-zl-classical-lisse-restriction-models). -/
def restriction (S : ProEtale.CompletedLisse.System.{u} l)
    {X Y : PerAdic.Base D.k} (f : X.scheme ⟶ Y.scheme)
    (E : Padic.FiniteCoefficientFields l Ω) :=
  (S.operation (systemArrow D l Ω f E E (AlgHom.id _ _))).raw

/-- Common-stage pullback uses the recorded completed derived inverse image.
Source: blueprint completed convention
(blueprint: def-zl-classical-lisse-restriction-models). -/
def pull {X Y : PerAdic.Base D.k} (f : X.scheme ⟶ Y.scheme) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ f
    (residueInvertible D l X) (residueInvertible D l Y)

/-- The point fibre, with the actual pbc coefficient equivalence and inverse-limit sections.
Source: BS 6.8.14(2)
(blueprint: def-zl-classical-lisse-restriction-models). -/
def Realization.fiber (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme) :=
  (R.models X).comparison.inverse ⋙ (R.models X).fiber κ x

/-- The fixed point comparison of the supplied normalized realization. The inverse
unit of the coefficient equivalence removes its functor-inverse pair before applying
its recorded lisse fibre comparison.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-lisse-restriction-models). -/
def Realization.lisseFiberIso (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
    (F : LisseAlgebraicSheaf l X.scheme Ω) :
    (R.fiber D l Ω X κ x).obj ((R.functor D l Ω X).obj F) ≅
      lisseAlgebraicFiber l X.scheme Ω x F :=
  ((R.models X).fiber κ x).mapIso
    (((R.models X).comparison.unitIso.app ((R.models X).realization.obj F)).symm) ≪≫
      ((R.models X).fiber_lisse κ x).app F ≪≫
        eqToIso (lisseAlgebraicFiberFunctor_obj l X.scheme x Ω F)

/-- The normalized point identification for a specified realization isomorphism.
There is no independently chosen fibre identification in this definition.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-lisse-restriction-models). -/
def Realization.identifiedFiber (R : Realization D l Ω) (X : PerAdic.Base D.k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
    (F : LisseAlgebraicSheaf l X.scheme Ω)
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω X.scheme)
    (ρ : (R.functor D l Ω X).obj F ≅ N) :
    (R.fiber D l Ω X κ x).obj N ≅ lisseAlgebraicFiber l X.scheme Ω x F :=
  (R.fiber D l Ω X κ x).mapIso ρ.symm ≪≫ R.lisseFiberIso D l Ω X κ x F

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The finite rational sheaf underlying the scalar-realization model.
Source: BS 6.8.14(2)
(blueprint: def-zl-classical-lisse-restriction-models). -/
def realizedSheaf (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (X : PerAdic.Base D.k) (E : Padic.FiniteCoefficientFields l Ω) :
    sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X.scheme ⥤
      Sheaf (ProEt.topology X.scheme) AddCommGrpCat.{u + 1} :=
  (A.realization (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
    (realizationBase D l X)).sheaf D l (Fact.out : l ≠ D.p)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) ⋙
    SheafOfModules.toSheaf ((adicLisseForget X.scheme).obj
      (rationalCoefficientSheaf l X.scheme
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)))

/-- The finite bridge uses actual continuous coefficients, their quotient-normalized
scalar realization and the specified completed-system rationalization.
Source: BS 6.8.4(1),(4), 6.8.14(2), 6.8.15
(blueprint: def-zl-classical-lisse-restriction-models). -/
structure FiniteBridge (R : Realization D l Ω)
    (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (X : PerAdic.Base D.k) (E : Padic.FiniteCoefficientFields l Ω) where
  finite : ProEtale.CompletedLisse.RawRational l (completedBase D l Ω X E) ⥤
    sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X.scheme
  lisse : ∀ F, LisseRealization.Lisse D l (Fact.out : l ≠ D.p)
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
    (realizationBase D l X) (finite.obj F)
  coefficient : ProEtale.CompletedLisse.rationalRing l (completedBase D l Ω X E) ≅
    rationalCoefficientSheaf l X.scheme
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
  coefficient_values : ∀ (U : X.scheme.ProEtᵒᵖ)
    (s : (ProEtale.CompletedLisse.rationalRing l
      (completedBase D l Ω X E)).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      X.scheme U (coefficient.hom.hom.app U s) x =
        (Shrink.algEquiv ℚ_[l] E.val).symm (s.down x)
  sheaf : finite ⋙ realizedSheaf D l Ω A X E ≅
    (S.comparison (completedBase D l Ω X E)).rationalRealization ⋙
      ObjectProperty.ι _ ⋙ ProEtale.CompletedLisse.rationalForget l
        (completedBase D l Ω X E)
  sheaf_linear : ∀ F (U : X.scheme.ProEtᵒᵖ)
    (a : (rationalCoefficientSheaf l X.scheme
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj.obj U)
    (s : (((A.realization (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (realizationBase D l X)).sheaf D l (Fact.out : l ≠ D.p)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj
          (finite.obj F)).val.obj U),
    (sheaf.hom.app F).hom.app U
      (@SMul.smul _ _
        ((((A.realization (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          (realizationBase D l X)).sheaf D l (Fact.out : l ≠ D.p)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj
            (finite.obj F)).val.obj U).isModule.toSMul a s) =
      @SMul.smul _ _
        ((((S.comparison (completedBase D l Ω X E)).rationalRealization.obj F).obj.val.obj
          U).isModule.toSMul) (coefficient.inv.hom.app U a) ((sheaf.hom.app F).hom.app U s)
  stage : model D l Ω X E ⋙ R.functor D l Ω X ≅
    finite ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion E

/-- Restriction comparisons retain the finite unit square, composition and coefficient
extension. The ordinary unit pins the comparison even for a non-k-linear morphism.
Source: BS 6.8.4(1),(4), 6.8.15
(blueprint: def-zl-classical-lisse-restriction-models). -/
structure RestrictionComparison (R : Realization D l Ω)
    (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p)) where
  bridge : ∀ (X : PerAdic.Base D.k) (E : Padic.FiniteCoefficientFields l Ω),
    FiniteBridge D l Ω R S A X E
  normalized : ∀ (X Y : PerAdic.Base D.k) (f : X.scheme ⟶ Y.scheme)
    (E : Padic.FiniteCoefficientFields l Ω),
    LisseRealization.PullNormalized D l (Fact.out : l ≠ D.p)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f
      (A.realization _ (realizationBase D l X))
      (A.realization _ (realizationBase D l Y))
      (A.along (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        (X := realizationBase D l X) (Y := realizationBase D l Y) f)
  finitePull : ∀ (X Y : PerAdic.Base D.k) (f : X.scheme ⟶ Y.scheme)
    (E : Padic.FiniteCoefficientFields l Ω),
    (bridge Y E).finite ⋙ LisseRealization.pull D l (Fact.out : l ≠ D.p)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (X := realizationBase D l X) (Y := realizationBase D l Y) f ≅
        restriction D l Ω S f E ⋙ (bridge X E).finite
  unit_square : ∀ (X Y : PerAdic.Base D.k) (f : X.scheme ⟶ Y.scheme)
    (E : Padic.FiniteCoefficientFields l Ω)
    (F : ProEtale.CompletedLisse.RawRational l (completedBase D l Ω Y E))
    (U : Y.scheme.ProEt)
    (s : (((A.realization (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (realizationBase D l Y)).sheaf D l (Fact.out : l ≠ D.p)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj
        ((bridge Y E).finite.obj F)).val.obj (op U)),
    (((bridge X E).sheaf.hom.app ((restriction D l Ω S f E).obj F)).hom.app
      (op ((proEtaleBaseChange f).obj U)))
      ((((A.realization (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        (realizationBase D l X)).sheaf D l (Fact.out : l ≠ D.p)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).map
          ((finitePull X Y f E).hom.app F)).val.app
        (op ((proEtaleBaseChange f).obj U))
        (((A.along (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
          (X := realizationBase D l X) (Y := realizationBase D l Y) f).comparison
          ((bridge Y E).finite.obj F) ((bridge Y E).lisse F)).inv.val.app
          (op ((proEtaleBaseChange f).obj U))
          (ContinuousRational.moduleUnit f
            (LisseRealization.coefficientPull l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f)
            (((A.realization (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
              (realizationBase D l Y)).sheaf D l (Fact.out : l ≠ D.p)
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj
                ((bridge Y E).finite.obj F)) U s))) =
    ((S.operation (systemArrow D l Ω f E E (AlgHom.id _ _))).rational.hom.app F).hom.val.app
      (op ((proEtaleBaseChange f).obj U))
      (((S.operation (systemArrow D l Ω f E E (AlgHom.id _ _))).modules.rationalUnit l
        ((S.comparison (completedBase D l Ω Y E)).rationalRealization.obj F)).hom.app
          (op U) (((bridge Y E).sheaf.hom.app F).hom.app (op U) s))

end WeilConjectures.ZlFrontier
