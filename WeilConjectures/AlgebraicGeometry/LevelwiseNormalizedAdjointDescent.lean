/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalSystemTransport
public import WeilConjectures.AlgebraicGeometry.LevelwiseNormalizedStrictSystems
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic

public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.FiniteExceptional
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.UnboundedSiteComparison
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.UnboundedFiniteTorComparisonReflection
import WeilConjectures.AlgebraicGeometry.UnboundedOpenCounitSiteTransport
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.OpenExtensionFiniteTor
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SfPreservationClass
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom

/-! # Levelwise normalized adjoint descent

Source: latest blueprint, lem-coef-finite-exceptional.proof.md, last paragraph,
and sk-prop-pe-unbounded-classical unit/direct-image proofs
(blueprint: lem-coef-levelwise-normalized-adjoint-descent).

All systems are ordinary strict semilinear systems. Bounds are existential at
individual levels, with no bound on the whole derived system. Finite coefficient
exponent n+1 is used throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry SheafOfModules
attribute [local instance 10000] strictEtaleSystemDerived strictEtaleLevelDerived
  exceptionalProSystemDerived exceptionalProLevelDerived

attribute [local instance 30000] exceptionalTransportProEtaleCommRingSheafify
  exceptionalTransportProEtaleAddCommGrpSheafify exceptionalTransportProEtaleAddCommGrpLocal


namespace WeilConjectures.LevelwiseNormalizedAdjointDescent

/-- The fixed existing small-site witness, avoiding an unconstrained size search.
Source: blueprint size convention
(blueprint: lem-coef-levelwise-normalized-adjoint-descent). -/
local instance (priority := 50000) descentProSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt :=
  WeilConjectures.scalarReductionSiteSmall.{u, 0} W

variable {O : Type (u + 1)} [CommRing O] {ell : O}
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}

/-- Restriction of the actual site adjunction: stability and invertible actual unit/counit.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: lem-coef-levelwise-normalized-adjoint-descent). -/
structure SiteEquivalence (W : Scheme.{u}) {PE : StrictEtaleEvaluation W O ell}
    (C : ExceptionalSystemSiteComparison.{u} O ell W PE) : Prop where
  inverse : ∀ M, etaleNormalized O ell W PE M →
    proNormalized O ell W C.proEvaluation (C.image.system.inverse.obj M)
  direct : ∀ M, proNormalized O ell W C.proEvaluation M →
    etaleNormalized O ell W PE (C.image.system.direct.obj M)
  unit : ∀ M, etaleNormalized O ell W PE M →
    IsIso (C.image.system.adjunction.unit.app M)
  counit : ∀ M, proNormalized O ell W C.proEvaluation M →
    IsIso (C.image.system.adjunction.counit.app M)

variable (A : EvaluatedAdjunction S)
  (CX : ExceptionalSystemSiteComparison.{u} O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison.{u} O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison.{u} O ell c.Z S.PZ)
  (P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
  (R : ExceptionalSystemCompactificationComparison S CX CY CZ P)

/-- The actual etale-origin composite defining the transported right functor.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: lem-coef-levelwise-normalized-adjoint-descent). -/
def transportedRight :
    DerivedCategory.{u + 2}
      (CoefficientSystem.{u + 1, u, u + 1} (J := Scheme.ProEt.topology Y) O ell) ⥤
    DerivedCategory.{u + 2}
      (CoefficientSystem.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) O ell) :=
  CY.image.system.direct ⋙ A.right ⋙ CX.image.system.inverse

/-- Evaluation of the transported right functor before the final direct-image evaluation.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: lem-coef-levelwise-normalized-adjoint-descent). -/
def rightEtaleEvaluation (n : ℕ) :
    transportedRight A CX CY ⋙ CX.proEvaluation.evaluation n ≅
      CY.image.system.direct ⋙ S.PY.evaluation n ⋙ A.levelRight n ⋙
        (CX.image.level n).inverse :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (CX.image.inverseEvaluation n) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (A.evaluation n) _ ≪≫
        Functor.associator _ _ _)

/-- Canonical finite evaluation of the transported actual right functor.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: lem-coef-levelwise-normalized-adjoint-descent). -/
def rightEvaluation (n : ℕ) :
    transportedRight A CX CY ⋙ CX.proEvaluation.evaluation n ≅
      CY.proEvaluation.evaluation n ⋙
        (CY.image.level n).direct ⋙ A.levelRight n ⋙ (CX.image.level n).inverse :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (CX.image.inverseEvaluation n) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (A.evaluation n) _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CY.image.directEvaluation n) _ ≪≫ Functor.associator _ _ _

/-- All preservation, mate, site equivalence and normalized adjunction conclusions.
Source: blueprint levelwise descent, constructions and conclusions
(blueprint: lem-coef-levelwise-normalized-adjoint-descent). -/
structure Descent where
  leftPreserves : ∀ M, etaleNormalized O ell X S.PX M →
    etaleNormalized O ell Y S.PY (S.functor.obj M)
  rightPreserves : ∀ N, etaleNormalized O ell Y S.PY N →
    etaleNormalized O ell X S.PX (A.right.obj N)
  etaleAdjunction :
    (etaleNormalized O ell Y S.PY).lift
      ((etaleNormalized O ell X S.PX).ι ⋙ S.functor)
      (fun M ↦ leftPreserves M.obj M.property) ⊣
    (etaleNormalized O ell X S.PX).lift
      ((etaleNormalized O ell Y S.PY).ι ⋙ A.right)
      (fun N ↦ rightPreserves N.obj N.property)
  etaleUnit : ∀ M, (etaleAdjunction.unit.app M).hom = A.adjunction.unit.app M.obj
  etaleCounit : ∀ N, (etaleAdjunction.counit.app N).hom = A.adjunction.counit.app N.obj
  finiteSupportComparison : ∀ {m n : ℕ} (h : n ≤ m) M,
    etaleFiniteTor O ell X m M → IsIso ((q A h).app M)
  finiteMate : ∀ {m n : ℕ} (h : n ≤ m) N, etaleFiniteTor O ell Y m N →
    IsIso ((b A h).app N)
  mateIdentity : ∀ (n : ℕ) N, etaleFiniteTor O ell Y n N →
    (b A (Nat.le_refl n)).app N ≫
      (A.levelRight n).map ((S.PY.derivedUnit n).hom.app N) =
    (S.PX.derivedUnit n).hom.app ((A.levelRight n).obj N)
  mateComposition : ∀ {r m n : ℕ} (h : m ≤ r) (k : n ≤ m) N,
    etaleFiniteTor O ell Y r N →
    (S.PX.derivedAssoc h k).hom.app ((A.levelRight r).obj N) ≫
      (b A (k.trans h)).app N =
    (S.PX.scalar k).derived.map ((b A h).app N) ≫
      (b A k).app ((S.PY.scalar h).derived.obj N) ≫
      (A.levelRight n).map ((S.PY.derivedAssoc h k).hom.app N)
  mateUnit : ∀ {m n : ℕ} (h : n ≤ m) M, etaleFiniteTor O ell X m M →
    (S.PX.scalar h).derived.map ((A.levelAdjunction m).unit.app M) ≫
      (b A h).app ((S.levelFunctor m).obj M) ≫
      (A.levelRight n).map ((q A h).app M) =
    (A.levelAdjunction n).unit.app ((S.PX.scalar h).derived.obj M)
  mateCounit : ∀ {m n : ℕ} (h : n ≤ m) N, etaleFiniteTor O ell Y m N →
    (q A h).app ((A.levelRight m).obj N) ≫
      (S.levelFunctor n).map ((b A h).app N) ≫
      (A.levelAdjunction n).counit.app ((S.PY.scalar h).derived.obj N) =
    (S.PY.scalar h).derived.map ((A.levelAdjunction m).counit.app N)
  siteX : SiteEquivalence X CX
  siteY : SiteEquivalence Y CY
  siteZ : SiteEquivalence c.Z CZ
  comparison : ∀ M, etaleNormalized O ell X S.PX M →
    IsIso ((exceptionalSystemComparison R).app M)
  systemAdjunction : ExceptionalOriginAdjunction A.adjunction
    CX.image.system.adjunction CY.image.system.adjunction (exceptionalProSupport P)
    (proNormalized O ell X CX.proEvaluation) (proNormalized O ell Y CY.proEvaluation)
    (exceptionalSystemOriginComparison R)
  finiteAdjunction : ∀ n : ℕ, ExceptionalOriginAdjunction (A.levelAdjunction n)
    (CX.image.level n).adjunction (CY.image.level n).adjunction
    (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct)
    (proFiniteTor O ell X n) (proFiniteTor O ell Y n)
    (exceptionalSystemLevelOriginComparison R n)
  comparisonEvaluation : ∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M)
  unitEvaluation : ∀ (n : ℕ) M,
    (CX.proEvaluation.evaluation n).map (systemAdjunction.adjunction.unit.app M).hom ≫
      (rightEvaluation A CX CY n).hom.app ((exceptionalProSupport P).obj M.obj) ≫
      ((CY.image.level n).direct ⋙ A.levelRight n ⋙ (CX.image.level n).inverse).map
        ((exceptionalProSupportEvaluation P n).hom.app M.obj) =
    ((finiteAdjunction n).adjunction.unit.app
      ⟨(CX.proEvaluation.evaluation n).obj M.obj, M.property.2 n⟩).hom
  counitEvaluation : ∀ (n : ℕ) N,
    (exceptionalProSupportEvaluation P n).hom.app ((transportedRight A CX CY).obj N.obj) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((rightEvaluation A CX CY n).hom.app N.obj) ≫
      ((finiteAdjunction n).adjunction.counit.app
        ⟨(CY.proEvaluation.evaluation n).obj N.obj, N.property.2 n⟩).hom =
    (CY.proEvaluation.evaluation n).map (systemAdjunction.adjunction.counit.app N).hom
  quotientTransition : ∀ {m n : ℕ} (h : n ≤ m) N,
    (CX.proEvaluation.scalar h).derived.map
        ((rightEtaleEvaluation A CX CY m).hom.app N) ≫
      (CX.image.derivedTensor h).inv.app
        ((A.levelRight m).obj ((S.PY.evaluation m).obj (CY.image.system.direct.obj N))) ≫
      (CX.image.level n).inverse.map
        ((b A h).app ((S.PY.evaluation m).obj (CY.image.system.direct.obj N))) ≫
      (CX.image.level n).inverse.map ((A.levelRight n).map
        (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
          ((S.PY.transition h).app (CY.image.system.direct.obj N)))) =
    ((CX.proEvaluation.scalar h).derivedAdj.homEquiv _ _).symm
        ((CX.proEvaluation.transition h).app ((transportedRight A CX CY).obj N)) ≫
      (rightEtaleEvaluation A CX CY n).hom.app N

/-- The ordinary etale adjunction descends to normalized systems with levelwise
bounded constructible finite Tor coefficients, with its actual units and counits.
Source: latest blueprint lem-coef-finite-exceptional.proof.md, final paragraph;
sk-prop-pe-unbounded-classical unit/direct-image proofs
(blueprint: lem-coef-levelwise-normalized-adjoint-descent).

Proof:
1. Evaluate the actual site unit. Unbounded finite-coefficient full faithfulness
makes it invertible at every level; conservative evaluation makes it invertible
on systems. The same argument applies to the counit on etale-origin levels.
2. The derived tensor square identifies reduction adjuncts under inverse image.
Full faithfulness reflects normalization. Unbounded comparison reflection detects
bounded constructibility and finite Tor amplitude before choosing any lower bound.
Constructible-origin comparison supplies the converse direction.
3. Paste the actual proper geometric mate and open extension comparison. Their
unbounded finite comparisons are invertible. Conservative evaluations detect this
for the specified system map, yielding the geometric comparison on the full classes.
4. Open extension preserves each finite Tor interval. Proper image changes its
upper endpoint by twice a finite dimension bound for the compactification (zero
for the empty scheme). Finite exceptional preservation treats the right adjoint.
Unbounded reflection returns both results to the etale levels. Choose intervals
independently at every level.
5. Mate pasting identifies b with the finite exceptional comparison: both are the
unique transpose characterized by the displayed counit equation. Reflect its
invertibility, unit/counit equations, identity index and quotient cocycle through
the fully faithful level comparison.
6. Substitute q and b into the assumed actual transition formulas. Both outputs
are normalized; combine with level preservation. Restrict the ambient adjunction
to the full normalized subcategories, keeping its actual unit and counit.
7. Compose the two actual site Hom bijections with the etale adjunction and the
inverse origin counit. This is precisely ExceptionalOriginAdjunction.transpose;
its inverse and triangles follow from the three actual adjunction triangles.
8. Evaluate these specified Hom words. The canonical comparison evaluations give
the finite exceptional adjunction, its unit and counit. Tensor/site mate pasting
gives the displayed quotient-transition equation on actual systems. No equality
of arbitrary system morphisms is inferred merely from its finite evaluations.
-/
theorem levelwise_normalized_adjoint_descent
    (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) c)
    (A : EvaluatedAdjunction S) (_htrans : TransitionFormulas A) :
    ∃ (CX : ExceptionalSystemSiteComparison _ _ X S.PX)
      (CY : ExceptionalSystemSiteComparison _ _ Y S.PY)
      (CZ : ExceptionalSystemSiteComparison _ _ c.Z S.PZ)
      (P : ExceptionalProCompactSupport _ _ c
        CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
      (R : ExceptionalSystemCompactificationComparison S CX CY CZ P),
      Nonempty (Descent A CX CY CZ P R) := by
  sorry

end WeilConjectures.LevelwiseNormalizedAdjointDescent
