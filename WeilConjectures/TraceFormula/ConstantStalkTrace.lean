/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientConventions
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.TraceFormula.PointTransportComposition
public import WeilConjectures.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import WeilConjectures.AlgebraicGeometry.CoefficientPullbackUnitCoordinates
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf

/-! # The constant coefficient complex has unit fixed-stalk trace

Source: latest blueprint, sec-trace-formula/sk-p-pairing,
cor-trf-constant-stalk-trace.md and its proof
(blueprint: cor-trf-constant-stalk-trace).

The fixed-stalk operator uses the specified intrinsic-to-tensor presentation comparison,
the normalized inverse-image stalk comparison, and multiplication on the coefficient unit.
The native condensed presentation of the constant complex is the regular module in degree zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The constant discrete coefficient ring, as a condensed ring in the site universe.
`ULift` changes only size; this is the sheafification of the constant ring presheaf.
Source: latest blueprint, cor-trf-constant-stalk-trace.md, the constant complex
(blueprint: cor-trf-constant-stalk-trace). -/
abbrev constantStalkTraceCoefficient (A : Type u) [CommRing A] :=
  Sheaf.constRingSheaf (coherentTopology Profinite.{u}) (ULift.{u + 1, u} A)

/-- The native presentation of `A_X[0]`, the regular coefficient module in degree zero.
Source: latest blueprint, cor-trf-constant-stalk-trace.proof.md, first sentence
(blueprint: cor-trf-constant-stalk-trace). -/
def constantStalkTraceNativeComplex (A : Type u) [CommRing A] (X : Scheme.{u}) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (Mod.regular (AlgebraicGeometry.ProEtale.condensedRingObj
      (constantStalkTraceCoefficient A) X))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The comparison `gamma = c o stalk(b)`, followed by the specified fixed-point equality.
Both isomorphisms are the recorded unit-normalized comparisons; no new one is chosen.
Source: latest blueprint, cor-trf-constant-stalk-trace.md, fixed geometric stalk
(blueprint: cor-trf-constant-stalk-trace). -/
def constantStalkTraceComparison (n : ℕ) {X : Scheme.{u}} (h : X ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (hx : x ≫ h = x) :
    (proEtaleFiniteCoefficientDerivedStalk (Padic.coefficientExtensionRing l E (n + 1)) x).obj
        ((finiteDerivedPullback l E n h).obj (finiteConstantCoefficientObject l E X n)) ≅
      (proEtaleFiniteCoefficientDerivedStalk
        (Padic.coefficientExtensionRing l E (n + 1)) x).obj
          (finiteConstantCoefficientObject l E X n) :=
  (proEtaleFiniteCoefficientDerivedStalk _ x).mapIso
      ((pointPowerPullbackModel l E n h).app (finiteConstantCoefficientObject l E X n)) ≪≫
    (proEtaleDerivedPullbackStalkComparison
      (Padic.coefficientExtensionRing l E (n + 1)) h x).app
        (finiteConstantCoefficientObject l E X n) ≪≫
    eqToIso (congrArg (fun y ↦ (proEtaleFiniteCoefficientDerivedStalk
      (Padic.coefficientExtensionRing l E (n + 1)) y).obj
        (finiteConstantCoefficientObject l E X n)) hx)

/-- The fixed-stalk endomorphism `u_x o gamma^{-1}` for the canonical multiplication `u`.
Source: latest blueprint, cor-trf-constant-stalk-trace.md, trace endomorphism
(blueprint: cor-trf-constant-stalk-trace). -/
def constantStalkTraceEndomorphism (n : ℕ) {X : Scheme.{u}} (h : X ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (hx : x ≫ h = x) :
    (proEtaleFiniteCoefficientDerivedStalk
      (Padic.coefficientExtensionRing l E (n + 1)) x).obj
        (finiteConstantCoefficientObject l E X n) ⟶
    (proEtaleFiniteCoefficientDerivedStalk
      (Padic.coefficientExtensionRing l E (n + 1)) x).obj
        (finiteConstantCoefficientObject l E X n) :=
  (constantStalkTraceComparison l E n h x hx).inv ≫
    (proEtaleFiniteCoefficientDerivedStalk _ x).map
      (ConstantGeometricStalkUnit.finiteUnit l E h n).hom

/-- The canonical constant-coefficient fixed-stalk trace is one, and the constant complex
is site-perfect. The positive exponent is indexed by `n + 1`. The stalk ring is lifted
into the coefficient universe; taking `.down` reads its trace as an element of `A`.
The existential perfectness proof supplies the domain condition of the recorded trace,
rather than assuming perfectness of the stalk.

Source: latest blueprint, sec-trace-formula/sk-p-pairing,
cor-trf-constant-stalk-trace.md and cor-trf-constant-stalk-trace.proof.md
(blueprint: cor-trf-constant-stalk-trace).
Proof: the regular coefficient sheaf is free of rank one. The identity cover and its
single degree-zero term therefore prove site-perfectness in the native coefficient model.
The geometric stalk of the constant sheaf is the free rank-one coefficient module,
with generator the germ of one. Multiplication sends `1 tensor 1` to one. The presentation
comparison preserves the pullback-unit section, and the normalized inverse-image stalk
comparison sends that section to the same constant germ. Using `hx`, their composite
identifies the source and target stalks, and `u_x o gamma^{-1}` fixes the generator.
It is linear and hence the identity of `A[0]`. In particular the stalk is perfect.
On its single projective term use the dual frame `(1, id_A)`: the chain-supertrace
formula gives `(-1)^0 * id_A(1) = 1` and identifies it with the categorical trace.
The size lift preserves one, so the scalar in `A` is also one. -/
theorem constantStalkTrace (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (F : IntermediateField (Padic c.l) c.Qbar) [FiniteDimensional (Padic c.l) F]
    (n : ℕ) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] (h : X ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (hx : x ≫ h = x) :
    AlgebraicGeometry.ProEtale.CondensedRing.IsPerfectOnCoefficientSite
        (constantStalkTraceCoefficient (Padic.coefficientExtensionRing c.l F (n + 1))) X
        (constantStalkTraceNativeComplex (Padic.coefficientExtensionRing c.l F (n + 1)) X) ∧
      ∃ hp : @DerivedCategory.IsPerfectRingComplex
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing c.l F (n + 1))) _
          (HasDerivedCategory.ofIsGrothendieckAbelian
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing c.l F (n + 1)))))
          ((proEtaleFiniteCoefficientDerivedStalk
            (Padic.coefficientExtensionRing c.l F (n + 1)) x).obj
              (finiteConstantCoefficientObject c.l F X n)),
        (@DerivedCategory.perfectCategoricalTrace
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing c.l F (n + 1))) _
          (HasDerivedCategory.ofIsGrothendieckAbelian
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing c.l F (n + 1))))) _ hp
          (constantStalkTraceEndomorphism c.l F n h x hx)).down = 1 := by
  sorry

end WeilConjectures
