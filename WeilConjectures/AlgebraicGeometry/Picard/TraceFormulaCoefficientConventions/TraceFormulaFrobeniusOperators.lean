/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaLocalFrobeniusOperator
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.FrobeniusRationalPointFixed
public import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Defs
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.TraceFormulaIteratedWeil
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.TraceFormulaSchemeGaloisComparison
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.SixFunctors.AbsoluteFrobeniusSite
public import WeilConjectures.AlgebraicGeometry.SixFunctors.FrobeniusTrivializationPullback
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.PoincareDuality.CondensedFrobeniusOperators.FiniteStrictWeilComplex.TraceFormulaFiniteStrictWeilComplex
public import WeilConjectures.SixFunctors.CondensedFrobeniusOperators.TraceFormulaFiniteCompactTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFiniteCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedGeometricFrobeniusTransport
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusFactorization
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFrobeniusGeometry

/-! # Global and local finite-coefficient geometric Frobenius operators

Source: latest blueprint, sec-smooth-purity/sk-cor-sp-all-coefficients/
def-trf-frobenius-operators.md, clauses 1 and 2
(blueprint: def-trf-frobenius-operators).

The strict Weil category, its iterated isomorphism, the canonical comparison kappa,
and the local stalk construction are reused. Global transport is the direct
isomorphism along g^m, including restriction along Spec(gamma^m) on the base.
The retained model compactification represents the specified compact-support functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TraceFormulaCoefficientConventions

/-- The specified first arrow g_(gamma,c)^(m,*), using the actual power square.
The helper constructs iota_(b_m) followed by Fib_s(e_!), with no implicit
identification of the semilinear base automorphism with the identity.
Source: latest blueprint, def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def globalCompactFrobeniusTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex)
    (m : ℕ) (_hm : 1 ≤ m) :
    (T.finiteGlobalCompactSections c₀).obj K.obj.carrier ≅
      (T.finiteGlobalCompactSections c₀).obj
        ((proEtaleConstantRingDerivedPullback T.coefficientRing
          ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ m)).obj K.obj.carrier) :=
  letI := T.finitePowerCompactTransport_isIso c₀ m K.obj.carrier
  asIso (T.finitePowerCompactTransport c₀ m K.obj.carrier)

/-- The global compact-support coefficient-complex endomorphism
F_(c,K)^m = RΓ_c(phi^[m]) after g_(gamma,c)^(m,*).
Source: latest blueprint, def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def globalCompactFrobenius (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex)
    (m : ℕ) (hm : 1 ≤ m) :
    End ((T.finiteGlobalCompactSections c₀).obj K.obj.carrier) :=
  (T.globalCompactFrobeniusTransport c₀ K m hm).hom ≫
    (T.finiteGlobalCompactSections c₀).map (T.iteratedWeilIsomorphism K m hm).hom

/-- The induced operator on H_c^i, for every integer i, including negative degrees.
Source: latest blueprint, def-trf-frobenius-operators, clause 1
(blueprint: def-trf-frobenius-operators). -/
def globalCompactFrobeniusCohomology (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom) (K : T.strictWeilComplex)
    (m : ℕ) (hm : 1 ≤ m) (i : ℤ) :=
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) i).map
      (T.globalCompactFrobenius c₀ K m hm)

/-- The canonical stalk transport tau_(x,m): rho from Phi^m xbar = xbar, followed
by Fib_s(Lxbar^* kappa^(m)). The fibre functor is exact terminal sections of the
pullback to Spec k, not the unevaluated sheaf-module complex on Spec k.
Source: latest blueprint, def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def localFrobeniusTransport (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m)
    (x : T.datum.extensionPoints T.X₀ m hm) :
    (T.finiteLocalFibre (localExtensionPoint T.datum T.X₀ m hm x)).obj K.obj.carrier ≅
      (T.finiteLocalFibre (localExtensionPoint T.datum T.X₀ m hm x)).obj
        ((proEtaleConstantRingDerivedPullback T.coefficientRing
          ((End.of (T.datum.geometricGaloisFrobenius T.X₀)) ^ m)).obj K.obj.carrier) :=
  T.finiteLocalRho K m (localExtensionPoint T.datum T.X₀ m hm x)
      (rationalPoint_schemeFrobenius_fixed T.datum T.X₀ m hm x) ≪≫
    (T.finiteLocalFibre (localExtensionPoint T.datum T.X₀ m hm x)).mapIso
      ((T.selectedSchemeGaloisComparison T.X₀ m hm).app K.obj.carrier)

/-- The local Frobenius operator at the canonical geometric lift of x. This
specializes the existing rho-kappa-phi composite, without a new arbitrary map or
an extra fixed-point hypothesis. Thus it is Fib_s(Lxbar^* phi^[m]) after tau_(x,m).
Source: latest blueprint, def-trf-frobenius-operators, clause 2
(blueprint: def-trf-frobenius-operators). -/
def localFrobeniusAtRationalPoint (T : TraceFormulaCoefficientConventions.{u})
    (K : T.strictWeilComplex) (m : ℕ) (hm : 1 ≤ m)
    (x : T.datum.extensionPoints T.X₀ m hm) :
    End ((T.finiteLocalFibre (localExtensionPoint T.datum T.X₀ m hm x)).obj K.obj.carrier) :=
  T.finiteLocalFrobenius K m hm (localExtensionPoint T.datum T.X₀ m hm x)
    (rationalPoint_schemeFrobenius_fixed T.datum T.X₀ m hm x)

end WeilConjectures.TraceFormulaCoefficientConventions

namespace WeilConjectures.CondensedFrobeniusOperators

/-- The scheme-square for the `m`-th geometric-Frobenius power.  Its base map and
middle map are the actual powers, so the compact transport below is `t_{c,g^m}`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`
(blueprint: def-trf-frobenius-operators).
-/
noncomputable def poweredGeometry
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (m : ℕ) :
    Geometry F.k := by
  let q := condensedFrobeniusGeometry F Y₀
  let g : q.X ≅ q.X :=
    { hom := (F.geometricFrobenius Y₀).hom
      inv := (F.geometricFrobenius Y₀).inv
      hom_inv_id := (F.geometricFrobenius Y₀).hom_inv_id
      inv_hom_id := (F.geometricFrobenius Y₀).inv_hom_id }
  have hbase : g.hom ≫ q.a = q.a ≫ q.b.hom := by
    simpa [q, g, condensedFrobeniusGeometry] using q.comm
  exact
    { X := q.X
      X' := q.X
      a := q.a
      a' := q.a
      b := q.b.pow m
      h := g.pow m
      comm := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Iso.pow_succ, Iso.pow_succ, Iso.trans_hom, Iso.trans_hom]
          simp only [Category.assoc]
          rw [hbase]
          simpa [Category.assoc] using congrArg (fun f => f ≫ q.b.hom) ih
      separated := q.separated
      finiteType := q.finiteType
      quasiCompact := q.quasiCompact
      separated' := q.separated
      finiteType' := q.finiteType
      quasiCompact' := q.quasiCompact }

/-- The global operator at any coefficient ring with the normalized transport data.
This is the same insertion/exchange/iterated-Weil composite as the finite-quotient
operator below; its transport input carries the full normalization laws.
Source: def-trf-frobenius-operators, clause (1)
(blueprint: def-trf-frobenius-operators). -/
noncomputable def globalFrobeniusMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (S : CompactData Λ (Spec (.of F.k))) (hS : Laws Λ S)
    (K : (boundedConstructible (condensedRingObj Λ (F.geometricFiber Y₀).left)).FullSubcategory)
    (φ : (L Λ (condensedFrobeniusGeometry F Y₀).h.hom).obj K.obj ≅ K.obj)
    (c : Compactification (condensedFrobeniusGeometry F Y₀).a) (m : ℕ) :
    End ((Γ Λ (Spec (.of F.k))).obj ((C Λ c).obj K.obj)) :=
  compactTransport Λ S (poweredGeometry F Y₀ m) c c K
      (hS.pull_constructible (poweredGeometry F Y₀ m) K) ≫
    (Γ Λ (Spec (.of F.k))).map
      ((C Λ c).map (iteratedWeilMap Λ F Y₀ K.obj φ m).hom)

/-- The global geometric Frobenius operator
`F^m_{c,K} = RΓ_c(φ^[m]) ∘ t_{c,g^m}`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`
(blueprint: def-trf-frobenius-operators).
-/
noncomputable def condensedGlobalFrobenius
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (c : Compactification (geometricFrobeniusGeometry F Y₀).a) (m : ℕ) (_hm : 1 ≤ m) :
    End ((Γ (finiteCoefficient ell E n) (Spec (.of F.k))).obj
      ((C (finiteCoefficient ell E n) c).obj K.carrier.obj)) := by
  let Λ := finiteCoefficient ell E n
  let q := poweredGeometry F Y₀ m
  let S := finiteTransportData F ell hEll E n hn
  let hM := S.property.pull_constructible q K.carrier
  exact
    compactTransport Λ S.val q c c K.carrier hM ≫
      (Γ Λ (Spec (.of F.k))).map
        ((C Λ c).map (iteratedWeil F Y₀ ell E n hn K m).hom)

/-- A rational point with its canonical geometric lift from the finite extension point.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`
(blueprint: def-trf-frobenius-operators).
-/
structure FiniteFixedPoint
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (m : ℕ) (hm : 1 ≤ m) where
  x : F.extensionPoints Y₀ m hm

/-- The geometric lift of `x ∈ X₀(F_(q^m))`, using the fixed inclusion into `k`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`
(blueprint: def-trf-frobenius-operators).
-/
noncomputable def FiniteFixedPoint.xbar
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (m : ℕ) (hm : 1 ≤ m)
    (P : FiniteFixedPoint F Y₀ m hm) : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left :=
  extensionPointGeometry F Y₀ m hm P.x

/-- The canonical stalk transport before point evaluation. After applying `Γ`, this
is `τ_{x,m} = Fib(Lx̄^*κ^(m)) ∘ ρ_{x,m}`. Its first two factors form `ρ` from
the recorded fixed-point equality and pullback compositor; the last factor applies
the normalized scheme/Galois comparison.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`
(blueprint: def-trf-frobenius-operators).
-/
noncomputable def fixedPointReturn
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    (P : FiniteFixedPoint F Y₀ m hm)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn) :
    (L (finiteCoefficient ell E n) (P.xbar F Y₀ m hm)).obj K.carrier.obj ≅
      (L (finiteCoefficient ell E n) (P.xbar F Y₀ m hm)).obj
        ((L (finiteCoefficient ell E n)
          ((condensedFrobeniusGeometry F Y₀).h.pow m).hom).obj K.carrier.obj) := by
  let Λ := finiteCoefficient ell E n
  let xbar := P.xbar F Y₀ m hm
  exact (eqToIso (congrArg (fun f => (L Λ f).obj K.carrier.obj)
      (rationalPoint_schemeFrobenius_fixed F Y₀ m hm P.x))).symm ≪≫
    (leftDerivedUpperStarComp Λ xbar (F.coefficientFreeSchemeFrobeniusIterate Y₀ m)).app
      K.carrier.obj ≪≫
    (L Λ xbar).mapIso (finiteSchemeGaloisComparison F Y₀ ell hEll E n hn K m hm)

/-- The local geometric Frobenius operator
`F_{x,m}=Fib(Lx̄^*φ^[m]) ∘ Fib(Lx̄^*κ^(m)) ∘ ρ_{x,m}`.
The middle factor is the finite-coefficient scheme/Galois comparison represented by the
powered condensed geometry; the final map is the iterated Weil isomorphism.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`
(blueprint: def-trf-frobenius-operators).
-/
noncomputable def condensedLocalFrobenius
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    (P : FiniteFixedPoint F Y₀ m hm)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn) :
    End ((Γ (finiteCoefficient ell E n) (Spec (.of F.k))).obj
      ((L (finiteCoefficient ell E n) (P.xbar F Y₀ m hm)).obj K.carrier.obj)) := by
  let Λ := finiteCoefficient ell E n
  let G := Γ Λ (Spec (.of F.k))
  let tau := fixedPointReturn F Y₀ ell hEll E n hn m hm P K
  exact G.map tau.hom ≫
    G.map ((L Λ (P.xbar F Y₀ m hm)).map
      (iteratedWeil F Y₀ ell E n hn K m).hom)

/-- The induced global operator on every integer compact cohomology group.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`
(blueprint: def-trf-frobenius-operators). -/
noncomputable def condensedGlobalFrobeniusCohomology
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (c : Compactification (condensedFrobeniusGeometry F Y₀).a) (m : ℕ) (hm : 1 ≤ m) (i : ℤ) :=
  (@DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2}
    (ModuleCat.{u + 1, u + 1} (condensedScalarRing (finiteCoefficient ell E n)))
    inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian
      (ModuleCat.{u + 1, u + 1} (condensedScalarRing (finiteCoefficient ell E n)))) i).map
    (condensedGlobalFrobenius F Y₀ ell hEll E n hn K c m hm)

end WeilConjectures.CondensedFrobeniusOperators
