/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation2
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SmoothPurity.TraceFixedScheme
public import WeilConjectures.AlgebraicGeometry.FixedScheme
public import WeilConjectures.ZetaWeil.FiniteTraceGlobalOperator
public import WeilConjectures.SmoothPurity.FiniteTraceFormulaConventions.FiniteTraceFormulaConventions
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.TraceFormula.FiniteFieldDatum.FrobeniusOpenSquare
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.RelativeFrobeniusGeometricFiber
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek

/-!
# Extension by zero of a Frobenius coefficient morphism

Source: latest blueprint, part-duality-trace-formula/sec-trace-formula/
sec-the-trace-formula-with-finite-coefficients/sk-thm-tf-coefficient-morphism-formula/
lem-trf-compactification-graph-operator.md, clauses (1)--(3)
(blueprint: lem-trf-compactification-graph-operator).

All objects are the recorded finite-coefficient ones of `FiniteTraceFormulaConventions`
(def-trf-coefficient-conventions): complexes are objects of the ordinary derived category of
module objects over the pulled-back discrete condensed ring `T.coefficients`, which is the
category of the recorded graph correspondence (def-trf-graph-correspondence) and global
operator (def-trf-global-operator). The compactification is a recorded
`Compactification T.X₀.hom` (def-weil-compactifications-refinements); the Frobenii are the
scalar extensions of the model's q-power Frobenius (def-trf-scheme-frobenius,
`FiniteFieldDatum.relativeFrobenius`); extension by zero is the exact levelwise `D(j_!)`;
`b_m` is the open-square exchange `boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'`
(lem-trf-open-square-exchange), i.e. the inverse of the open base-change mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactificationGraphOperator

variable (T : FiniteTraceFormulaConventions.{u})

/-- The compactifying model `X̄₀` of the recorded compactification `j₀ : X₀ → X̄₀` over `k₀`.
Source: lem-trf-compactification-graph-operator, first paragraph
(blueprint: lem-trf-compactification-graph-operator). -/
abbrev barModel (c₀ : Compactification T.X₀.hom) : Over (Spec (.of T.datum.k₀)) :=
  Over.mk c₀.g

/-- The compactifying model is locally of finite type over `k₀`: its structure map is proper.
Source: lem-trf-compactification-graph-operator, first paragraph
(blueprint: lem-trf-compactification-graph-operator). -/
instance barModel_locallyOfFiniteType (c₀ : Compactification T.X₀.hom) :
    LocallyOfFiniteType (barModel T c₀).hom :=
  inferInstanceAs (LocallyOfFiniteType c₀.g)

/-- The compactifying model is quasi-compact over `k₀`: its structure map is proper.
Source: lem-trf-compactification-graph-operator, first paragraph
(blueprint: lem-trf-compactification-graph-operator). -/
instance barModel_quasiCompact (c₀ : Compactification T.X₀.hom) :
    QuasiCompact (barModel T c₀).hom :=
  inferInstanceAs (QuasiCompact c₀.g)

/-- The open immersion `j : X → X̄` of geometric fibres, the base change of `j₀` to `k`.
Source: lem-trf-compactification-graph-operator, first paragraph
(blueprint: lem-trf-compactification-graph-operator). -/
def openImmersion (c₀ : Compactification T.X₀.hom) :
    T.datum.geometricFiber T.X₀ ⟶ T.datum.geometricFiber (barModel T c₀) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))).map
    (Over.homMk (U := T.X₀) (V := barModel T c₀) c₀.i c₀.comm.symm)

/-- The q-power scheme Frobenius of the geometric fibre of a model, as a `k`-endomorphism.
Its underlying scheme map is `FiniteFieldDatum.relativeFrobenius`, which is
`FiniteFieldDatum.schemeFrobenius` of def-trf-scheme-frobenius.
Source: def-trf-scheme-frobenius (blueprint: lem-trf-compactification-graph-operator). -/
def frobenius (Y₀ : Over (Spec (.of T.datum.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] : T.datum.geometricFiber Y₀ ⟶ T.datum.geometricFiber Y₀ :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap T.datum.k₀ T.datum.k)))).map
    (Over.homMk (Y₀.left.iterateFrobenius T.datum.prime (T.datum.model_characteristic Y₀.hom)
      T.datum.a) (T.datum.model_frobenius_over Y₀.hom))

/-- The iterate `Φ^m` of the scheme Frobenius, `m ≥ 0`, as a `k`-endomorphism.
Source: def-trf-scheme-frobenius, iterates (blueprint: lem-trf-compactification-graph-operator). -/
def frobeniusIterate (Y₀ : Over (Spec (.of T.datum.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] (m : ℕ) : T.datum.geometricFiber Y₀ ⟶ T.datum.geometricFiber Y₀ :=
  End.asHom (End.of (frobenius T Y₀) ^ m)

/-- The iterates `ψ_m : LΦ^{m*}K → K`, `m ≥ 1`, of a Frobenius coefficient morphism
`ψ : LΦ^*K → K`; the value at index `m` is `ψ_{m+1}`. As in the blueprint,
`ψ_1 = ψ` and `ψ_{m+1} = ψ ∘ LΦ^*ψ_m ∘ (LΦ^{(m+1)*} ≅ LΦ^*LΦ^{m*})`, the last arrow being
the recorded composition isomorphism `leftDerivedUpperStarComp`. No invertibility is assumed.
Source: def-trf-frobenius-coefficient-morphism, clauses (1)--(2)
(blueprint: def-trf-frobenius-coefficient-morphism). -/
def coefficientIterate (Y₀ : Over (Spec (.of T.datum.k₀))) [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (T.datum.geometricFiber Y₀).left)
      Ab.{u + 1}) (condensedRingObj T.coefficients (T.datum.geometricFiber Y₀).left)))
    (ψ : (moduleObjectDerivedPullback T.coefficients (frobenius T Y₀).left).obj K ⟶ K) :
    (m : ℕ) → (moduleObjectDerivedPullback T.coefficients
      (frobeniusIterate T Y₀ (m + 1)).left).obj K ⟶ K
  | 0 => eqToHom (congrArg (fun f : T.datum.geometricFiber Y₀ ⟶ T.datum.geometricFiber Y₀ ↦
      (moduleObjectDerivedPullback T.coefficients f.left).obj K)
      (pow_one (End.of (frobenius T Y₀)))) ≫ ψ
  | m + 1 => eqToHom (congrArg (fun f : T.datum.geometricFiber Y₀ ⟶ T.datum.geometricFiber Y₀ ↦
      (moduleObjectDerivedPullback T.coefficients f.left).obj K)
      (pow_succ (End.of (frobenius T Y₀)) (m + 1))) ≫
    (leftDerivedUpperStarComp T.coefficients (frobenius T Y₀).left
      (frobeniusIterate T Y₀ (m + 1)).left).hom.app K ≫
    (moduleObjectDerivedPullback T.coefficients (frobenius T Y₀).left).map
      (coefficientIterate Y₀ K ψ m) ≫ ψ

/-- Extension by zero `j_!` on ordinary module-object derived categories: the exact
levelwise functor `D(j_!)` (def-weil-extension-by-zero in these coordinates).
Source: lem-trf-compactification-graph-operator, clause (1)
(blueprint: lem-trf-compactification-graph-operator). -/
abbrev extensionByZero (c₀ : Compactification T.X₀.hom)
    [IsOpenImmersion (openImmersion T c₀).left] :=
  (openImmersionLowerShriek T.coefficients (openImmersion T c₀).left).mapDerivedCategory

/-- The open-square exchange `b : Lḡ^* j_! K → j_! Lg^* K` for a Cartesian square
`j ∘ g = ḡ ∘ j` of Frobenius maps, on a bounded constructible `K`: the component of the
recorded exchange isomorphism `boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'`,
the inverse of the canonical open base-change mate (lem-trf-open-square-exchange).
Source: lem-trf-compactification-graph-operator, definition of `b_m`
(blueprint: lem-trf-compactification-graph-operator). -/
def openSquareExchange (c₀ : Compactification T.X₀.hom)
    [IsSeparated (T.datum.geometricFiber T.X₀).hom]
    [LocallyOfFiniteType (T.datum.geometricFiber T.X₀).hom]
    [QuasiCompact (T.datum.geometricFiber T.X₀).hom]
    [IsProper (T.datum.geometricFiber (barModel T c₀)).hom]
    [IsOpenImmersion (openImmersion T c₀).left]
    (g : T.datum.geometricFiber T.X₀ ⟶ T.datum.geometricFiber T.X₀)
    (gbar : T.datum.geometricFiber (barModel T c₀) ⟶ T.datum.geometricFiber (barModel T c₀))
    (sq : IsPullback g (openImmersion T c₀) (openImmersion T c₀) gbar)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (T.datum.geometricFiber T.X₀).left)
      Ab.{u + 1}) (condensedRingObj T.coefficients (T.datum.geometricFiber T.X₀).left)))
    (hK : T.constructibleFiniteTor (T.datum.geometricFiber T.X₀).left K) :
    (moduleObjectDerivedPullback T.coefficients gbar.left).obj ((extensionByZero T c₀).obj K) ⟶
      (extensionByZero T c₀).obj ((moduleObjectDerivedPullback T.coefficients g.left).obj K) := by
  let F := T.datum
  letI : Fact F.p.Prime := ⟨F.prime⟩
  letI : Fintype F.k₀ := Fintype.ofFinite F.k₀
  have hc : Fintype.card F.k₀ = F.p ^ F.a := by
    simpa only [Nat.card_eq_fintype_card] using F.card_base.trans F.cardinality_eq
  letI : CharP F.k₀ F.p := charP_of_card_eq_prime_pow hc
  letI : CharP F.k F.p := charP_of_injective_algebraMap' F.k₀ F.p
  letI : Fact (ringChar F.k).Prime := ⟨by rw [ringChar.eq F.k F.p]; exact F.prime⟩
  letI : Fact (ringChar F.k ≠ T.ell) :=
    ⟨by rw [ringChar.eq F.k F.p]; exact Ne.symm T.ell_ne⟩
  exact ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' T.coefficients T.ell
    sq).hom.app ⟨K, hK.1⟩).hom

/-- The extension `v̄ = j_!v ∘ b` of a coefficient map `v : Lg^*K → K` along `j`.
Source: lem-trf-compactification-graph-operator, clause (1), display of `v̄`
(blueprint: lem-trf-compactification-graph-operator). -/
def extendCoefficient (c₀ : Compactification T.X₀.hom)
    [IsSeparated (T.datum.geometricFiber T.X₀).hom]
    [LocallyOfFiniteType (T.datum.geometricFiber T.X₀).hom]
    [QuasiCompact (T.datum.geometricFiber T.X₀).hom]
    [IsProper (T.datum.geometricFiber (barModel T c₀)).hom]
    [IsOpenImmersion (openImmersion T c₀).left]
    (g : T.datum.geometricFiber T.X₀ ⟶ T.datum.geometricFiber T.X₀)
    (gbar : T.datum.geometricFiber (barModel T c₀) ⟶ T.datum.geometricFiber (barModel T c₀))
    (sq : IsPullback g (openImmersion T c₀) (openImmersion T c₀) gbar)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (T.datum.geometricFiber T.X₀).left)
      Ab.{u + 1}) (condensedRingObj T.coefficients (T.datum.geometricFiber T.X₀).left)))
    (hK : T.constructibleFiniteTor (T.datum.geometricFiber T.X₀).left K)
    (v : (moduleObjectDerivedPullback T.coefficients g.left).obj K ⟶ K) :
    (moduleObjectDerivedPullback T.coefficients gbar.left).obj ((extensionByZero T c₀).obj K) ⟶
      (extensionByZero T c₀).obj K :=
  openSquareExchange T c₀ g gbar sq K hK ≫ (extensionByZero T c₀).map v

/-- The endomorphism `v_ȳ` of the geometric stalk `M_ȳ = Lȳ^*M` induced by `v : Lg^*M → M`
at a geometric point fixed by `g`, through `(Lg^*M)_ȳ ≅ M_ȳ`, i.e. through the recorded
composition isomorphism for `ȳ = ȳ ∘ g`.
Source: lem-trf-compactification-graph-operator, clause (2)
(blueprint: lem-trf-compactification-graph-operator). -/
def stalkEndomorphism {Y : Scheme.{u}} (g : Y ⟶ Y) {Ω : Type u} [Field Ω]
    (y : Spec (.of Ω) ⟶ Y) (hy : y ≫ g = y)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj T.coefficients Y)))
    (v : (moduleObjectDerivedPullback T.coefficients g).obj M ⟶ M) :
    (moduleObjectDerivedPullback T.coefficients y).obj M ⟶
      (moduleObjectDerivedPullback T.coefficients y).obj M :=
  eqToHom (by rw [hy]; rfl) ≫
    (leftDerivedUpperStarComp T.coefficients y g).hom.app M ≫
    (moduleObjectDerivedPullback T.coefficients y).map v

/-- The canonical stalk map `K_x → (j_!K)_{jx}`: the unit `K → j^*j_!K`, followed by the
recorded identification of `j^*` with its derived functor and the composition isomorphism.
Source: lem-trf-compactification-graph-operator, clause (2), `(j_!K)_ȳ = K_ȳ`
(blueprint: lem-trf-compactification-graph-operator). -/
def insideStalkMap (c₀ : Compactification T.X₀.hom)
    [IsOpenImmersion (openImmersion T c₀).left] {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ (T.datum.geometricFiber T.X₀).left)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (T.datum.geometricFiber T.X₀).left)
      Ab.{u + 1}) (condensedRingObj T.coefficients (T.datum.geometricFiber T.X₀).left))) :
    (moduleObjectDerivedPullback T.coefficients x).obj K ⟶
      (moduleObjectDerivedPullback T.coefficients (x ≫ (openImmersion T c₀).left)).obj
        ((extensionByZero T c₀).obj K) :=
  (moduleObjectDerivedPullback T.coefficients x).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction T.coefficients
          (openImmersion T c₀).left).unit.app K ≫
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion T.coefficients
          (openImmersion T c₀).left).inv.app ((extensionByZero T c₀).obj K)) ≫
    (leftDerivedUpperStarComp T.coefficients x (openImmersion T c₀).left).inv.app
      ((extensionByZero T c₀).obj K)

/-- The compactification `(j, ā)` of the structure map `a_X`, through `X̄`.
Source: lem-trf-compactification-cohomology, the compactification `j`
(blueprint: lem-trf-compactification-graph-operator). -/
def openCompactification (c₀ : Compactification T.X₀.hom)
    [IsProper (T.datum.geometricFiber (barModel T c₀)).hom]
    [IsOpenImmersion (openImmersion T c₀).left] :
    Compactification (T.datum.geometricFiber T.X₀).hom where
  Z := (T.datum.geometricFiber (barModel T c₀)).left
  g := (T.datum.geometricFiber (barModel T c₀)).hom
  i := (openImmersion T c₀).left
  comm := (Over.w (openImmersion T c₀)).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The comparison `C_{j,K} : RΓ_c(X,K) → RΓ(X̄, j_!K)`: compact support computed with the
compactification `(j, ā)` is `Fib_s Rā_* j_!K`, and ordinary cohomology of the proper `X̄`
is compact support for `(id, ā)`; the two differ by the recorded identification
`D((id)_!) ≅ 𝟭` of `derivedOpenImmersionLowerShriekId`.
Source: lem-trf-compactification-cohomology, displayed comparison
(blueprint: lem-trf-compactification-graph-operator). -/
def compactificationComparison (c₀ : Compactification T.X₀.hom)
    [IsProper (T.datum.geometricFiber (barModel T c₀)).hom]
    [IsOpenImmersion (openImmersion T c₀).left]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (T.datum.geometricFiber T.X₀).left)
      Ab.{u + 1}) (condensedRingObj T.coefficients (T.datum.geometricFiber T.X₀).left))) :
    (T.operatorCompactSupport (openCompactification T c₀)).obj K ⟶
      (T.operatorCompactSupport
        (Compactification.ofIsProper (T.datum.geometricFiber (barModel T c₀)).hom)).obj
        ((extensionByZero T c₀).obj K) :=
  T.pointFiber.map ((CondensedRing.lowerStar T.coefficients
      (T.datum.geometricFiber (barModel T c₀)).hom).rightDerivedFunctor.map
    ((derivedOpenImmersionLowerShriekId T.coefficients
      (T.datum.geometricFiber (barModel T c₀)).left).inv.app ((extensionByZero T c₀).obj K)))

/-- The primary condition of the shrunk coefficient ring, as used by the recorded operators.
Source: def-trf-coefficient-conventions (blueprint: lem-trf-compactification-graph-operator).

Proof: take the exponent `N` of `T.primary`; transport `ell^N • 1 = 0` along
`Shrink.ringEquiv`, and multiply by `a`. -/
theorem shrinkPrimary :
    ∃ n : ℕ, 0 < n ∧ ∀ a : Shrink.{0} T.A, (T.ell ^ n) • a = 0 := by
  obtain ⟨n, hn, h⟩ := T.primary
  refine ⟨n, hn, fun a ↦ ?_⟩
  have h' : (T.ell ^ n : Shrink.{0} T.A) = 0 := by
    apply (Shrink.ringEquiv.{0} T.A).injective
    simpa only [map_pow, map_natCast, map_zero, nsmul_eq_mul, _root_.mul_one,
      Nat.cast_pow] using h
  rw [nsmul_eq_mul, Nat.cast_pow, h', zero_mul]

end WeilConjectures.CompactificationGraphOperator
