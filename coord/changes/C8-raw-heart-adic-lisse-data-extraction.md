# WeilConjectures.RawHeartAdic data interfaces

## Reason

The main theorem needs three separate, independently provable encoding-transport lemmas.
Those lemmas must mention its existing structures, so keeping the structures in the
assembly module would introduce an import cycle. Extract the existing declarations into
Sheaf.DeligneLaumon.RawHeartAdicLisseData, and publicly reexport them from the original
module. This is an interface extraction for dependency direction, not a timeout workaround.
No definition is repaired or weakened. Every moved signature and body is unchanged,
checked by the repository declaration parser. The original theorem signature is unchanged.
No target statement or definition changes meaning. No data is chosen from an unproved
existence theorem; every new sorry is a named public proposition.

## Old

The following signatures were declared in
lean/Sheaf/DeligneLaumon/RawHeartAdicLisseStratification.lean; their existing definition
bodies and all structure fields are retained verbatim in the new data module.

```lean
abbrev baseSeparated {k : Type u} [Field k] (X : PerAdic.Base k) : X.scheme.IsSeparated

def realBase (X : PerAdic.Base D.k) : LisseRealization.Base D l hl

abbrev baseInvertible (X : PerAdic.Base D.k) (x : X.scheme) : Invertible (l : X.scheme.residueField x)

def systemBase (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : PerAdic.Base D.k) : ProEtale.CompletedLisse.Base.{u} l

def continuousBase (X : PerAdic.Base D.k) : ContinuousRational.Base.{u} l

abbrev baseDimension (X : PerAdic.Base D.k) : Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)

abbrev basePrimeUnit (X : PerAdic.Base D.k) : Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))

structure CoefficientSize (X : PerAdic.Base D.k)

structure CondensedCoefficients (X : PerAdic.Base D.k)

def CondensedCoefficients.rationalChart {X : PerAdic.Base D.k} (d : CondensedCoefficients D l E X)

def CondensedCoefficients.integralChart {X : PerAdic.Base D.k} (d : CondensedCoefficients D l E X)

structure ClassicalAt (a : LisseRealization.Family D l hl) (c : ProEtale.CompletedLisse.System.{u} l) (X : PerAdic.Base D.k)

def systemArrow (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F) {X Y : PerAdic.Base D.k} (f : Y.scheme ⟶ X.scheme) : ProEtale.CompletedLisse.Arrow l (systemBase D l hl E X) (systemBase D l hl F Y)

def identityChartProjection (X : Scheme.{u}) (U : X.ProEt) : (proEtaleBaseChange (𝟙 X)).obj U ⟶ U

structure ClassicalFamily (a : LisseRealization.Family D l hl) (c : ProEtale.CompletedLisse.System.{u} l)

abbrev pullCommon (A : Type u) [Field A] [Algebra ℚ_[l] A] [IsAlgClosure ℚ_[l] A] {X Y : PerAdic.Base D.k} (f : X.scheme ⟶ Y.scheme)

abbrev ClassicalStage (X : PerAdic.Base D.k) (i : AlgebraicallyClosedCoefficients.Index l Ω)

def liftedStage (i : AlgebraicallyClosedCoefficients.Index l Ω) : Padic.FiniteCoefficientFields l (ULift.{u + 1} Ω)

def liftedStageMap (i : AlgebraicallyClosedCoefficients.Index l Ω) : ULift.{u + 1} (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) →ₐ[ℚ_[l]] (liftedStage l Ω i).val

abbrev liftedClosure : IsAlgClosure ℚ_[l] (ULift.{u + 1} Ω)

def algebraicModelFunctor (X : PerAdic.Base D.k) (i : AlgebraicallyClosedCoefficients.Index l Ω) : ClassicalStage D l hl Ω X i ⥤ @LisseAlgebraicSheaf l _ X.scheme _ (baseSeparated X) (baseInvertible D l hl X) (ULift.{u + 1} Ω) _ _

def algebraicModel (X : PerAdic.Base D.k) (i : AlgebraicallyClosedCoefficients.Index l Ω) (F : ClassicalStage D l hl Ω X i)

structure ClassicalCommon (a : LisseRealization.Family D l hl) (c : ProEtale.CompletedLisse.System.{u} l) (b : ClassicalFamily D l hl a c) (X : PerAdic.Base D.k)

structure HeartComparison (a : LisseRealization.Family D l hl) (S : FdCoefficientComparisonSystem.{u} l Ω) (r : ContinuousRational.Family.{u} l) (X : PerAdic.Base D.k) [hDim : Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)] [hInv : Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))]

structure Strata (a : LisseRealization.Family D l hl) (c : ProEtale.CompletedLisse.System.{u} l) (b : ClassicalFamily D l hl a c) (X : PerAdic.Base D.k) (M : sfCommonStageHeart l X.scheme Ω)

def Strata.lattice {a : LisseRealization.Family D l hl} {c : ProEtale.CompletedLisse.System.{u} l} {b : ClassicalFamily D l hl a c} {X : PerAdic.Base D.k} {M : sfCommonStageHeart l X.scheme Ω} (s : Strata D l hl Ω a c b X M) (ν : Fin s.partition.n)

def ClassicalAt.completed {a : LisseRealization.Family D l hl} {c : ProEtale.CompletedLisse.System.{u} l} {X : PerAdic.Base D.k} (d : ClassicalAt D l hl E a c X)

def finiteModel (Y₀ : Over (Spec (.of D.k₀))) (m : ℕ) (hm : 1 ≤ m)

def reducedModel (Y₀ : Over (Spec (.of D.k₀))) (m : ℕ) (hm : 1 ≤ m)

def reductionInclusion (Y₀ : Over (Spec (.of D.k₀))) (m : ℕ) (hm : 1 ≤ m) : reducedModel D Y₀ m hm ⟶ finiteModel D Y₀ m hm

def geometricChange (m : ℕ) (hm : 1 ≤ m)

structure Frontier {a : LisseRealization.Family D l hl} {c : ProEtale.CompletedLisse.System.{u} l} {b : ClassicalFamily D l hl a c} {X : PerAdic.Base D.k} {M : sfCommonStageHeart l X.scheme Ω} (s : Strata D l hl Ω a c b X M) (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] (e : X.scheme ≅ (D.geometricFiber Y₀).left.nilradical.subscheme)

def geometricBase (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] : PerAdic.Base D.k

def restrictedWeil (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] (K : sfCommonStageWeilComplex D l hl Y₀ Ω) (W : PerAdic.Base D.k) (f : W.scheme ⟶ (D.geometricFiber Y₀).left) (g : W.scheme ⟶ W.scheme) (n : ℕ) (h : g ≫ f = f ≫ localPositivePower (D.geometricFrobenius Y₀).hom n) : (pullCommon D l hl Ω (X := W) (Y := W) g).obj ((pullCommon D l hl Ω (X := W) (Y := geometricBase D Y₀) f).obj K.carrier) ≅ (pullCommon D l hl Ω (X := W) (Y := geometricBase D Y₀) f).obj K.carrier

def classicalPullIso {a : LisseRealization.Family D l hl} {c : ProEtale.CompletedLisse.System.{u} l} (b : ClassicalFamily D l hl a c) (i : AlgebraicallyClosedCoefficients.Index l Ω) {X Y : PerAdic.Base D.k} (f : Y.scheme ⟶ X.scheme) (F : ClassicalStage D l hl Ω X i) : (GeneralAlgebraicallyClosedCoefficients.inclusion i).obj ((b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) Y).realization.obj ((c.operation (systemArrow D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) (AlgHom.id _ _) (X := X) (Y := Y) f)).raw.obj F)) ≅ (pullCommon D l hl Ω (X := Y) (Y := X) f).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion i).obj ((b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X).realization.obj F))

structure WeilLift {a : LisseRealization.Family D l hl} {c : ProEtale.CompletedLisse.System.{u} l} {b : ClassicalFamily D l hl a c} {X : PerAdic.Base D.k} {M : sfCommonStageHeart l X.scheme Ω} (s : Strata D l hl Ω a c b X M) (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] (e : X.scheme ≅ (D.geometricFiber Y₀).left) (K : sfCommonStageWeilComplex D l hl Y₀ Ω) (ν : Fin s.partition.n) (m : ℕ) (hm : 1 ≤ m) (V₀ : Over (Spec (.of (D.extensionSubfield m hm)))) (W : PerAdic.Base D.k) (eW : W.scheme ≅ ((geometricChange D m hm).obj V₀).left) (j : W.scheme ⟶ (s.bases ν).scheme)

structure Normalized (a : LisseRealization.Family D l hl) : Prop
```

## New

The same signatures above, with the same bodies and structure fields, are declared in
lean/Sheaf/DeligneLaumon/RawHeartAdicLisseData.lean. The original module publicly imports
that module. The precise new module dependency is:

```lean
public import Sheaf.DeligneLaumon.RawHeartAdicLisseData
```

The three new theorem signatures are reproduced verbatim below; each is a strict part
of the old argument and is left as a named public theorem with its node and proof plan.

```lean
theorem raw_heart_adic_comparison_bridge (a : LisseRealization.Family D l hl) (ha : Normalized D l hl Ω a) (c : ProEtale.CompletedLisse.System.{u} l) (S : FdCoefficientComparisonSystem.{u} l Ω) (hS : FdComparisonSchemeCoherence l Ω S) (r : ContinuousRational.Family.{u} l) : ∃ b : ClassicalFamily D l hl a c, (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A] (Y : PerAdic.Base D.k), Nonempty (CondensedCoefficients D l A Y)) ∧ (∀ Y : PerAdic.Base D.k, Nonempty (HeartComparison D l hl Ω a S r Y (hDim := baseDimension D l hl Y) (hInv := basePrimeUnit D l hl Y))) ∧ (∀ Y : PerAdic.Base D.k, Nonempty (ClassicalCommon D l hl Ω a c b Y))
```

```lean
theorem raw_heart_adic_strata_bridge (a : LisseRealization.Family D l hl) (c : ProEtale.CompletedLisse.System.{u} l) (b : ClassicalFamily D l hl a c) (S : FdCoefficientComparisonSystem.{u} l Ω) (r : ContinuousRational.Family.{u} l) (hheart : ∀ Y : PerAdic.Base D.k, Nonempty (HeartComparison D l hl Ω a S r Y (hDim := baseDimension D l hl Y) (hInv := basePrimeUnit D l hl Y))) (X : PerAdic.Base D.k) (i : AlgebraicallyClosedCoefficients.Index l Ω) (N : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) X.scheme) (F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω i))) (hF : ∃ t : Scheme.FiniteLocallyClosedStratification X.scheme, ∀ j : Fin t.n, ((proEtaleModuleInverseImage (t.immersion j) (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω i))).obj F).IsFiniteLocallyFree) (hreal : letI := baseDimension D l hl X letI := basePrimeUnit D l hl X Nonempty (((r.realization (pbcFiniteField.{u} l Ω i) (continuousBase D l hl X)).J.obj (((S.coefficients X.scheme).stage i).rational.functor.obj N.obj)) ≅ (DerivedCategory.singleFunctor _ 0).obj F)) : ∃ (partition : Scheme.FiniteLocallyClosedStratification X.scheme), (∀ ν : Fin partition.n, IsReduced (partition.domain ν)) ∧ ∃ (bases : Fin partition.n → PerAdic.Base D.k) (domain : ∀ ν : Fin partition.n, (bases ν).scheme = partition.domain ν), (∀ ν : Fin partition.n, eqToHom (domain ν) ≫ partition.immersion ν ≫ (X.scheme ↘ Spec (.of D.k)) = ((bases ν).scheme ↘ Spec (.of D.k))) ∧ ∃ model : ∀ ν : Fin partition.n, ClassicalStage D l hl Ω (bases ν) i, ∀ ν : Fin partition.n, Nonempty ((@rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) _ _ _ _ _ (eqToHom (domain ν) ≫ partition.immersion ν) (baseInvertible D l hl (bases ν)) (baseInvertible D l hl X)).obj N.obj ≅ (b.finite (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) (bases ν)).realization.obj (model ν))
```

```lean
theorem raw_heart_adic_restriction_bridge (a : LisseRealization.Family D l hl) (ha : Normalized D l hl Ω a) (c : ProEtale.CompletedLisse.System.{u} l) (b : ClassicalFamily D l hl a c) (hcommon : (∀ Y : PerAdic.Base D.k, Nonempty (ClassicalCommon D l hl Ω a c b Y))) (X : PerAdic.Base D.k) (M : sfCommonStageHeart l X.scheme Ω) (s : Strata D l hl Ω a c b X M) : (∀ (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] (e : X.scheme ≅ (D.geometricFiber Y₀).left.nilradical.subscheme), Nonempty (Frontier D l hl Ω s Y₀ e)) ∧ (∀ (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom] (e : X.scheme ≅ (D.geometricFiber Y₀).left) (K : sfCommonStageWeilComplex D l hl Y₀ Ω), Nonempty ((pullCommon D l hl Ω (X := X) (Y := geometricBase D Y₀) e.hom).obj K.carrier ≅ M.obj) → ∀ (ν : Fin s.partition.n) (m : ℕ) (hm : 1 ≤ m) (V₀ : Over (Spec (.of (D.extensionSubfield m hm)))) (j₀ : V₀ ⟶ finiteModel D Y₀ m hm), IsImmersion j₀.left → ∀ (W : PerAdic.Base D.k) (eW : W.scheme ≅ ((geometricChange D m hm).obj V₀).left), eW.hom ≫ ((geometricChange D m hm).obj V₀).hom = (W.scheme ↘ Spec (.of D.k)) → ∀ (j : W.scheme ⟶ (s.bases ν).scheme), IsImmersion j → (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom) ≫ pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = eW.hom ≫ pullback.fst V₀.hom (Spec.map (CommRingCat.ofHom (algebraMap (D.extensionSubfield m hm) D.k))) ≫ j₀.left ≫ pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) → (j ≫ eqToHom (s.domain ν) ≫ s.partition.immersion ν ≫ e.hom) ≫ (D.geometricFiber Y₀).hom = (W.scheme ↘ Spec (.of D.k)) → Nonempty (WeilLift D l hl Ω s Y₀ e K ν m hm V₀ W eW j))
```

## Users

`tools/downstream.py Sheaf.DeligneLaumon.RawHeartAdicLisseStratification --uses Strata
ClassicalAt ClassicalFamily ClassicalCommon HeartComparison Normalized` reports zero
existing downstream modules. The DAG parent thm-zl-real-mixed-by-curves and its unit
still require the original theorem; both are preserved. No consumer signature changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | C8 | Same theorem statement; explicit assembly, publicly reexports the unchanged interfaces. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | new in C8 | Owns the identical interface declarations. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | new in C8 | Comparison functor transport only; no object partition. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | new in C8 | Finite partition and classical systems for an already supplied finite heart model and continuous sheaf. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | new in C8 | Weil/frontier extension of a supplied partition. |

## Status

landed 20261025T100843-L-3630032 2026-10-25 (merge of deliver/C8/Sheaf.DeligneLaumon.RawHeartAdicLisseStratification)
