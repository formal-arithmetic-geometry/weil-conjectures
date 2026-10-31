/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.ConstantExtensionPunctualWeights
public import WeilConjectures.AlgebraicGeometry.CondensedConstantExtensionFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleSheetSumCompatibility
import WeilConjectures.AlgebraicGeometry.ConstantExtensionSheetGeometry
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.CategoryTheory.CyclicReturnExactEquivalence
import WeilConjectures.AlgebraicGeometry.CondensedFiniteEtaleStalkCycles
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteEtaleSplitHomDescent
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Constant-extension sheets and trace for condensed Weil sheaves

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraph 5
(blueprint: lem-zl-condensed-constant-extension-trace).

The hearts below specialize the recorded fixed-pair and finite constant local model
constructions. The module functors, their compositors, adjunction and coefficient action
are the published condensed ones. In particular the coefficient is the finite-subextension
valued ring, including when the extension degree is divisible by the coefficient prime.

The existing definitions used in the signature have definition-node owners:
`CondensedWeil.extend` is recorded by def-zl-condensed-weil-constant-extension;
`finiteEtaleSheetSum` by def-zl-finite-etale-sheet-sum; and
`FiniteEtaleModuleChart.Compatible` by def-zl-finite-etale-chart-compatibility.
Their published source modules are imported above without duplicating their definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedConstantExtension

/-- The constructible heart of ordinary condensed Weil pairs, with the constructibility
predicate of coefficientHeart. Source: latest blueprint, paragraph 5 and coefficient-heart
convention (blueprint: lem-zl-condensed-constant-extension-trace). -/
abbrev Heart (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  ObjectProperty.FullSubcategory (fun M : CondensedWeil.WeilModule D l T₀ ↦
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber T₀).left M.carrier)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (m : ℕ) (hm : 1 ≤ m) (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]

/-- The actual geometric projection of the constant extension, over the original field.
Source: latest blueprint, paragraph 5
(blueprint: lem-zl-condensed-constant-extension-trace). -/
abbrev projection := zlFiberMap D (constantExtensionProjection D m hm T₀)

/-- Pullback with the canonical Frobenius square, on ordinary Weil modules.
Source: latest blueprint, paragraph 5, g^*M
(blueprint: lem-zl-condensed-constant-extension-trace). -/
def pull : CondensedWeil.WeilModule D l T₀ ⥤
    CondensedWeil.WeilModule D l (constantExtensionOriginalModel D m hm T₀) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (CommSq.mk (zlFrobenius_naturality D
        (constantExtensionProjection D m hm T₀)))).symm

/-- Underived direct image, with the specified base-change exchange followed by g_*theta.
Source: latest blueprint, paragraph 5, exact finite image
(blueprint: lem-zl-condensed-constant-extension-trace). -/
def push : CondensedWeil.WeilModule D l (constantExtensionOriginalModel D m hm T₀) ⥤
    CondensedWeil.WeilModule D l T₀ :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (asIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
      (CommSq.mk (zlFrobenius_naturality D
        (constantExtensionProjection D m hm T₀)))))

/-- Return to the distinguished sheet: the ordered m-fold Weil iterate, restricted
along the actual sheet inclusion with its canonical pullback-square comparison.
Source: latest blueprint, paragraph 5, cyclic-sheet interpretation
(blueprint: lem-zl-condensed-constant-extension-trace). -/
def returnObj
    (N : CondensedWeil.WeilModule D l (constantExtensionOriginalModel D m hm T₀)) :
    CondensedWeil.WeilModule (constantExtensionDatum D m hm) l
      (constantExtensionModel D m hm T₀) :=
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (CommSq.mk (constantExtensionSheet_return D m hm T₀))).symm).obj
    (CategoryTheory.Endofunctor.IsoAlgebra.mk N.carrier
      (CondensedWeil.iterate (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm T₀)).hom
        N.carrier N.str (m - 1)))

/-- The scalar-fibre identification is the pullback compositor for the geometric point
and the distinguished sheet, followed by actual point sections.
Source: latest blueprint, paragraph 5, preservation of local spectra
(blueprint: lem-zl-condensed-constant-extension-trace). -/
def sheetFibreIso
    (N : CondensedWeil.WeilModule D l (constantExtensionOriginalModel D m hm T₀))
    (z : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm T₀)).left) :=
  (CondensedQbarGeometricEvaluation.fieldFiber D.k l).mapIso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
      z (constantExtensionSheet D m hm T₀)).app N.carrier)

/-- Every clause of constant-extension descent on the actual condensed constructible
Weil hearts. The return functor is fixed on objects and arrows; the comparison of
pullback with m-fold extension has its canonical carrier map. Exactness supplies
quotients, and the displayed order maps supply subobjects and hence finite filtrations.
The trace and its divided retraction are natural transformations in the Weil heart.
The equation m * retraction = trace specifies division by the nonzero rational integer.

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real,
thm-zl-real-mixed-by-curves.proof.md, paragraph 5
(blueprint: lem-zl-condensed-constant-extension-trace).

Proof plan (the ten steps of the node):
1. Use constantExtensionSheetGeometry only for the m clopen sheets and their successor
and return identities. Finite-field separability and etale base change make the projection
finite etale of degree m; on an affine chart a field basis gives its free rank m.
2. Apply internalAbelianSheafModuleEquivalence and clopen_ringed_module_gluing to the
actual pulled-back ring. Restrict finite stratifications to sheets and combine them in
the reverse direction. ProfinitePointPullback supplies coherent coefficient comparisons;
CondensedModulePullbackExact gives exactness, also for semilinear sheet coordinates.
3. The pulled-back Weil isomorphisms give the successive arrows and closing arrow of a
cyclic tuple. cyclicReturnExactEquivalence gives the exact return equivalence, its inverse,
and transport of subobjects, quotients and finite chains.
4. The return of pi^*M is theta followed by its successive Frobenius pullbacks, using
pi j_0 = the canonical fibre identification. Pullback composition gives the specified
comparison with CondensedWeil.extend, on maps as well as objects.
5. For a degree r point over k_m the old operator has mr factors. The new operator has
r blocks of m factors. The ordered products and the point reparametrizations coincide;
composition coherence gives the stated conjugacy. The residue cardinality is q^(mr) in
both interpretations, proving preservation of spectra, weights and mixed filtrations.
6. CondensedFiniteEtaleStalkCycles gives constructibility of ordinary direct image and
its induced Weil structure. SplitProEtaleModuleProductMap identifies it locally with a
finite product of exact sheet pullbacks. A common refinement of the finitely many lifting
covers proves surjectivity; kernels and images are componentwise. Descent gives exactness.
7. In a stalk cycle of length e, an eigenvalue lambda of Frobenius has lambda^e as an
eigenvalue of the return. Purity and q_z = q_y^e give |iota(lambda)| = q_y^(v/2).
A nonzero eigenvector has a nonzero block; no semisimplicity or lissity is needed.
8. finiteEtaleSheetSum_compatible gives overlap agreement of the actual local counit
sums; finiteEtaleSplitHom_descent glues them. Sheaf separatedness gives uniqueness.
Applying a module map to the finite sum proves naturality. Geometric-point splitting
and actual point sections give summation on every fibre.
9. Frobenius permutes the sheets and acts by the same pulled-back Weil map on each;
additivity makes it commute with their sum. The same overlap comparison descends the
Weil square. Each counit projection composed with the adjunction unit is the identity,
so the unit is diagonal and trace after unit is m times the identity as sheaf maps.
10. The constant 1/m is a section already over Q_l. Pointwise multiplication by m gives
one, and pulling back preserves this identity and its Weil compatibility. Multiplying
trace by this scalar gives the specified retraction, even if l divides m. For m=1 there
are no intermediate arrows; zero modules and the empty scheme give zero maps. -/
theorem trace (hl : l ≠ D.p) (iota : PadicAlgCl l ≃+* ℂ) :
    ∃ (E : Heart D l (constantExtensionOriginalModel D m hm T₀) ≌
        Heart (constantExtensionDatum D m hm) l (constantExtensionModel D m hm T₀))
      (P : Heart D l T₀ ⥤ Heart D l (constantExtensionOriginalModel D m hm T₀))
      (Q : Heart D l (constantExtensionOriginalModel D m hm T₀) ⥤ Heart D l T₀),
      (∀ N, (E.functor.obj N).obj = returnObj D l m hm T₀ N.obj) ∧
      (∀ (N N' : Heart D l (constantExtensionOriginalModel D m hm T₀)) (f : N ⟶ N'),
        HEq (E.functor.map f).hom.hom.f
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (constantExtensionSheet D m hm T₀)).map f.hom.hom.f)) ∧
      PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor ∧
      PreservesFiniteLimits E.inverse ∧ PreservesFiniteColimits E.inverse ∧
      (∀ N, ∃ s : Subobject N ≃o Subobject (E.functor.obj N),
        ∀ U, s U = Subobject.mk (E.functor.map U.arrow)) ∧
      (∀ (N : Heart D l (constantExtensionOriginalModel D m hm T₀)) (v : ℝ),
        (CondensedWeil.Pure D l (constantExtensionOriginalModel D m hm T₀)
            N.obj iota.toRingHom v ↔
          CondensedWeil.Pure (constantExtensionDatum D m hm) l
            (constantExtensionModel D m hm T₀) (E.functor.obj N).obj iota.toRingHom v) ∧
        (CondensedWeil.Mixed D l (constantExtensionOriginalModel D m hm T₀)
            N.obj iota.toRingHom v ↔
          CondensedWeil.Mixed (constantExtensionDatum D m hm) l
            (constantExtensionModel D m hm T₀) (E.functor.obj N).obj iota.toRingHom v)) ∧
      (∀ M, (P.obj M).obj = (pull D l m hm T₀).obj M.obj) ∧
      (∀ (M M' : Heart D l T₀) (f : M ⟶ M'),
        HEq (P.map f).hom ((pull D l m hm T₀).map f.hom)) ∧
      (∀ M, ∃ a : (E.functor.obj (P.obj M)).obj ≅
          CondensedWeil.extend D l T₀ m hm M.obj,
        HEq a.hom.hom.f
          ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
            (constantExtensionSheet D m hm T₀) (projection D m hm T₀)).inv.app
              M.obj.carrier)) ∧
      (∀ N, (Q.obj N).obj = (push D l m hm T₀).obj N.obj) ∧
      (∀ (N N' : Heart D l (constantExtensionOriginalModel D m hm T₀)) (f : N ⟶ N'),
        HEq (Q.map f).hom ((push D l m hm T₀).map f.hom)) ∧
      PreservesFiniteLimits Q ∧ PreservesFiniteColimits Q ∧
      (∀ (N : Heart D l (constantExtensionOriginalModel D m hm T₀)) (v : ℝ),
        CondensedWeil.Pure D l (constantExtensionOriginalModel D m hm T₀)
          N.obj iota.toRingHom v →
        CondensedWeil.Pure D l T₀ (Q.obj N).obj iota.toRingHom v) ∧
      (∀ (N : Heart D l (constantExtensionOriginalModel D m hm T₀))
        (z : Spec (.of D.k) ⟶ ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm T₀)).left) (r : ℕ)
        (hN : (z ≫ constantExtensionSheet D m hm T₀) ≫ localPositivePower
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm T₀)).hom
            (m * (r + 1) - 1) =
          localPositivePower (frobeniusPointIso D).hom (m * (r + 1) - 1) ≫
            (z ≫ constantExtensionSheet D m hm T₀))
        (hA : z ≫ localPositivePower
          ((constantExtensionDatum D m hm).geometricFrobenius
            (constantExtensionModel D m hm T₀)).hom r =
          localPositivePower (frobeniusPointIso (constantExtensionDatum D m hm)).hom r ≫ z),
        CondensedWeil.localReturn l D.k
            (D.geometricFrobenius (constantExtensionOriginalModel D m hm T₀)).hom
            (frobeniusPointIso D).hom N.obj.carrier N.obj.str
            (z ≫ constantExtensionSheet D m hm T₀) (m * (r + 1) - 1) hN ≫
          (sheetFibreIso D l m hm T₀ N.obj z).hom =
        (sheetFibreIso D l m hm T₀ N.obj z).hom ≫
          CondensedWeil.localReturn l D.k
            ((constantExtensionDatum D m hm).geometricFrobenius
              (constantExtensionModel D m hm T₀)).hom
            (frobeniusPointIso (constantExtensionDatum D m hm)).hom
            (returnObj D l m hm T₀ N.obj).carrier (returnObj D l m hm T₀ N.obj).str
            z r hA) ∧
      ∃ (η : 𝟭 (Heart D l T₀) ⟶ P ⋙ Q) (τ : P ⋙ Q ⟶ 𝟭 (Heart D l T₀))
        (ρ : P ⋙ Q ⟶ 𝟭 (Heart D l T₀)),
        (∀ M, HEq (η.app M).hom.hom.f
          ((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
            (projection D m hm T₀)).unit.app M.obj.carrier)) ∧
        (∀ (M : Heart D l T₀) (c : CondensedRing.FiniteEtaleModuleChart
          (projection D m hm T₀)),
          HEq ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) c.map).map
            (τ.app M).hom.hom.f)
            (CondensedRing.finiteEtaleSheetSum (Profinite.padicAlgClRingObj l)
              (projection D m hm T₀) M.obj.carrier c)) ∧
        (∀ M : Heart D l T₀,
          CondensedRing.FiniteEtaleModuleChart.Compatible (Profinite.padicAlgClRingObj l)
            ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
              (projection D m hm T₀)).obj
              ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
                (projection D m hm T₀)).obj M.obj.carrier)) M.obj.carrier
            (CondensedRing.finiteEtaleSheetSum (Profinite.padicAlgClRingObj l)
              (projection D m hm T₀) M.obj.carrier)) ∧
        (∀ (M : Heart D l T₀) (z : Spec (.of D.k) ⟶ (D.geometricFiber T₀).left),
          ∃ (t : Fin m → (Spec (.of D.k) ⟶
              (D.geometricFiber (constantExtensionOriginalModel D m hm T₀)).left))
            (w : ∀ j, t j ≫ projection D m hm T₀ = z),
            Nonempty (IsColimit (Cofan.mk (pullback (projection D m hm T₀) z)
              (fun j ↦ pullback.lift (t j) (𝟙 _) (by simpa using w j)))) ∧
            HEq ((CondensedQbarGeometricEvaluation.fieldFiber D.k l).map
                ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map
                  (τ.app M).hom.hom.f))
              ((CondensedQbarGeometricEvaluation.fieldFiber D.k l).map
                (CondensedRing.finiteEtaleTraceSheetSum (Profinite.padicAlgClRingObj l)
                  (projection D m hm T₀) M.obj.carrier z m t w))) ∧
        η ≫ τ = m • 𝟙 (𝟭 (Heart D l T₀)) ∧
        η ≫ ρ = 𝟙 (𝟭 (Heart D l T₀)) ∧ m • ρ = τ := by
  sorry

end WeilConjectures.CondensedConstantExtension
