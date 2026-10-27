/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.SpaceRelativeProjSchemeTests
public import Sheaf.AlgebraicGeometry.RelativeProjTwistsDegreeOpens
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.SchemeProjVeroneseQuotientFunctor

/-! # The normalized graded twisting algebra on space relative Proj

Source: Stacks Project, spaces-divisors.tex, Tags 084D and 085C;
constructions.tex, Tag 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists).

The records expand the conclusion, rather than adding hypotheses. Products are
sectionwise bilinear maps, equivalently maps out of the sheaf tensor product as in
EtaleGradedModuleAlgebra. Their commutativity is ordinary, including negative degrees.
Scheme comparisons retain the actual tensor pullbacks and their affine fraction models.
-/

@[expose] public noncomputable section

-- Avoid serializing large generated lemmas for the dependent output records.
set_option genInjectivity false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The integer graded algebra in the conclusion of 084D. The nonnegative algebra
uses the existing notion; the displayed equation identifies its products with the
integer products. Both total objects are coproducts of module sheaves.
Source: Stacks, 084D (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
structure SpaceProjTwistAlgebra (P : AlgebraicSpace S) where
  E : ℤ → P.Modules
  quasiCoherent : ∀ n, (E n).IsQuasicoherent
  zero : SheafOfModules.unit P.structureSheaf ≅ E 0
  mul (m n : ℤ) (V : P.EtaleSite) :
    (E m).val.obj (op V) →+ (E n).val.obj (op V) →+ (E (m + n)).val.obj (op V)
  smul_left (m n : ℤ) (V : P.EtaleSite) (r : P.structureSheaf.obj.obj (op V))
      (s : (E m).val.obj (op V)) (t : (E n).val.obj (op V)) :
    mul m n V (r • s) t = r • mul m n V s t
  smul_right (m n : ℤ) (V : P.EtaleSite) (r : P.structureSheaf.obj.obj (op V))
      (s : (E m).val.obj (op V)) (t : (E n).val.obj (op V)) :
    mul m n V s (r • t) = r • mul m n V s t
  naturality (m n : ℤ) {V W : P.EtaleSite} (f : V ⟶ W)
      (s : (E m).val.obj (op W)) (t : (E n).val.obj (op W)) :
    (E (m + n)).val.map f.op (mul m n W s t) =
      mul m n V ((E m).val.map f.op s) ((E n).val.map f.op t)
  assoc (l m n : ℤ) (V : P.EtaleSite) (a : (E l).val.obj (op V))
      (b : (E m).val.obj (op V)) (c : (E n).val.obj (op V)) :
    HEq (mul (l + m) n V (mul l m V a b) c)
      (mul l (m + n) V a (mul m n V b c))
  comm (m n : ℤ) (V : P.EtaleSite) (a : (E m).val.obj (op V))
      (b : (E n).val.obj (op V)) : HEq (mul m n V a b) (mul n m V b a)
  one_mul (n : ℤ) (V : P.EtaleSite) (a : (E n).val.obj (op V)) :
    HEq (mul 0 n V (zero.hom.val.app (op V) (1 : P.structureSheaf.obj.obj (op V))) a) a
  mul_one (n : ℤ) (V : P.EtaleSite) (a : (E n).val.obj (op V)) :
    HEq (mul n 0 V a (zero.hom.val.app (op V) (1 : P.structureSheaf.obj.obj (op V)))) a
  nonnegative : EtaleGradedModuleAlgebra (fun n : ℕ ↦ E n)
  nonnegative_mul (m n : ℕ) (V : P.EtaleSite)
      (s : (E m).val.obj (op V)) (t : (E n).val.obj (op V)) :
    HEq (nonnegative.mul m n V s t) (mul m n V s t)
  nonnegative_unit : nonnegative.unit = zero.hom
  integerCoproduct : HasCoproduct E
  nonnegativeCoproduct : HasCoproduct (fun n : ℕ ↦ E n)

/-- An integer graded isomorphism with its complete algebra normalization.
Source: Stacks, 084D, uniqueness (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
structure SpaceProjTwistAlgebra.Iso {P : AlgebraicSpace S}
    (D D' : SpaceProjTwistAlgebra P) where
  degree (n : ℤ) : D.E n ≅ D'.E n
  zero : D.zero.hom ≫ (degree 0).hom = D'.zero.hom
  mul (m n : ℤ) (V : P.EtaleSite)
      (s : (D.E m).val.obj (op V)) (t : (D.E n).val.obj (op V)) :
    (degree (m + n)).hom.val.app (op V) (D.mul m n V s t) =
      D'.mul m n V ((degree m).hom.val.app (op V) s)
        ((degree n).hom.val.app (op V) t)

/-- The scheme-test arrow into the space Proj, using its specified cartesian square.
Source: Stacks, 084B and 084D (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def spaceProjTwistTestMap {C : SpaceProjCoefficients S} {X : AlgebraicSpace S}
    {A : SpaceProjInput X} (R : SpaceProjRealization C A) (W : Over S)
    (g : schemeSpace W ⟶ X) :
    schemeSpace (spaceProjScheme W (C.scheme A W g).affine) ⟶ R.space :=
  ObjectProperty.homMk ⟨R.compare W g⟩

/-- Pulling an integer graded algebra through an actual tensor functor. Its formulas
on local tensors fix the products and the structural unit, without an arbitrary tensor map.
Source: Stacks, 084D and 085C; 03D7
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
structure SpaceProjTwistPullback {P Q : AlgebraicSpace S} (f : Q ⟶ P)
    (D : SpaceProjTwistAlgebra P) where
  algebra : SpaceProjTwistAlgebra Q
  degree (n : ℤ) : (moduleTensorPullback f).obj (D.E n) ≅ algebra.E n
  mul (m n : ℤ) (V : P.EtaleSite) (q : ModuleChart f V)
      (b c : Q.structureSheaf.obj.obj (op q.left))
      (s : (D.E m).val.obj (op V)) (t : (D.E n).val.obj (op V)) :
    (degree (m + n)).hom.val.app (op q.left)
        (moduleTensorSection f (D.E (m + n)) V q (b * c) (D.mul m n V s t)) =
      algebra.mul m n q.left
        ((degree m).hom.val.app (op q.left) (moduleTensorSection f (D.E m) V q b s))
        ((degree n).hom.val.app (op q.left) (moduleTensorSection f (D.E n) V q c t))
  zero (V : P.EtaleSite) (q : ModuleChart f V)
      (b : Q.structureSheaf.obj.obj (op q.left)) (r : P.structureSheaf.obj.obj (op V)) :
    (degree 0).hom.val.app (op q.left)
        (moduleTensorSection f (D.E 0) V q b (D.zero.hom.val.app (op V) r)) =
      algebra.zero.hom.val.app (op q.left) (b * moduleChartScalar f V q r)

/-- The pulled-back homogeneous map, with both compositors and the actual commuting
square inserted. No comparison or map is chosen from a bare existence assertion.
Source: Stacks, 084D, arbitrary scheme test
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def spaceProjTwistTestPsi {C : SpaceProjCoefficients S} {X P Q T : AlgebraicSpace S}
    {A : SpaceProjInput X} (p : P ⟶ X) (r : Q ⟶ P) (g : T ⟶ X) (π : Q ⟶ T)
    (h : π ≫ g = r ≫ p) (D : SpaceProjTwistAlgebra P)
    (ψ : (C.pullback p A).algebra.Hom D.nonnegative)
    (F : SpaceProjTwistPullback r D) (n : ℕ) :
    (moduleTensorPullback π).obj ((moduleTensorPullback g).obj (A.piece n)) ⟶
      F.algebra.E n :=
  (moduleTensorComposition π g).hom.app (A.piece n) ≫
    eqToHom (congrArg (fun f ↦ (moduleTensorPullback f).obj (A.piece n)) h) ≫
    (moduleTensorComposition r p).inv.app (A.piece n) ≫
    (moduleTensorPullback r).map (ψ.degree n) ≫ (F.degree n).hom

/-- Scheme-test data for the twists. The affine identifications are with the existing
locally-fraction sheaves Proj.twist, not with arbitrary modules.
Source: Stacks, 084D; Constructions, 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
structure SpaceProjTwistTests {C : SpaceProjCoefficients S} {X : AlgebraicSpace S}
    {A : SpaceProjInput X} (R : SpaceProjRealization C A) (D : SpaceProjTwistAlgebra R.space)
    (ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative) where
  test (W : Over S) (g : schemeSpace W ⟶ X) :
    SpaceProjTwistPullback (spaceProjTwistTestMap R W g) D
  square (W : Over S) (g : schemeSpace W ⟶ X) :
    evaluationSchemeMap (spaceProjSchemeProjection W (C.scheme A W g).affine) ≫ g =
      spaceProjTwistTestMap R W g ≫ R.projection
  chart (W : Over S) (g : schemeSpace W ⟶ X) (V : W.left.affineOpens) (n : ℤ) :
    (((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
      ((test W g).algebra.E n)).restrict ((C.scheme A W g).affine.relProjι V)) ≅
      Proj.twist ((C.scheme A W g).affine.grading V) n

/-- Sections of the scheme-test family in its affine Proj chart.
Source: Stacks, 084D and 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.chartSection {C : SpaceProjCoefficients S} {X : AlgebraicSpace S}
    {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) (W : Over S) (g : schemeSpace W ⟶ X)
    (V : W.left.affineOpens) (n : ℤ) (U : (C.scheme A W g).affine.relProj.Opens)
    (s : Γ((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
      ((T.test W g).algebra.E n), U)) :
    Γ(Proj.twist ((C.scheme A W g).affine.grading V) n,
      (C.scheme A W g).affine.relProjι V ⁻¹ᵁ U) :=
  (T.chart W g V n).hom.app _
    (((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
      ((T.test W g).algebra.E n)).presheaf.map
        (homOfLE (((C.scheme A W g).affine.relProjι V).image_preimage_le U)).op s)

/-- The actual coefficient-induced tensor comparison between two scheme tests.
The isomorphism is defined from their comparisons to the same global family; the
cartesian-test naturality identifies its target. It is not a freely chosen base-change map.
Source: Stacks, 084D and 085C
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.baseChange {C : SpaceProjCoefficients S} {X : AlgebraicSpace S}
    {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) {U W : Over S} (a : U ⟶ W)
    (g : schemeSpace W ⟶ X) (n : ℤ) :
    (moduleTensorPullback (evaluationSchemeMap
      (spaceProjSchemeBaseChange a (C.schemeBaseChange A a g)))).obj
        ((T.test W g).algebra.E n) ≅
      (T.test U (evaluationSchemeMap a ≫ g)).algebra.E n :=
  (moduleTensorPullback _).mapIso ((T.test W g).degree n).symm ≪≫
    (moduleTensorComposition _ _).app (D.E n) ≪≫
    eqToIso (congrArg (fun f ↦ (moduleTensorPullback f).obj (D.E n))
      (by
        apply ObjectProperty.hom_ext
        apply Sheaf.hom_ext
        exact R.naturality a g)) ≪≫
    (T.test U (evaluationSchemeMap a ≫ g)).degree n

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Evaluate a morphism from tensor pullback on the actual open-chart tensor 1 tensor s.
This keeps the Zariski comparison on the given scheme opens.
Source: Stacks, 03D7 and 084D (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def spaceProjTwistPullSection {U W : Over S} (a : U ⟶ W)
    (M : (schemeSpace W).Modules) (N : (schemeSpace U).Modules)
    (e : (moduleTensorPullback (evaluationSchemeMap a)).obj M ⟶ N)
    (V : W.left.Opens) (s : Γ((evaluationZariskiRestriction W).obj M, V)) :
    Γ((evaluationZariskiRestriction U).obj N, a.left ⁻¹ᵁ V) :=
  e.val.app (op (evaluationOpenChart a V).left)
    (moduleTensorSection (evaluationSchemeMap a) M (spaceProjOpenChart W V)
      (evaluationOpenChart a V) 1 s)

/-- The section a/1 before passing to an affine Proj chart. The coefficient a is
identified with the actual pulled-back algebra section by SpaceProjCoefficients.sections.
Source: Stacks, 084D and 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.homogeneousSection {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) (W : Over S) (g : schemeSpace W ⟶ X)
    (V : W.left.affineOpens) (n : ℕ) (a : (C.scheme A W g).affine.grading V n) :
    Γ((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
      ((T.test W g).algebra.E n), (C.scheme A W g).affine.relProjHom ⁻¹ᵁ V.1) :=
  spaceProjTwistPullSection
    (spaceProjSchemeProjection W (C.scheme A W g).affine)
    ((moduleTensorPullback g).obj (A.piece n)) ((T.test W g).algebra.E n)
    (spaceProjTwistTestPsi R.projection (spaceProjTwistTestMap R W g) g
      (evaluationSchemeMap (spaceProjSchemeProjection W (C.scheme A W g).affine))
      (T.square W g) D ψ (T.test W g) n) V.1 ((C.scheme A W g).sections V n a)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The unit normalization of the scheme-test comparisons.
Source: Stacks, 084D, 085C and 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.unitNormalized {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) : Prop :=
  ∀ (W : Over S) (g : schemeSpace W ⟶ X) (V : W.left.affineOpens)
      (U : (C.scheme A W g).affine.relProj.Opens)
      (x : (C.scheme A W g).affine.relProjι V ⁻¹ᵁ U),
   ((T.chartSection W g V 0 U
      ((T.test W g).algebra.zero.hom.val.app
        (op (spaceProjOpenChart (spaceProjScheme W (C.scheme A W g).affine) U))
        (1 : (schemeSpace (spaceProjScheme W (C.scheme A W g).affine)).structureSheaf.obj.obj
          (op (spaceProjOpenChart (spaceProjScheme W (C.scheme A W g).affine) U))))).val x).val = 1

/-- The mul normalization of the scheme-test comparisons.
Source: Stacks, 084D, 085C and 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.mulNormalized {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) : Prop :=
  ∀ (W : Over S) (g : schemeSpace W ⟶ X) (V : W.left.affineOpens) (m n : ℤ)
      (U : (C.scheme A W g).affine.relProj.Opens)
      (s : Γ((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
        ((T.test W g).algebra.E m), U))
      (t : Γ((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
        ((T.test W g).algebra.E n), U))
      (x : (C.scheme A W g).affine.relProjι V ⁻¹ᵁ U),
   ((T.chartSection W g V (m + n) U
      ((T.test W g).algebra.mul m n
        (spaceProjOpenChart (spaceProjScheme W (C.scheme A W g).affine) U) s t)).val x).val =
      ((T.chartSection W g V m U s).val x).val *
        ((T.chartSection W g V n U t).val x).val

/-- The homogeneous normalization of the scheme-test comparisons.
Source: Stacks, 084D, 085C and 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.homogeneousNormalized {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) : Prop :=
  ∀ (W : Over S) (g : schemeSpace W ⟶ X) (V : W.left.affineOpens)
      (n : ℕ) (a : (C.scheme A W g).affine.grading V n),
   HEq (T.chartSection W g V n ((C.scheme A W g).affine.relProjHom ⁻¹ᵁ V.1)
      (T.homogeneousSection W g V n a))
      ((Proj.unitToTwist (A := (C.scheme A W g).affine.obj V)
        (𝒜 := (C.scheme A W g).affine.grading V) (d := n) (f := a.val)
        a.property).app ⊤ (Scheme.Modules.unitSectionsEquiv ⊤ 1))

/-- The ordinary coefficient localization homomorphism on homogeneous prime charts.
Source: Stacks, 01MZ, 01O3 and 084D
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def spaceProjTwistLocalizationMap {B F σ τ : Type u} [CommRing B] [CommRing F]
    [SetLike σ B] [AddSubgroupClass σ B] [SetLike τ F] [AddSubgroupClass τ F]
    (𝒝 : ℕ → σ) [GradedRing 𝒝] (𝓕 : ℕ → τ) [GradedRing 𝓕]
    (f : B →+* F) (x : ProjectiveSpectrum 𝓕) (y : ProjectiveSpectrum 𝒝)
    (h : y.asHomogeneousIdeal.toIdeal = x.asHomogeneousIdeal.toIdeal.comap f) :
    Localization.AtPrime y.asHomogeneousIdeal.toIdeal →+*
      Localization.AtPrime x.asHomogeneousIdeal.toIdeal :=
  @Localization.localRingHom B _ F _ y.asHomogeneousIdeal.toIdeal y.isPrime
    x.asHomogeneousIdeal.toIdeal x.isPrime f h

/-- The restriction normalization of the scheme-test comparisons.
Source: Stacks, 084D, 085C and 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.restrictionNormalized {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) : Prop :=
  ∀ (W : Over S) (g : schemeSpace W ⟶ X) (V V' : W.left.affineOpens)
      (h : V' ≤ V) (n : ℤ) (U : (C.scheme A W g).affine.relProj.Opens)
      (s : Γ((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
        ((T.test W g).algebra.E n), U))
      (x : (C.scheme A W g).affine.relProjι V' ⁻¹ᵁ U)
      (y : (C.scheme A W g).affine.relProjι V ⁻¹ᵁ U)
      (hy : y.val.asHomogeneousIdeal.toIdeal =
        x.val.asHomogeneousIdeal.toIdeal.comap ((C.scheme A W g).affine.res h).toRingHom),
   ((T.chartSection W g V' n U s).val x).val =
      spaceProjTwistLocalizationMap ((C.scheme A W g).affine.grading V)
        ((C.scheme A W g).affine.grading V') ((C.scheme A W g).affine.res h).toRingHom
        x.val y.val
        hy ((T.chartSection W g V n U s).val y).val

/-- Pull a scheme-test section through the specified tensor comparison.
Source: Stacks, 084D and 085C (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.baseChangeSection {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) {W' W : Over S} (a : W' ⟶ W)
    (g : schemeSpace W ⟶ X) (n : ℤ)
    (U : (C.scheme A W g).affine.relProj.Opens)
    (s : Γ((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
      ((T.test W g).algebra.E n), U)) :
    Γ((evaluationZariskiRestriction
      (spaceProjScheme W' (C.scheme A W' (evaluationSchemeMap a ≫ g)).affine)).obj
      ((T.test W' (evaluationSchemeMap a ≫ g)).algebra.E n),
      (spaceProjSchemeBaseChange a (C.schemeBaseChange A a g)).left ⁻¹ᵁ U) :=
  spaceProjTwistPullSection (spaceProjSchemeBaseChange a (C.schemeBaseChange A a g))
    ((T.test W g).algebra.E n) ((T.test W' (evaluationSchemeMap a ≫ g)).algebra.E n)
    (T.baseChange a g n).hom U s


/-- The baseChange normalization of the scheme-test comparisons.
Source: Stacks, 084D, 085C and 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.baseChangeNormalized {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) : Prop :=
  ∀ {W' W : Over S} (a : W' ⟶ W) (g : schemeSpace W ⟶ X)
      (V : W.left.affineOpens) (V' : W'.left.affineOpens)
      (h : V'.1 ≤ a.left ⁻¹ᵁ V.1) (n : ℤ)
      (U : (C.scheme A W g).affine.relProj.Opens)
      (s : Γ((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).obj
        ((T.test W g).algebra.E n), U))
      (x : (C.scheme A W' (evaluationSchemeMap a ≫ g)).affine.relProjι V' ⁻¹ᵁ
        (spaceProjSchemeBaseChange a (C.schemeBaseChange A a g)).left ⁻¹ᵁ U)
      (y : (C.scheme A W g).affine.relProjι V ⁻¹ᵁ U)
      (hy : y.val.asHomogeneousIdeal.toIdeal =
        x.val.asHomogeneousIdeal.toIdeal.comap ((C.schemeBaseChange A a g).map h).toRingHom),
   ((T.chartSection W' (evaluationSchemeMap a ≫ g) V' n
      ((spaceProjSchemeBaseChange a (C.schemeBaseChange A a g)).left ⁻¹ᵁ U)
      (T.baseChangeSection a g n U s)).val x).val =
      spaceProjTwistLocalizationMap ((C.scheme A W g).affine.grading V)
        ((C.scheme A W' (evaluationSchemeMap a ≫ g)).affine.grading V')
        ((C.schemeBaseChange A a g).map h).toRingHom x.val y.val
        hy ((T.chartSection W g V n U s).val y).val

/-- The complete normalization on schemes and further base changes. Fraction maps
use coefficient localization; hence identity and successive composition use the same
identity and composite ring maps.
Source: Stacks, 084D and 085C (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.Normalized {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) : Prop :=
  T.unitNormalized ∧ T.mulNormalized ∧ T.homogeneousNormalized ∧
    T.restrictionNormalized ∧ T.baseChangeNormalized


/-- Restrict ordinary scheme modules to one of the affine-base Proj charts.
Source: Stacks, 01NR and 084D (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
abbrev spaceProjTwistChartRestriction {W : Scheme.{u}} (B : W.GradedAlgebraData)
    (V : W.affineOpens) : B.relProj.Modules ⥤ (Proj (B.grading V)).Modules :=
  Scheme.Modules.restrictFunctor (B.relProjι V)

/-- The actual pullback, Zariski restriction and affine Proj chart functor.
Source: Stacks, 084D (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
abbrev spaceProjTwistChartFunctor {C : SpaceProjCoefficients S} {X : AlgebraicSpace S}
    {A : SpaceProjInput X} (R : SpaceProjRealization C A) (W : Over S)
    (g : schemeSpace W ⟶ X) (V : W.left.affineOpens) :
    R.space.Modules ⥤ (Proj ((C.scheme A W g).affine.grading V)).Modules :=
  moduleTensorPullback (spaceProjTwistTestMap R W g) ⋙
    evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine) ⋙
      spaceProjTwistChartRestriction (C.scheme A W g).affine V

/-- The complete comparison from the space family to an ordinary affine twist.
Source: Stacks, 084D and 01NR (blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.chartComparison {C : SpaceProjCoefficients S}
    {X : AlgebraicSpace S} {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    (T : SpaceProjTwistTests R D ψ) (W : Over S) (g : schemeSpace W ⟶ X)
    (V : W.left.affineOpens) (n : ℤ) :
    (spaceProjTwistChartFunctor R W g V).obj (D.E n) ≅
      Proj.twist ((C.scheme A W g).affine.grading V) n :=
  (spaceProjTwistChartRestriction (C.scheme A W g).affine V).mapIso
    ((evaluationZariskiRestriction (spaceProjScheme W (C.scheme A W g).affine)).mapIso
      ((T.test W g).degree n)) ≪≫ T.chart W g V n

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- An isomorphism preserves the canonical graded map and every scheme-test comparison.
The chart equations are equations between actual module morphisms; affine charts cover
the test Proj, so they assert preservation of the whole scheme comparison.
Source: Stacks, 084D, uniqueness
(blueprint: lem-sfb-space-relative-proj-graded-twists). -/
def SpaceProjTwistTests.Respects {C : SpaceProjCoefficients S} {X : AlgebraicSpace S}
    {A : SpaceProjInput X} {R : SpaceProjRealization C A}
    {D D' : SpaceProjTwistAlgebra R.space}
    {ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative}
    {ψ' : (C.pullback R.projection A).algebra.Hom D'.nonnegative}
    (T : SpaceProjTwistTests R D ψ) (T' : SpaceProjTwistTests R D' ψ')
    (e : D.Iso D') : Prop :=
  (∀ n : ℕ, ψ.degree n ≫ (e.degree n).hom = ψ'.degree n) ∧
    ∀ (W : Over S) (g : schemeSpace W ⟶ X) (V : W.left.affineOpens) (n : ℤ),
      (spaceProjTwistChartFunctor R W g V).map (e.degree n).hom ≫
        (T'.chartComparison W g V n).hom = (T.chartComparison W g V n).hom


/-- The canonical graded twisting family on relative Proj of an algebraic space,
with arbitrary scheme-test comparisons, fraction normalization and unique normalized
isomorphism. C and R are precisely the normalized realization of the relative Proj
supplied by lem-sfb-space-relative-proj-scheme-tests, not further geometric assumptions.

Source: Stacks Project, spaces-divisors.tex, Tags 084D and 085C;
constructions.tex, Tag 01NR
(blueprint: lem-sfb-space-relative-proj-graded-twists).

Proof:
1. Tensor pullback preserves quasi-coherence, by
   lem-sfb-space-module-pullback-quasicoherent. Use the equivalence of Zariski and
   etale quasi-coherent modules, lem-trf-scheme-zariski-etale-quasi-coherent-equivalence,
   and the tensor comparison lem-weil-pbc-ringed-topoi-module-pullback-tensor to pass
   the algebra operations between the two sites. The adjunction in
   def-trf-space-etale-module-functors preserves the small coproducts, by
   lem-weil-pbc-left-adjoint-preserves-colimits. The compositor in
   def-sfb-space-module-tensor-composition sends c tensor (d tensor m) to cd tensor m;
   its associativity is the associativity of multiplication in the final structure ring.
2. On schemes take the twists of lem-sfb-relative-proj-twists-degree-opens. On affine
   base charts, lem-weil-pbc-module-pullback-affine-sections identifies the pulled-back
   graded algebra with scalar extension in every degree. The cartesian Proj map is
   lem-nagata-affine-proj-scalar-extension. The formula in
   lem-sfb-proj-scalar-extension-twist-comparison sends (a/f^r) tensor c to
   c*psi(a)/psi(f)^r. It preserves products, the unit and a/1. By
   lem-sfb-scheme-proj-veronese-quotient-functor this is the same underlying map as
   the scheme-test comparison, since it preserves the universal degree-d datum.
3. These maps glue by the restriction compatibility of the affine fraction formulas;
   refine nonaffine intersections by affine opens. Their identity and composition
   equations are the identity and composition equations of coefficient ring maps,
   under moduleTensorComposition. Hence all scheme comparisons have their cocycles.
4. Choose an etale surjective scheme atlas U of X. Its double and triple overlaps
   are schemes by def-trf-algebraic-space. The corresponding relative Projs are the
   scheme tests of lem-sfb-space-relative-proj-scheme-tests. By
   lem-trf-space-fibre-products-etale-covers and lem-sfb-space-fppf-covering-calculus,
   their atlas is an fppf covering, without requiring quasi-compactness. The two
   scheme comparisons give descent data for every integer twist; step 3 is the cocycle.
5. Apply lem-sfb-space-fppf-qcoh-descent in each degree. Normalize degree zero by
   the descended structure-module isomorphism. Tensor products remain quasi-coherent
   by the scheme etale equivalence, the tensor-pullback comparison and
   lem-weil-pbc-quasi-coherent-tensor-product-affine-sections, checked on scheme charts.
6. The scheme products and homogeneous maps are morphisms of descent data. Full
   faithfulness descends them uniquely, and faithfulness gives the algebra laws and
   compatibility of the graded map. The total objects are sheaf coproducts, as in
   def-trf-etale-graded-module-algebra, not sums of global sections.
7. For any scheme W over X pull back the atlas to W. On its relative Proj the scheme
   comparisons identify the descended twists with the ordinary scheme twists. Their
   equality on double overlaps follows from step 3; full faithfulness descends these
   comparisons and their inverses to W. Products and the homogeneous map agree there
   because they agree after this fppf cover.
8. On further scheme base change both comparisons become the same coefficientwise
   fraction map after the atlas cover, so faithfulness gives the baseChangeNormalized
   formula. For identity and successive composition these formulas are respectively
   the identity and composite ring maps, with moduleTensorComposition inserted as
   in baseChange. Two normalized families agree on the atlas, uniquely; full
   faithfulness descends this unique graded isomorphism, preserving every scheme test.
9. On Spec R, SpaceProjSchemeAlgebra.sections identifies the graded ring with the
   homogeneous affine sections. The existing Proj.twist is the locally-fraction
   sheaf of (C_f)_n on D_+(f), by def-weil-pbc-proj-twisting-sheaf. The chart unit is 1,
   products multiply fractions, and unitToTwist sends a to a/1. These are exactly the
   unitNormalized, mulNormalized and homogeneousNormalized clauses, for all integer
   degrees. No generation, flatness, separation or quasi-compactness condition is used. -/
theorem exists_space_relativeProj_graded_twists (C : SpaceProjCoefficients S)
    {X : AlgebraicSpace S} (A : SpaceProjInput X) (R : SpaceProjRealization C A) :
    ∃ (D : SpaceProjTwistAlgebra R.space)
      (ψ : (C.pullback R.projection A).algebra.Hom D.nonnegative)
      (T : SpaceProjTwistTests R D ψ), T.Normalized ∧
        ∀ (D' : SpaceProjTwistAlgebra R.space)
          (ψ' : (C.pullback R.projection A).algebra.Hom D'.nonnegative)
          (T' : SpaceProjTwistTests R D' ψ'), T'.Normalized →
            ∃! e : D.Iso D', T.Respects T' e := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
