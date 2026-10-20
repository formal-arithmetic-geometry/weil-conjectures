/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Algebra.Homology.SignedDoubleHomCone
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Sheaf.Paper.FieldShriekCompositionQcqs

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
import Sheaf.Paper.FiniteCoefficientAdjointComparisons
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
/-! # Verdier-duality exchange

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-verdier-exchange,
order 2503 (blueprint: sk-thm-sf-verdier-exchange).

The exceptional functors below are the existing constructible adjoints. In particular
none of these definitions uses an ambient exceptional-adjoint datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u a b c d e v w z
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme


namespace WeilConjectures
namespace VerdierExchange
open CategoryTheory.Pretriangulated.Opposite

/-- Conjugate the inverse compact-support compositor under the constructible adjunctions.
The orientation is G_f G_a to G_x. Evaluating at the coefficient unit gives c_Lambda.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 2
(blueprint: sk-thm-sf-verdier-exchange). -/
def composition
    {X : Type a} {Y : Type b} {S : Type c}
    [Category.{v} X] [Category.{w} Y] [Category.{z} S]
    {Ff : X ⥤ Y} {Gf : Y ⥤ X} {Fa : Y ⥤ S} {Ga : S ⥤ Y}
    {Fx : X ⥤ S} {Gx : S ⥤ X}
    (adjf : Ff ⊣ Gf) (adja : Fa ⊣ Ga) (adjx : Fx ⊣ Gx)
    (alpha : Ff ⋙ Fa ≅ Fx) : Ga ⋙ Gf ≅ Gx :=
  conjugateIsoEquiv (adjf.comp adja) adjx alpha.symm

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The original site is essentially small in its object universe.
Source: the project's small-site convention (blueprint: sk-thm-sf-verdier-exchange). -/
local instance smallSite (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt

open ConstructibleExceptionalCoefficients

/-- The existing ambient ring-stage internal Hom on the original small pro-etale site.
The finite and integral cases use precisely the coefficient sheaves of RingStage.
Source: blueprint sk-def-sf-operations (i), specialized to the displayed duals
(blueprint: sk-thm-sf-verdier-exchange). -/
abbrev ringHom (T : Scheme.{u}) (s : RingStage.{u} l) :=
  derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology T) ((s.coefficients l).ring T)

/-- The coefficient sheaf itself in degree zero, rather than an unspecified unit object.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 1
(blueprint: sk-thm-sf-verdier-exchange). -/
def ringUnit (T : Scheme.{u}) (s : RingStage.{u} l) :
    DerivedCategory (pbcModules T ((s.coefficients l).ring T)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((s.coefficients l).ring T)))

/-- Internal Hom into the specified dualizing object, restricted in its first variable
by the existing full finite-Tor inclusion. The target remains the ambient derived category.
Source: blueprint sk-thm-sf-verdier-exchange, definition of D_T
(blueprint: sk-thm-sf-verdier-exchange). -/
def ringDual (T : Scheme.{u}) (s : RingStage.{u} l)
    (omega : C l Ω T (s.stage l)) :
    (C l Ω T (s.stage l))ᵒᵖ ⥤
      DerivedCategory (pbcModules T ((s.coefficients l).ring T)) :=
  (s.inclusion l Ω T).op ⋙
    (Functor.curry.obj (ringHom l T s)).flip.obj ((s.inclusion l Ω T).obj omega)

/-- Substitution of the dualizing-object comparison in the second variable of RHom.
This is the second arrow in the required exchange; it acts on the actual internal Hom.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 3
(blueprint: sk-thm-sf-verdier-exchange). -/
def substitute {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (omega omega' : C l Ω X (s.stage l)) (c : omega ≅ omega') :
    ringDual l Ω X s omega ⋙ PurCompactSupport.push (s.coefficients l) f ≅
      ringDual l Ω X s omega' ⋙ PurCompactSupport.push (s.coefficients l) f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (s.inclusion l Ω X).op
      ((Functor.curry.obj (ringHom l X s)).flip.mapIso
        ((s.inclusion l Ω X).mapIso c)))
    (PurCompactSupport.push (s.coefficients l) f)

/-- The required orientation of Verdier exchange: invert tensor-Hom exchange, then
apply Rf_* RHom(M,-) to c_Lambda. No objectwise isomorphism is selected.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 3
(blueprint: sk-thm-sf-verdier-exchange). -/
def exchange {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (F : C l Ω X (s.stage l) ⥤ C l Ω Y (s.stage l))
    (G : C l Ω Y (s.stage l) ⥤ C l Ω X (s.stage l))
    (omegaY : C l Ω Y (s.stage l)) (omegaX : C l Ω X (s.stage l))
    (theta : ringDual l Ω X s (G.obj omegaY) ⋙
        PurCompactSupport.push (s.coefficients l) f ≅
      F.op ⋙ ringDual l Ω Y s omegaY)
    (c : G.obj omegaY ≅ omegaX) :
    F.op ⋙ ringDual l Ω Y s omegaY ≅
      ringDual l Ω X s omegaX ⋙ PurCompactSupport.push (s.coefficients l) f :=
  theta.symm ≪≫ substitute l Ω f s (G.obj omegaY) omegaX c

/-- Closed tensor--Hom data on the existing constructible category, together with
ordinary pullback/direct-image adjunction data. The compact-support adjunction is the
recorded Operation, not an ambient exceptional adjoint. All fields are output data in
the final assertion. Source: blueprint operations (i), (ii), (vi), exchange proof step 3
(blueprint: sk-thm-sf-verdier-exchange). -/
structure StageData {X Y S : Scheme.{u}} (s : Stage.{u} l)
    (F : Operation l Ω X Y s) (A : Operation l Ω Y S s)
    (B : Operation l Ω X S s) (unit : C l Ω S s) where
  homX : (C l Ω X s)ᵒᵖ × C l Ω X s ⥤ C l Ω X s
  homY : (C l Ω Y s)ᵒᵖ × C l Ω Y s ⥤ C l Ω Y s
  closedX : CoefficientClosedStructure homX
  closedY : CoefficientClosedStructure homY
  pull : C l Ω Y s ⥤ C l Ω X s
  star : C l Ω X s ⥤ C l Ω Y s
  adjunction : pull ⊣ star
  projection (K : C l Ω Y s) (M : C l Ω X s) :
    F.F.obj (closedX.tensor.obj (pull.obj K, M)) ≅
      closedY.tensor.obj (K, F.F.obj M)
  dualizing : F.G.obj (A.G.obj unit) ≅ B.G.obj unit

/-- Internal Hom into the exceptional inverse image of the coefficient unit.
Source: blueprint definition of D_T (blueprint: sk-thm-sf-verdier-exchange). -/
def StageData.dualX {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation l Ω X Y s} {A : Operation l Ω Y S s}
    {B : Operation l Ω X S s} {unit : C l Ω S s}
    (d : StageData l Ω s F A B unit) : (C l Ω X s)ᵒᵖ ⥤ C l Ω X s :=
  (Functor.curry.obj d.homX).flip.obj (B.G.obj unit)

/-- Internal Hom into omega_Y, with its actual contravariant arrow action.
Source: blueprint definition of D_T (blueprint: sk-thm-sf-verdier-exchange). -/
def StageData.dualY {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation l Ω X Y s} {A : Operation l Ω Y S s}
    {B : Operation l Ω X S s} {unit : C l Ω S s}
    (d : StageData l Ω s F A B unit) : (C l Ω Y s)ᵒᵖ ⥤ C l Ω Y s :=
  (Functor.curry.obj d.homY).flip.obj (A.G.obj unit)

/-- The canonical exchange arrow, without selecting any isomorphism. First use the
projection isomorphism and evaluation, then the constructible exceptional adjunction,
postcomposition by c, tensor--Hom transposition, and the ordinary pull/star adjunction.
This is the inverse tensor--Hom exchange followed by Rf_* RHom(M,c) from step 3.
Source: blueprint exchange proof steps 2--3
(blueprint: sk-thm-sf-verdier-exchange). -/
def StageData.epsilon {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation l Ω X Y s} {A : Operation l Ω Y S s}
    {B : Operation l Ω X S s} {unit : C l Ω S s}
    (d : StageData l Ω s F A B unit) (M : C l Ω X s) :
    (d.dualY l Ω).obj (op (F.F.obj M)) ⟶
      d.star.obj ((d.dualX l Ω).obj (op M)) :=
  d.adjunction.homEquiv _ _
    (d.closedX.transpose _ M (B.G.obj unit)
      (F.adjunction.homEquiv _ _
        ((d.projection ((d.dualY l Ω).obj (op (F.F.obj M))) M).hom ≫
          d.closedY.evaluation (F.F.obj M) (A.G.obj unit)) ≫ d.dualizing.hom))

/-- Realization of the stage data in the original ambient pro-etale derived categories.
The closed models retain signed K-flat evaluation, and pull/star is the ordinary
ringed-topos adjunction. Thus this is a realization of the specified operations, not a
new six-functor formalism. Source: blueprint setting, operations, and exchange step 3
(blueprint: sk-thm-sf-verdier-exchange). -/
structure RingRealization {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (s : RingStage.{u} l)
    {F : Operation l Ω X Y (s.stage l)} {A : Operation l Ω Y S (s.stage l)}
    {B : Operation l Ω X S (s.stage l)} {unit : C l Ω S (s.stage l)}
    (d : StageData l Ω (s.stage l) F A B unit) where
  unitIso : (s.inclusion l Ω S).obj unit ≅ ringUnit l S s
  modelX : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology X) ((s.coefficients l).ring X)
  modelY : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology Y) ((s.coefficients l).ring Y)
  homX : d.homX ⋙ s.inclusion l Ω X ≅
    ((s.inclusion l Ω X).op.prod (s.inclusion l Ω X)) ⋙ ringHom l X s
  homY : d.homY ⋙ s.inclusion l Ω Y ≅
    ((s.inclusion l Ω Y).op.prod (s.inclusion l Ω Y)) ⋙ ringHom l Y s
  tensorX : d.closedX.tensor ⋙ s.inclusion l Ω X ≅
    ((s.inclusion l Ω X).prod (s.inclusion l Ω X)) ⋙ modelX.closed.tensor
  tensorY : d.closedY.tensor ⋙ s.inclusion l Ω Y ≅
    ((s.inclusion l Ω Y).prod (s.inclusion l Ω Y)) ⋙ modelY.closed.tensor
  evaluationX (M N : C l Ω X (s.stage l)) :
    (s.inclusion l Ω X).map (d.closedX.evaluation M N) =
      tensorX.hom.app (d.homX.obj (op M, N), M) ≫
        modelX.closed.tensor.map (Prod.mkHom (homX.hom.app (op M, N)) (𝟙 _)) ≫
        modelX.closed.evaluation ((s.inclusion l Ω X).obj M) ((s.inclusion l Ω X).obj N)
  evaluationY (M N : C l Ω Y (s.stage l)) :
    (s.inclusion l Ω Y).map (d.closedY.evaluation M N) =
      tensorY.hom.app (d.homY.obj (op M, N), M) ≫
        modelY.closed.tensor.map (Prod.mkHom (homY.hom.app (op M, N)) (𝟙 _)) ≫
        modelY.closed.evaluation ((s.inclusion l Ω Y).obj M) ((s.inclusion l Ω Y).obj N)
  pull : d.pull ⋙ s.inclusion l Ω X ≅
    s.inclusion l Ω Y ⋙ PurCompactSupport.pull (s.coefficients l) f
  star : d.star ⋙ s.inclusion l Ω Y ≅
    s.inclusion l Ω X ⋙ PurCompactSupport.push (s.coefficients l) f
  adjunction (K : C l Ω Y (s.stage l)) (M : C l Ω X (s.stage l))
      (a : d.pull.obj K ⟶ M) :
    (s.inclusion l Ω Y).map (d.adjunction.homEquiv K M a) ≫ star.hom.app M =
      (proEtaleRingDerivedAdjunction f ((s.coefficients l).ring Y)
        ((s.coefficients l).ring X) ((s.coefficients l).pull f)).homEquiv _ _
          (pull.inv.app K ≫ (s.inclusion l Ω X).map a)

/-- The natural exchange is required to have the already defined canonical components.
Its shift structure is on opposite categories: shifting M by r shifts D(M) by -r.
Source: blueprint exchange, naturality and shift sentence
(blueprint: sk-thm-sf-verdier-exchange). -/
structure StageConclusion {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation l Ω X Y s} {A : Operation l Ω Y S s}
    {B : Operation l Ω X S s} {unit : C l Ω S s}
    (d : StageData l Ω s F A B unit) where
  epsilon : F.F.op ⋙ d.dualY l Ω ≅ d.dualX l Ω ⋙ d.star
  components (M : C l Ω X s) : epsilon.hom.app (op M) = d.epsilon l Ω M
  [dualXShift : (d.dualX l Ω).CommShift ℤ]
  [dualYShift : (d.dualY l Ω).CommShift ℤ]
  [starShift : d.star.CommShift ℤ]
  shift : epsilon.hom.CommShift ℤ

/-- The ordinary ambient dual into the displayed object, before restricting its source.
Source: blueprint definition of D_T (blueprint: sk-thm-sf-verdier-exchange). -/
def rawDual (T : Scheme.{u}) (s : RingStage.{u} l)
    (omega : DerivedCategory (pbcModules T ((s.coefficients l).ring T))) :=
  (Functor.curry.obj (ringHom l T s)).flip.obj omega

/-- The fixed K-injective target complex used in the existing Hom localization.
Source: blueprint signed Hom calculation (blueprint: sk-thm-sf-verdier-exchange). -/
abbrev homTarget (T : Scheme.{u}) (s : RingStage.{u} l)
    (O : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ) :=
  (coefficientHomResolution.{u, u + 1, u}
    (ProEt.topology T) ((s.coefficients l).ring T)).obj O

/-- The signed Hom comparison fixed by the product-component formula (-1)^(m*q).
The theorem's product equations determine this first witness uniquely; no arbitrary
shift automorphism is selected. Source: signed Hom calculation, blueprint step 4
(blueprint: sk-thm-sf-verdier-exchange). -/
def signedShift (T : Scheme.{u}) (s : RingStage.{u} l)
    (O P : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ) (m : ℤ) :=
  (CategoryTheory.SignedDoubleHomCone.comparison.{u + 1, u, u + 1, u + 1}
    (R := (s.coefficients l).ring T) (homTarget l T s O)).choose P m

/-- Realization of the dual's shift structure by the actual signed Hom complex.
The component equation fixes the localization comparison, and its CommShift law
transports the fixed sign convention to the ambient category.
Source: blueprint shift clause and proof step 4
(blueprint: sk-thm-sf-verdier-exchange). -/
structure DualShiftModel (T : Scheme.{u}) (s : RingStage.{u} l)
    (omega : DerivedCategory (pbcModules T ((s.coefficients l).ring T))) where
  target : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ
  targetIso : DerivedCategory.Q.obj target ≅ omega
  [complexShift : (CategoryTheory.SignedDoubleHomCone.dual.{u + 1, u, u + 1, u + 1}
    (R := (s.coefficients l).ring T) (homTarget l T s target)).CommShift ℤ]
  signed (P : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ) (r : ℤ) :
    ((CategoryTheory.SignedDoubleHomCone.dual.{u + 1, u, u + 1, u + 1}
      (R := (s.coefficients l).ring T) (homTarget l T s target)).commShiftIso r).hom.app
        (op P) =
      (signedShift l T s target P (-r)).hom ≫
        eqToHom (congrArg (fun n : ℤ =>
          (homComplex.{u + 1, u, u + 1, u + 1}
            (R := (s.coefficients l).ring T) P (homTarget l T s target))⟦n⟧) (neg_neg r))
  [ambientShift : (rawDual l T s omega).CommShift ℤ]
  realization : CategoryTheory.SignedDoubleHomCone.dual.{u + 1, u, u + 1, u + 1}
      (R := (s.coefficients l).ring T) (homTarget l T s target) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q.op ⋙ rawDual l T s omega
  components (P : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ) :
    realization.hom.app (op P) =
      (coefficientHomResolutionIso.{u, u + 1, u}
        (ProEt.topology T) ((s.coefficients l).ring T) P target).inv ≫
          (ringHom l T s).map (Prod.mkHom (𝟙 _) targetIso.hom)
  realizationShift : realization.hom.CommShift ℤ

/-- The canonical shift on the existing full constructible inclusions, by cases in
its recorded coefficient index. Source: full subcategory convention
(blueprint: sk-thm-sf-verdier-exchange). -/
instance ringInclusionShift (T : Scheme.{u}) (s : RingStage.{u} l) :
    (s.inclusion l Ω T).CommShift ℤ :=
  match s with
  | .finite _E _n => inferInstance
  | .integral _E => inferInstance

/-- Restrict the normalized ambient signed shifts to the constructible categories.
The ordinary pushforward comparison also respects its existing derived shift.
Source: blueprint shift clause (blueprint: sk-thm-sf-verdier-exchange). -/
structure RingShiftRealization {X Y S : Scheme.{u}} {f : X ⟶ Y}
    {s : RingStage.{u} l}
    {F : Operation l Ω X Y (s.stage l)} {A : Operation l Ω Y S (s.stage l)}
    {B : Operation l Ω X S (s.stage l)} {unit : C l Ω S (s.stage l)}
    {d : StageData l Ω (s.stage l) F A B unit}
    (r : RingRealization l Ω f s d) (c : StageConclusion l Ω d) where
  modelX : DualShiftModel l X s ((s.inclusion l Ω X).obj (B.G.obj unit))
  modelY : DualShiftModel l Y s ((s.inclusion l Ω Y).obj (A.G.obj unit))
  dualX : d.dualX l Ω ⋙ s.inclusion l Ω X ≅
    (s.inclusion l Ω X).op ⋙ rawDual l X s ((s.inclusion l Ω X).obj (B.G.obj unit))
  dualY : d.dualY l Ω ⋙ s.inclusion l Ω Y ≅
    (s.inclusion l Ω Y).op ⋙ rawDual l Y s ((s.inclusion l Ω Y).obj (A.G.obj unit))
  componentsX (M : C l Ω X (s.stage l)) :
    dualX.hom.app (op M) = r.homX.hom.app (op M, B.G.obj unit)
  componentsY (M : C l Ω Y (s.stage l)) :
    dualY.hom.app (op M) = r.homY.hom.app (op M, A.G.obj unit)
  shiftX : letI := c.dualXShift
    letI := modelX.ambientShift
    dualX.hom.CommShift ℤ
  shiftY : letI := c.dualYShift
    letI := modelY.ambientShift
    dualY.hom.CommShift ℤ
  starShift : letI := c.starShift
    r.star.hom.CommShift ℤ

/-- Comparison of the actual operations on their closed coefficient domains. Tensor
comparison is used covariantly; internal-Hom comparison will be its evaluation transpose.
The three exceptional comparisons retain both unit and counit normalization.
Source: blueprint exchange proof steps 5--8
(blueprint: sk-thm-sf-verdier-exchange). -/
structure StageScalar {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation l Ω X Y s} {As : Operation l Ω Y S s}
    {Bs : Operation l Ω X S s} {us : C l Ω S s}
    {Ft : Operation l Ω X Y t} {At : Operation l Ω Y S t}
    {Bt : Operation l Ω X S t} {ut : C l Ω S t}
    (ds : StageData l Ω s Fs As Bs us) (dt : StageData l Ω t Ft At Bt ut)
    (TX : C l Ω X s ⥤ C l Ω X t) (TY : C l Ω Y s ⥤ C l Ω Y t)
    (TS : C l Ω S s ⥤ C l Ω S t) where
  exceptional : FieldComparison l Ω Fs Ft TX TY
  structureY : FieldComparison l Ω As At TY TS
  structureX : FieldComparison l Ω Bs Bt TX TS
  unit : TS.obj us ≅ ut
  tensorX : ds.closedX.tensor ⋙ TX ≅ (TX.prod TX) ⋙ dt.closedX.tensor
  tensorY : ds.closedY.tensor ⋙ TY ≅ (TY.prod TY) ⋙ dt.closedY.tensor
  pull : ds.pull ⋙ TX ≅ TY ⋙ dt.pull
  projection (K : C l Ω Y s) (M : C l Ω X s) :
    TY.map (ds.projection K M).hom ≫ tensorY.hom.app (K, Fs.F.obj M) ≫
        dt.closedY.tensor.map (Prod.mkHom (𝟙 _) ((exceptional.q l Ω).hom.app M)) =
      (exceptional.q l Ω).hom.app (ds.closedX.tensor.obj (ds.pull.obj K, M)) ≫
        Ft.F.map (tensorX.hom.app (ds.pull.obj K, M) ≫
          dt.closedX.tensor.map (Prod.mkHom (pull.hom.app K) (𝟙 _))) ≫
        (dt.projection (TY.obj K) (TX.obj M)).hom

/-- The coefficient comparison on omega_X is b_a evaluated at the unit, followed by
its canonical unit identification. Source: blueprint proof step 8
(blueprint: sk-thm-sf-verdier-exchange). -/
def StageScalar.kappaX {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation l Ω X Y s} {As : Operation l Ω Y S s}
    {Bs : Operation l Ω X S s} {us : C l Ω S s}
    {Ft : Operation l Ω X Y t} {At : Operation l Ω Y S t}
    {Bt : Operation l Ω X S t} {ut : C l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {TS : C l Ω S s ⥤ C l Ω S t} (a : StageScalar l Ω ds dt TX TY TS) :
    TX.obj (Bs.G.obj us) ≅ Bt.G.obj ut :=
  (a.structureX.b l Ω).app us ≪≫ Bt.G.mapIso a.unit

/-- The identical construction on Y. Source: blueprint proof step 8
(blueprint: sk-thm-sf-verdier-exchange). -/
def StageScalar.kappaY {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation l Ω X Y s} {As : Operation l Ω Y S s}
    {Bs : Operation l Ω X S s} {us : C l Ω S s}
    {Ft : Operation l Ω X Y t} {At : Operation l Ω Y S t}
    {Bt : Operation l Ω X S t} {ut : C l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {TS : C l Ω S s ⥤ C l Ω S t} (a : StageScalar l Ω ds dt TX TY TS) :
    TY.obj (As.G.obj us) ≅ At.G.obj ut :=
  (a.structureY.b l Ω).app us ≪≫ At.G.mapIso a.unit

/-- Scalar comparison for the displayed dual on X, defined by extending evaluation
and transposing it. There is no arbitrary-input internal-Hom isomorphism hypothesis.
Source: blueprint proof step 8 (blueprint: sk-thm-sf-verdier-exchange). -/
def StageScalar.dualX {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation l Ω X Y s} {As : Operation l Ω Y S s}
    {Bs : Operation l Ω X S s} {us : C l Ω S s}
    {Ft : Operation l Ω X Y t} {At : Operation l Ω Y S t}
    {Bt : Operation l Ω X S t} {ut : C l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {TS : C l Ω S s ⥤ C l Ω S t} (a : StageScalar l Ω ds dt TX TY TS)
    (M : C l Ω X s) :
    TX.obj ((ds.dualX l Ω).obj (op M)) ⟶ (dt.dualX l Ω).obj (op (TX.obj M)) :=
  dt.closedX.transpose _ (TX.obj M) (Bt.G.obj ut)
    (a.tensorX.inv.app ((ds.dualX l Ω).obj (op M), M) ≫
      TX.map (ds.closedX.evaluation M (Bs.G.obj us)) ≫ (a.kappaX l Ω).hom)

/-- Scalar comparison for the dual on Y, with the same evaluation normalization.
Source: blueprint proof step 8 (blueprint: sk-thm-sf-verdier-exchange). -/
def StageScalar.dualY {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation l Ω X Y s} {As : Operation l Ω Y S s}
    {Bs : Operation l Ω X S s} {us : C l Ω S s}
    {Ft : Operation l Ω X Y t} {At : Operation l Ω Y S t}
    {Bt : Operation l Ω X S t} {ut : C l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {TS : C l Ω S s ⥤ C l Ω S t} (a : StageScalar l Ω ds dt TX TY TS)
    (M : C l Ω Y s) :
    TY.obj ((ds.dualY l Ω).obj (op M)) ⟶ (dt.dualY l Ω).obj (op (TY.obj M)) :=
  dt.closedY.transpose _ (TY.obj M) (At.G.obj ut)
    (a.tensorY.inv.app ((ds.dualY l Ω).obj (op M), M) ≫
      TY.map (ds.closedY.evaluation M (As.G.obj us)) ≫ (a.kappaY l Ω).hom)

/-- Direct-image coefficient comparison as the counit-normalized mate of pullback
comparison. Its domain is precisely the specified constructible coefficient domain.
Source: blueprint final coefficient sentence (blueprint: sk-thm-sf-verdier-exchange). -/
def StageScalar.star {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation l Ω X Y s} {As : Operation l Ω Y S s}
    {Bs : Operation l Ω X S s} {us : C l Ω S s}
    {Ft : Operation l Ω X Y t} {At : Operation l Ω Y S t}
    {Bt : Operation l Ω X S t} {ut : C l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {TS : C l Ω S s ⥤ C l Ω S t} (a : StageScalar l Ω ds dt TX TY TS)
    (M : C l Ω X s) : TY.obj (ds.star.obj M) ⟶ dt.star.obj (TX.obj M) :=
  dt.adjunction.homEquiv _ _
    (a.pull.inv.app (ds.star.obj M) ≫ TX.map (ds.adjunction.counit.app M))

/-- The two actual coefficient squares: c is preserved under b and the unit, and epsilon
is preserved under the evaluation-defined Hom map and direct-image mate. These equations
cover quotient maps, ramified scalar changes, integral reduction and field descent.
Source: blueprint proof steps 6--8 (blueprint: sk-thm-sf-verdier-exchange). -/
structure ScalarConclusion {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation l Ω X Y s} {As : Operation l Ω Y S s}
    {Bs : Operation l Ω X S s} {us : C l Ω S s}
    {Ft : Operation l Ω X Y t} {At : Operation l Ω Y S t}
    {Bt : Operation l Ω X S t} {ut : C l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {TS : C l Ω S s ⥤ C l Ω S t} (a : StageScalar l Ω ds dt TX TY TS) : Prop where
  dualizing : TX.map ds.dualizing.hom ≫ (a.kappaX l Ω).hom =
    (a.exceptional.b l Ω).hom.app (As.G.obj us) ≫
      Ft.G.map (a.kappaY l Ω).hom ≫ dt.dualizing.hom
  exchange (M : C l Ω X s) :
    TY.map (ds.epsilon l Ω M) ≫ a.star l Ω ((ds.dualX l Ω).obj (op M)) ≫
        dt.star.map (a.dualX l Ω M) =
      a.dualY l Ω (Fs.F.obj M) ≫
        (dt.dualY l Ω).map ((a.exceptional.q l Ω).inv.app M).op ≫
        dt.epsilon l Ω (TX.obj M)

/-- Shift compatibility of the evaluation-transposed coefficient arrows, on exactly
these dualizing pairs. This transports the integral signed normalization to fields.
The arrows are not assumed invertible on additional ambient inputs.
Source: blueprint coefficient and shift clauses (blueprint: sk-thm-sf-verdier-exchange). -/
structure ScalarShifts {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation l Ω X Y s} {As : Operation l Ω Y S s}
    {Bs : Operation l Ω X S s} {us : C l Ω S s}
    {Ft : Operation l Ω X Y t} {At : Operation l Ω Y S t}
    {Bt : Operation l Ω X S t} {ut : C l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    (cs : StageConclusion l Ω ds) (ct : StageConclusion l Ω dt)
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {TS : C l Ω S s ⥤ C l Ω S t} (b : StageScalar l Ω ds dt TX TY TS) where
  dualX : ds.dualX l Ω ⋙ TX ⟶ TX.op ⋙ dt.dualX l Ω
  dualY : ds.dualY l Ω ⋙ TY ⟶ TY.op ⋙ dt.dualY l Ω
  star : ds.star ⋙ TY ⟶ TX ⋙ dt.star
  componentsX (M : C l Ω X s) : dualX.app (op M) = b.dualX l Ω M
  componentsY (M : C l Ω Y s) : dualY.app (op M) = b.dualY l Ω M
  componentsStar (M : C l Ω X s) : star.app M = b.star l Ω M
  shiftX : letI := cs.dualXShift
    letI := ct.dualXShift
    letI := b.exceptional.shiftX
    dualX.CommShift ℤ
  shiftY : letI := cs.dualYShift
    letI := ct.dualYShift
    letI := b.exceptional.shiftY
    dualY.CommShift ℤ
  shiftStar : letI := cs.starShift
    letI := ct.starShift
    letI := b.exceptional.shiftX
    letI := b.exceptional.shiftY
    star.CommShift ℤ

/-- Use the same signed K-flat tensor model for the ringed projection construction and
for closed evaluation. The normalization pins the comparison on every flat representative.
Source: blueprint projection and tensor--Hom construction
(blueprint: sk-thm-sf-verdier-exchange). -/
structure ProjectionTensor (T : Scheme.{u}) (s : RingStage.{u} l)
    (m : RingedSiteDualityModel.{u + 1, u, u}
      (ProEt.topology T) ((s.coefficients l).ring T)) where
  representative :
    ((proEtaleFlatRepresentatives T ((s.coefficients l).ring T)).ι.prod
      (proEtaleFlatRepresentatives T ((s.coefficients l).ring T)).ι) ⋙
        Functor.uncurry.obj
          ((proEtaleOrdinaryTensor T ((s.coefficients l).ring T)).map₂HomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      (((proEtaleFlatRepresentatives T ((s.coefficients l).ring T)).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives T ((s.coefficients l).ring T)).ι ⋙ DerivedCategory.Q)) ⋙
          (RingedSiteDualityModel.closed.{u + 1, u, u} m).tensor
  nativeKFlat (P : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ)
      (hP : proEtaleFlatRepresentatives T ((s.coefficients l).ring T) P) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      T.ProEt inferInstance (smallSite T) (ProEt.topology T) ((s.coefficients l).ring T) P
  normalized (P Q : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ)
      (hp : proEtaleFlatRepresentatives T ((s.coefficients l).ring T) P)
      (hq : proEtaleFlatRepresentatives T ((s.coefficients l).ring T) Q) :
    HEq (representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩))
      ((WeilConjectures.CoefficientTensorModels.iso.{u, u + 1, u}
        (ProEt.topology T) ((s.coefficients l).ring T)
        (RingedSiteDualityModel.closed.{u + 1, u, u} m)
        (RingedSiteDualityModel.models.{u + 1, u, u} m) P Q
        (nativeKFlat P hp) (nativeKFlat Q hq)).hom)

/-- The actual projection tensor model, with the preceding representative comparison.
Source: blueprint projection construction (blueprint: sk-thm-sf-verdier-exchange). -/
def ProjectionTensor.toModel {T : Scheme.{u}} {s : RingStage.{u} l}
    {m : RingedSiteDualityModel.{u + 1, u, u}
      (ProEt.topology T) ((s.coefficients l).ring T)}
    (a : ProjectionTensor l T s m) : ProEtaleTensorModel T ((s.coefficients l).ring T) where
  tensor := (RingedSiteDualityModel.closed.{u + 1, u, u} m).tensor
  representative := a.representative

/-- The projection used in epsilon is the actual proper-counit/open-projection map,
with the two symmetries needed for the order evaluation tensor source. Each comparison
is retained, so rescaling a projection or selecting an unrelated isomorphism is excluded.
Source: blueprint exchange proof step 3 and compactification projection construction
(blueprint: sk-thm-sf-verdier-exchange). -/
structure RingProjection {X Y S : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (s : RingStage.{u} l)
    {F : Operation l Ω X Y (s.stage l)} {A : Operation l Ω Y S (s.stage l)}
    {B : Operation l Ω X S (s.stage l)} {unit : C l Ω S (s.stage l)}
    {d : StageData l Ω (s.stage l) F A B unit}
    (r : RingRealization l Ω f s d) (left : LeftRealization l Ω c s F) where
  tensorX : ProjectionTensor l X s r.modelX
  tensorY : ProjectionTensor l Y s r.modelY
  tensorBar : ProEtaleTensorModel c.Z ((s.coefficients l).ring c.Z)
  pullComposition : (s.coefficients l).pull (c.i ≫ c.g) =
    proEtaleRingCompositeCoefficients c.i c.g
      ((s.coefficients l).ring Y) ((s.coefficients l).ring c.Z)
      ((s.coefficients l).ring X) ((s.coefficients l).pull c.g) ((s.coefficients l).pull c.i)
  projectionIso (M : C l Ω X (s.stage l)) (K : C l Ω Y (s.stage l)) :
    r.modelY.closed.tensor.obj
        ((PurCompactSupport.image (s.coefficients l) c).obj ((s.inclusion l Ω X).obj M),
          (s.inclusion l Ω Y).obj K) ≅
      (PurCompactSupport.image (s.coefficients l) c).obj
        (r.modelX.closed.tensor.obj ((s.inclusion l Ω X).obj M,
          (PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion l Ω Y).obj K)))
  projectionMap (M : C l Ω X (s.stage l)) (K : C l Ω Y (s.stage l)) :
    (projectionIso M K).hom =
      ((PurCompactSupport.projectionMap (s.coefficients l) c
        tensorX.toModel tensorBar tensorY.toModel pullComposition).app
          ((s.inclusion l Ω X).obj M)).app ((s.inclusion l Ω Y).obj K)
  normalized (K : C l Ω Y (s.stage l)) (M : C l Ω X (s.stage l)) :
    (s.inclusion l Ω Y).map (d.projection K M).hom =
      left.hom.app (d.closedX.tensor.obj (d.pull.obj K, M)) ≫
        (PurCompactSupport.image (s.coefficients l) c).map
          (r.tensorX.hom.app (d.pull.obj K, M) ≫
            r.modelX.closed.tensor.map (Prod.mkHom (r.pull.hom.app K) (𝟙 _)) ≫
            (r.modelX.symmetric.braiding
              ((PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion l Ω Y).obj K))
              ((s.inclusion l Ω X).obj M)).hom) ≫
        (projectionIso M K).inv ≫
        (r.modelY.symmetric.braiding
          ((PurCompactSupport.image (s.coefficients l) c).obj ((s.inclusion l Ω X).obj M))
          ((s.inclusion l Ω Y).obj K)).hom ≫
        r.modelY.closed.tensor.map (Prod.mkHom (𝟙 _) (left.inv.app M)) ≫
        r.tensorY.inv.app (K, F.F.obj M)

/-- The actual regular-module morphism induced by a map of coefficient sheaves.
Source: blueprint coefficient-unit comparison (blueprint: sk-thm-sf-verdier-exchange). -/
def ringUnitRestrictionSheaf {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (T : Scheme.{u}) :
    SheafOfModules.unit ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((s.coefficients l).ring T)) ⟶
      (pbcRestrict (a.map T)).obj (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((t.coefficients l).ring T))) :=
  { val := (SheafOfModules.unitToPushforwardObjUnit (F := 𝟭 T.ProEt)
      (J := ProEt.topology T) (K := ProEt.topology T)
      (S := (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((s.coefficients l).ring T))
      (R := (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((t.coefficients l).ring T))
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.map T))).val }

/-- Localize the actual coefficient map in degree zero, then use exact restriction.
Source: blueprint coefficient-unit comparison (blueprint: sk-thm-sf-verdier-exchange). -/
def ringUnitRestriction {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (T : Scheme.{u}) :
    ringUnit l T s ⟶ (pbcDerivedRestrict (a.map T)).obj (ringUnit l T t) :=
  (DerivedCategory.singleFunctor _ 0).map (ringUnitRestrictionSheaf l a T) ≫
    ((pbcRestrict (a.map T)).mapDerivedCategorySingleFunctor 0).inv.app
      (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((t.coefficients l).ring T)))

/-- The coefficient-unit extension map is the transpose of the preceding actual map.
Source: blueprint coefficient-unit comparison (blueprint: sk-thm-sf-verdier-exchange). -/
def ringUnitScalar {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (T : Scheme.{u}) :
    (pbcDerivedExtend (a.map T)).obj (ringUnit l T s) ⟶ ringUnit l T t :=
  (pbcDerivedScalarAdjunction (a.map T)).homEquiv _ _ |>.symm (ringUnitRestriction l a T)

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (Sf : System l Ω D hl (f := f)) (Sg : System l Ω D hl (f := g))
  (Sfg : System l Ω D hl (f := f ≫ g))
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- The already normalized completed compositor expressed through the three recorded
left realizations. Its unique full-subcategory preimage is used before taking its mate.
No maps of normalized towers are recovered merely from their evaluations.
Source: blueprint proof steps 2 and 7; Stacks 0F7J
(blueprint: sk-thm-sf-verdier-exchange). -/
def integralAlphaRealization (E : FieldStage.{u} l) :
    ((Sf.ring.operation cf (.integral E)).F ⋙ (Sg.ring.operation cg (.integral E)).F) ⋙
        PurCompactSupport.finiteTorIntegralInclusion l E.carrier Z ≅
      (Sfg.ring.operation cfg (.integral E)).F ⋙
        PurCompactSupport.finiteTorIntegralInclusion l E.carrier Z :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Sg.ring.integralLeft cg E) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Sf.ring.integralLeft cf E) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (sfFieldShriekCompositionIntegral D l hl cf cg cfg E.carrier) ≪≫
    (Sfg.ring.integralLeft cfg E).symm

/-- All-stage exchange on the actual coefficient categories. These are conclusions,
including the realizations: there is no extra hypothesis about existence of an ambient
exceptional adjoint, a duality, a projection isomorphism, or a coefficient comparison.
The integral compositor normalization and all finite reductions fix c; rational and
common-stage passages descend that same map. The component epsilon is a real definition.
Source: blueprint exchange statement and proof steps 1--8
(blueprint: sk-thm-sf-verdier-exchange). -/
structure Package where
  unit (s : Stage.{u} l) : C l Ω Z s
  stage (s : Stage.{u} l) : StageData l Ω s
    (Sf.ring.operation cf s) (Sg.ring.operation cg s) (Sfg.ring.operation cfg s) (unit s)
  ring (s : RingStage.{u} l) : RingRealization l Ω f s (stage (s.stage l))
  projection (s : RingStage.{u} l) :
    RingProjection l Ω cf s (ring s) (Sf.ring.left cf s)
  conclusion (s : Stage.{u} l) : StageConclusion l Ω (stage s)
  ringShifts (s : RingStage.{u} l) :
    RingShiftRealization l Ω (ring s) (conclusion (s.stage l))
  exchangeNaturality {s t : Stage.{u} l}
      {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
      {TZ : C l Ω Z s ⥤ C l Ω Z t}
      (b : StageScalar l Ω (stage s) (stage t) TX TY TZ)
      (_hc : TX.map (stage s).dualizing.hom ≫ (b.kappaX l Ω).hom =
        (b.exceptional.b l Ω).hom.app ((Sg.ring.operation cg s).G.obj (unit s)) ≫
          (Sf.ring.operation cf t).G.map (b.kappaY l Ω).hom ≫ (stage t).dualizing.hom)
      (M : C l Ω X s) :
    TY.map ((stage s).epsilon l Ω M) ≫
        b.star l Ω (((stage s).dualX l Ω).obj (op M)) ≫
        (stage t).star.map (b.dualX l Ω M) =
      b.dualY l Ω ((Sf.ring.operation cf s).F.obj M) ≫
        ((stage t).dualY l Ω).map ((b.exceptional.q l Ω).inv.app M).op ≫
        (stage t).epsilon l Ω (TX.obj M)
  integralAlpha (E : FieldStage.{u} l) :
    (Sf.ring.operation cf (.integral E)).F ⋙ (Sg.ring.operation cg (.integral E)).F ≅
      (Sfg.ring.operation cfg (.integral E)).F
  integralAlpha_normalized (E : FieldStage.{u} l) :
    Functor.isoWhiskerRight (integralAlpha E)
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier Z) =
      integralAlphaRealization l Ω D hl f g Sf Sg Sfg cf cg cfg E
  integralDualizing (E : FieldStage.{u} l) :
    (stage (.integral E)).dualizing =
      (composition (Sf.ring.operation cf (.integral E)).adjunction
        (Sg.ring.operation cg (.integral E)).adjunction
        (Sfg.ring.operation cfg (.integral E)).adjunction (integralAlpha E)).app
          (unit (.integral E))
  ringScalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :
    ∃ (SX : Scalar l Ω a X) (SY : Scalar l Ω a Y) (SZ : Scalar l Ω a Z),
      ∃ b : StageScalar l Ω (stage (s.stage l)) (stage (t.stage l))
          SX.functor SY.functor SZ.functor,
        ScalarConclusion l Ω b ∧
        Nonempty (ScalarShifts l Ω (conclusion (s.stage l))
          (conclusion (t.stage l)) b) ∧
        (∀ K : C l Ω X (s.stage l),
          (t.inclusion l Ω Y).map ((b.exceptional.q l Ω).hom.app K) ≫
              (Sf.ring.left cf t).hom.app (SX.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cf).map
                (SX.realization.hom.app K) =
            SY.realization.hom.app ((Sf.ring.operation cf (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Y)).map ((Sf.ring.left cf s).hom.app K) ≫
              (PurCompactSupport.comparison a cf).app ((s.inclusion l Ω X).obj K)) ∧
        (∀ K : C l Ω Y (s.stage l),
          (t.inclusion l Ω Z).map ((b.structureY.q l Ω).hom.app K) ≫
              (Sg.ring.left cg t).hom.app (SY.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cg).map
                (SY.realization.hom.app K) =
            SZ.realization.hom.app ((Sg.ring.operation cg (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Z)).map ((Sg.ring.left cg s).hom.app K) ≫
              (PurCompactSupport.comparison a cg).app ((s.inclusion l Ω Y).obj K)) ∧
        (∀ K : C l Ω X (s.stage l),
          (t.inclusion l Ω Z).map ((b.structureX.q l Ω).hom.app K) ≫
              (Sfg.ring.left cfg t).hom.app (SX.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cfg).map
                (SX.realization.hom.app K) =
            SZ.realization.hom.app ((Sfg.ring.operation cfg (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Z)).map ((Sfg.ring.left cfg s).hom.app K) ≫
              (PurCompactSupport.comparison a cfg).app ((s.inclusion l Ω X).obj K)) ∧
        (t.inclusion l Ω Z).map b.unit.hom ≫ (ring t).unitIso.hom =
          SZ.realization.hom.app (unit (s.stage l)) ≫
            (pbcDerivedExtend (a.map Z)).map (ring s).unitIso.hom ≫ ringUnitScalar l a Z
  rationalization (E : FieldStage.{u} l) :
    ∃ b : StageScalar l Ω (stage (.integral E)) (stage (.rational E))
        (ConstructibleExceptionalCoefficients.rationalization l Ω E X)
        (ConstructibleExceptionalCoefficients.rationalization l Ω E Y)
        (ConstructibleExceptionalCoefficients.rationalization l Ω E Z),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.integral E))
        (conclusion (.rational E)) b) ∧
      b.exceptional = Sf.fields.rationalizationComparison cf E ∧
      b.structureY = Sg.fields.rationalizationComparison cg E ∧
      b.structureX = Sfg.fields.rationalizationComparison cfg E
  rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    ∃ b : StageScalar l Ω (stage (.rational E)) (stage (.rational L))
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i X)
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i Y)
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i Z),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.rational E))
        (conclusion (.rational L)) b) ∧
      b.exceptional = Sf.fields.rationalComparison cf E L i ∧
      b.structureY = Sg.fields.rationalComparison cg E L i ∧
      b.structureX = Sfg.fields.rationalComparison cfg E L i
  common (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ∃ b : StageScalar l Ω (stage (.rational (commonField l Ω i))) (stage .closed)
        (commonInclusion l Ω X i) (commonInclusion l Ω Y i) (commonInclusion l Ω Z i),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.rational (commonField l Ω i)))
        (conclusion .closed) b) ∧
      b.exceptional = Sf.common.commonComparison cf i ∧
      b.structureY = Sg.common.commonComparison cg i ∧
      b.structureX = Sfg.common.commonComparison cfg i

end Geometry

/-- Specialize the operation package to the coefficient point with its identity
structure map. This fixes the base-over-base instance explicitly; the Spec algebra
instance can otherwise choose Spec(map id), which is not definitionally the identity.
All choices below are of existing normalized operations and compactifications.
Source: blueprint exchange setting s=Spec k (blueprint: sk-thm-sf-verdier-exchange). -/
def Assertion (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : Prop :=
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  ∀ (Sf : System l Ω D hl (f := f))
    (SY : System l Ω D hl (f := Y ↘ Spec (.of D.k)))
    (SX : System l Ω D hl (f := f ≫ (Y ↘ Spec (.of D.k))))
    (cf : Compactification f) (cY : Compactification (Y ↘ Spec (.of D.k)))
    (cX : Compactification (f ≫ (Y ↘ Spec (.of D.k)))),
    Nonempty (Package l Ω D hl f (Y ↘ Spec (.of D.k)) Sf SY SX cf cY cX)

/-- Verdier exchange for separated finite-type schemes over the fixed algebraic
closure of a finite field, at every positive finite level, at completed integral
coefficients, at finite coefficient fields, and over the algebraic closure of Q_l.
The three Systems are choices of the already constructed normalized operations, not
ambient exceptional-adjoint hypotheses. The conclusion supplies the canonical maps,
their ambient realizations, naturality, the [-r] shift law, and coefficient squares.

Source: main-20261015, sec-six-functors/sk-thm-sf-verdier-exchange, order 2503
(blueprint: sk-thm-sf-verdier-exchange).

Proof plan, in the order of the node:
1. The coefficient unit at the point is constructible of Tor amplitude [0,0]. Apply
   the constructible exceptional functors to obtain omega_X and omega_Y. The ring
   realizations use the original small pro-etale sites and completed integral sheaf.
2. Use lem-sf-constructible-exceptional-adjunction-coefficients for f, a_Y and a_X.
   Restrict canonical compact-support composition, thm-sf-comp-composition, to these
   full domains. At integral coefficients use the completed proper/open compositor
   in fix-lem-exchanges, realized by integralAlphaRealization. Conjugate its inverse
   under the composite adjunction and evaluate at the coefficient unit to obtain c.
3. Apply sk-thm-sf-tensor-hom with N=omega_Y and invert its isomorphism. Follow it
   by Rf_* RHom(M,c). Transposing the evaluations shows that this is exactly epsilon,
   which is defined above from the actual projection and the two adjunctions.
4. Naturality in the contravariant variable follows from naturality of evaluation,
   projection, both adjunction bijections and c. Their shift comparisons yield the
   commutative square with [-r]. DualShiftModel fixes the ordinary Hom shift
   to the product-component sign (-1)^(m*q) before localization.
   RingShiftRealization restricts it to the constructible categories; ScalarShifts
   carries that normalization through rationalization and common stages.
5. For each allowed finite quotient, integral reduction, or ramified finite-free
   scalar map, use the counit-normalized q and b of the constructible System.
   lem-sp-et-proet-coefficient-compatibility gives the composition/q square.
6. Transpose its two sides under the composite adjunction. The counit equations
   identify both with the same composite of q, inverse alpha and the old counits.
   Faithfulness of the Hom equivalence proves the scalar square for c; this is the
   mate-pasting calculation of lem-weil-pbc-mate-pasting and adjunction-conjugate.
7. Use lem-coef-cartesian-section-adjoint-mates and the finite adjoint comparisons
   on coherent cartesian systems. lem-coef-semilinear-derived-sections and
   lem-sf-integral-compactification-system-realization identify the actual completed
   proper/open composites before total limit. Their maps, not an arbitrary family
   of evaluated finite arrows, give the integral equation. Rationalization and
   common finite-stage descent preserve these equations and all inverses.
8. Evaluate at the coefficient unit. Naturality gives the kappa/c equation displayed
   in ScalarConclusion. Internal-Hom comparison is extended evaluation transposed;
   direct-image comparison is the pullback/counit mate. Paste their squares to obtain
   the displayed epsilon equation, on exactly these constructible domains. The
   exchangeNaturality field records it for every projection-compatible comparison,
   so it applies to the specified canonical maps independently of their presentations. Field
   reduction always means reduction of an integral representative before localization.
-/
theorem verdier_exchange
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    : Assertion l Ω D hl f := by
  sorry

end VerdierExchange
end WeilConjectures
