/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingedSiteDualityMaps
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.SignedDoubleHomConeSupplement
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.FieldShriekCompositionQcqs

/-! # Verdier-exchange definition interface

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-verdier-exchange, construction and normalization clauses
(blueprint: def-sf-verdier-exchange-data).

The exceptional functors below are the existing constructible adjoints. In particular
none of these definitions uses an ambient exceptional-adjoint datum.
The complete definition interface is moved out of the quarantined theorem module.
There is no existence assertion and no import of either exchange theorem module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option relaxedAutoImplicit false
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
(blueprint: def-sf-verdier-exchange-data). -/
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
Source: the project's small-site convention (blueprint: def-sf-verdier-exchange-data). -/
instance smallSite (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt

open ConstructibleExceptionalCoefficients

/-- The existing ambient ring-stage internal Hom on the original small pro-etale site.
The finite and integral cases use precisely the coefficient sheaves of RingStage.
Source: blueprint sk-def-sf-operations (i), specialized to the displayed duals
(blueprint: def-sf-verdier-exchange-data). -/
abbrev ringHom (T : Scheme.{u}) (s : RingStage.{u} l) :=
  derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology T) ((s.coefficients l).ring T)

/-- The coefficient sheaf itself in degree zero, rather than an unspecified unit object.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 1
(blueprint: def-sf-verdier-exchange-data). -/
def ringUnit (T : Scheme.{u}) (s : RingStage.{u} l) :
    DerivedCategory (pbcModules T ((s.coefficients l).ring T)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((s.coefficients l).ring T)))

/-- Internal Hom into the specified dualizing object, restricted in its first variable
by the existing full finite-Tor inclusion. The target remains the ambient derived category.
Source: blueprint sk-thm-sf-verdier-exchange, definition of D_T
(blueprint: def-sf-verdier-exchange-data). -/
def ringDual (T : Scheme.{u}) (s : RingStage.{u} l)
    (omega : C.{u} l Ω T (s.stage l)) :
    (C.{u} l Ω T (s.stage l))ᵒᵖ ⥤
      DerivedCategory (pbcModules T ((s.coefficients l).ring T)) :=
  (s.inclusion.{u} l Ω T).op ⋙
    (Functor.curry.obj (ringHom l T s)).flip.obj ((s.inclusion.{u} l Ω T).obj omega)

/-- Substitution of the dualizing-object comparison in the second variable of RHom.
This is the second arrow in the required exchange; it acts on the actual internal Hom.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 3
(blueprint: def-sf-verdier-exchange-data). -/
def substitute {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (omega omega' : C.{u} l Ω X (s.stage l)) (c : omega ≅ omega') :
    ringDual l Ω X s omega ⋙ PurCompactSupport.push (s.coefficients l) f ≅
      ringDual l Ω X s omega' ⋙ PurCompactSupport.push (s.coefficients l) f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (s.inclusion.{u} l Ω X).op
      ((Functor.curry.obj (ringHom l X s)).flip.mapIso
        ((s.inclusion.{u} l Ω X).mapIso c)))
    (PurCompactSupport.push (s.coefficients l) f)

/-- The required orientation of Verdier exchange: invert tensor-Hom exchange, then
apply Rf_* RHom(M,-) to c_Lambda. No objectwise isomorphism is selected.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 3
(blueprint: def-sf-verdier-exchange-data). -/
def exchange {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (F : C.{u} l Ω X (s.stage l) ⥤ C.{u} l Ω Y (s.stage l))
    (G : C.{u} l Ω Y (s.stage l) ⥤ C.{u} l Ω X (s.stage l))
    (omegaY : C.{u} l Ω Y (s.stage l)) (omegaX : C.{u} l Ω X (s.stage l))
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
(blueprint: def-sf-verdier-exchange-data). -/
structure StageData {X Y S : Scheme.{u}} (s : Stage.{u} l)
    (F : Operation.{u} l Ω X Y s) (A : Operation.{u} l Ω Y S s)
    (B : Operation.{u} l Ω X S s) (unit : C.{u} l Ω S s) where
  homX : (C.{u} l Ω X s)ᵒᵖ × C.{u} l Ω X s ⥤ C.{u} l Ω X s
  homY : (C.{u} l Ω Y s)ᵒᵖ × C.{u} l Ω Y s ⥤ C.{u} l Ω Y s
  closedX : CoefficientClosedStructure homX
  closedY : CoefficientClosedStructure homY
  pull : C.{u} l Ω Y s ⥤ C.{u} l Ω X s
  star : C.{u} l Ω X s ⥤ C.{u} l Ω Y s
  adjunction : pull ⊣ star
  projection (K : C.{u} l Ω Y s) (M : C.{u} l Ω X s) :
    F.F.obj (closedX.tensor.obj (pull.obj K, M)) ≅
      closedY.tensor.obj (K, F.F.obj M)
  dualizing : F.G.obj (A.G.obj unit) ≅ B.G.obj unit

/-- Internal Hom into the exceptional inverse image of the coefficient unit.
Source: blueprint definition of D_T (blueprint: def-sf-verdier-exchange-data). -/
def StageData.dualX {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation.{u} l Ω X Y s} {A : Operation.{u} l Ω Y S s}
    {B : Operation.{u} l Ω X S s} {unit : C.{u} l Ω S s}
    (d : StageData l Ω s F A B unit) : (C.{u} l Ω X s)ᵒᵖ ⥤ C.{u} l Ω X s :=
  (Functor.curry.obj d.homX).flip.obj (B.G.obj unit)

/-- Internal Hom into omega_Y, with its actual contravariant arrow action.
Source: blueprint definition of D_T (blueprint: def-sf-verdier-exchange-data). -/
def StageData.dualY {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation.{u} l Ω X Y s} {A : Operation.{u} l Ω Y S s}
    {B : Operation.{u} l Ω X S s} {unit : C.{u} l Ω S s}
    (d : StageData l Ω s F A B unit) : (C.{u} l Ω Y s)ᵒᵖ ⥤ C.{u} l Ω Y s :=
  (Functor.curry.obj d.homY).flip.obj (A.G.obj unit)

/-- The canonical exchange arrow, without selecting any isomorphism. First use the
projection isomorphism and evaluation, then the constructible exceptional adjunction,
postcomposition by c, tensor--Hom transposition, and the ordinary pull/star adjunction.
This is the inverse tensor--Hom exchange followed by Rf_* RHom(M,c) from step 3.
Source: blueprint exchange proof steps 2--3
(blueprint: def-sf-verdier-exchange-data). -/
def StageData.epsilon {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation.{u} l Ω X Y s} {A : Operation.{u} l Ω Y S s}
    {B : Operation.{u} l Ω X S s} {unit : C.{u} l Ω S s}
    (d : StageData l Ω s F A B unit) (M : C.{u} l Ω X s) :
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
(blueprint: def-sf-verdier-exchange-data). -/
structure RingRealization {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (s : RingStage.{u} l)
    {F : Operation.{u} l Ω X Y (s.stage l)} {A : Operation.{u} l Ω Y S (s.stage l)}
    {B : Operation.{u} l Ω X S (s.stage l)} {unit : C.{u} l Ω S (s.stage l)}
    (d : StageData l Ω (s.stage l) F A B unit) where
  unitIso : (s.inclusion.{u} l Ω S).obj unit ≅ ringUnit l S s
  modelX : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology X) ((s.coefficients l).ring X)
  modelY : RingedSiteDualityModel.{u + 1, u, u}
    (ProEt.topology Y) ((s.coefficients l).ring Y)
  homX : d.homX ⋙ s.inclusion.{u} l Ω X ≅
    ((s.inclusion.{u} l Ω X).op.prod (s.inclusion.{u} l Ω X)) ⋙ ringHom l X s
  homY : d.homY ⋙ s.inclusion.{u} l Ω Y ≅
    ((s.inclusion.{u} l Ω Y).op.prod (s.inclusion.{u} l Ω Y)) ⋙ ringHom l Y s
  tensorX : d.closedX.tensor ⋙ s.inclusion.{u} l Ω X ≅
    ((s.inclusion.{u} l Ω X).prod (s.inclusion.{u} l Ω X)) ⋙ modelX.closed.tensor
  tensorY : d.closedY.tensor ⋙ s.inclusion.{u} l Ω Y ≅
    ((s.inclusion.{u} l Ω Y).prod (s.inclusion.{u} l Ω Y)) ⋙ modelY.closed.tensor
  evaluationX (M N : C.{u} l Ω X (s.stage l)) :
    (s.inclusion.{u} l Ω X).map (d.closedX.evaluation M N) =
      tensorX.hom.app (d.homX.obj (op M, N), M) ≫
        modelX.closed.tensor.map (Prod.mkHom (homX.hom.app (op M, N)) (𝟙 _)) ≫
        modelX.closed.evaluation ((s.inclusion.{u} l Ω X).obj M) ((s.inclusion.{u} l Ω X).obj N)
  evaluationY (M N : C.{u} l Ω Y (s.stage l)) :
    (s.inclusion.{u} l Ω Y).map (d.closedY.evaluation M N) =
      tensorY.hom.app (d.homY.obj (op M, N), M) ≫
        modelY.closed.tensor.map (Prod.mkHom (homY.hom.app (op M, N)) (𝟙 _)) ≫
        modelY.closed.evaluation ((s.inclusion.{u} l Ω Y).obj M) ((s.inclusion.{u} l Ω Y).obj N)
  pull : d.pull ⋙ s.inclusion.{u} l Ω X ≅
    s.inclusion.{u} l Ω Y ⋙ PurCompactSupport.pull (s.coefficients l) f
  star : d.star ⋙ s.inclusion.{u} l Ω Y ≅
    s.inclusion.{u} l Ω X ⋙ PurCompactSupport.push (s.coefficients l) f
  adjunction (K : C.{u} l Ω Y (s.stage l)) (M : C.{u} l Ω X (s.stage l))
      (a : d.pull.obj K ⟶ M) :
    (s.inclusion.{u} l Ω Y).map (d.adjunction.homEquiv K M a) ≫ star.hom.app M =
      (proEtaleRingDerivedAdjunction f ((s.coefficients l).ring Y)
        ((s.coefficients l).ring X) ((s.coefficients l).pull f)).homEquiv _ _
          (pull.inv.app K ≫ (s.inclusion.{u} l Ω X).map a)

/-- The natural exchange is required to have the already defined canonical components.
Its shift structure is on opposite categories: shifting M by r shifts D(M) by -r.
Source: blueprint exchange, naturality and shift sentence
(blueprint: def-sf-verdier-exchange-data). -/
structure StageConclusion {X Y S : Scheme.{u}} {s : Stage.{u} l}
    {F : Operation.{u} l Ω X Y s} {A : Operation.{u} l Ω Y S s}
    {B : Operation.{u} l Ω X S s} {unit : C.{u} l Ω S s}
    (d : StageData l Ω s F A B unit) where
  epsilon : F.F.op ⋙ d.dualY l Ω ≅ d.dualX l Ω ⋙ d.star
  components (M : C.{u} l Ω X s) : epsilon.hom.app (op M) = d.epsilon l Ω M
  [dualXShift : (d.dualX l Ω).CommShift ℤ]
  [dualYShift : (d.dualY l Ω).CommShift ℤ]
  [starShift : d.star.CommShift ℤ]
  shift : epsilon.hom.CommShift ℤ

/-- The ordinary ambient dual into the displayed object, before restricting its source.
Source: blueprint definition of D_T (blueprint: def-sf-verdier-exchange-data). -/
def rawDual (T : Scheme.{u}) (s : RingStage.{u} l)
    (omega : DerivedCategory (pbcModules T ((s.coefficients l).ring T))) :=
  (Functor.curry.obj (ringHom l T s)).flip.obj omega

/-- The fixed K-injective target complex used in the existing Hom localization.
Source: blueprint signed Hom calculation (blueprint: def-sf-verdier-exchange-data). -/
abbrev homTarget (T : Scheme.{u}) (s : RingStage.{u} l)
    (O : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ) :=
  (coefficientHomResolution.{u, u + 1, u}
    (ProEt.topology T) ((s.coefficients l).ring T)).obj O

/-- The signed Hom comparison fixed by the product-component formula (-1)^(m*q).
The theorem's product equations determine this first witness uniquely; no arbitrary
shift automorphism is selected. Source: signed Hom calculation, blueprint step 4
(blueprint: def-sf-verdier-exchange-data). -/
def signedShift (T : Scheme.{u}) (s : RingStage.{u} l)
    (O P : CochainComplex (pbcModules T ((s.coefficients l).ring T)) ℤ) (m : ℤ) :=
  let shift {A : Type (u + 1)} [Category.{u} A] {J : GrothendieckTopology A}
      [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
      (R : Sheaf J CommRingCat.{u + 1})
      (I K : CategoryTheory.SignedDoubleHomCone.Complex.{u + 1, u, u + 1, u + 1} R) (m : ℤ) :
      homComplex.{u + 1, u, u + 1, u + 1} (R := R) (K⟦m⟧) I ≅
        (homComplex.{u + 1, u, u + 1, u + 1} (R := R) K I)⟦-m⟧ :=
    (CategoryTheory.SignedDoubleHomCone.comparison.{u + 1, u, u + 1, u + 1} (R := R) I).choose K m
  shift
    ((s.coefficients l).ring T) (homTarget l T s O) P m

/-- Realization of the dual's shift structure by the actual signed Hom complex.
The component equation fixes the localization comparison, and its CommShift law
transports the fixed sign convention to the ambient category.
Source: blueprint shift clause and proof step 4
(blueprint: def-sf-verdier-exchange-data). -/
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
(blueprint: def-sf-verdier-exchange-data). -/
instance ringInclusionShift (T : Scheme.{u}) (s : RingStage.{u} l) :
    (s.inclusion.{u} l Ω T).CommShift ℤ := by
  cases s <;> infer_instance

/-- Restrict the normalized ambient signed shifts to the constructible categories.
The ordinary pushforward comparison also respects its existing derived shift.
Source: blueprint shift clause (blueprint: def-sf-verdier-exchange-data). -/
structure RingShiftRealization {X Y S : Scheme.{u}} {f : X ⟶ Y}
    {s : RingStage.{u} l}
    {F : Operation.{u} l Ω X Y (s.stage l)} {A : Operation.{u} l Ω Y S (s.stage l)}
    {B : Operation.{u} l Ω X S (s.stage l)} {unit : C.{u} l Ω S (s.stage l)}
    {d : StageData l Ω (s.stage l) F A B unit}
    (r : RingRealization l Ω f s d) (c : StageConclusion l Ω d) where
  modelX : DualShiftModel l X s ((s.inclusion.{u} l Ω X).obj (B.G.obj unit))
  modelY : DualShiftModel l Y s ((s.inclusion.{u} l Ω Y).obj (A.G.obj unit))
  dualX : d.dualX l Ω ⋙ s.inclusion.{u} l Ω X ≅
    (s.inclusion.{u} l Ω X).op ⋙ rawDual l X s ((s.inclusion.{u} l Ω X).obj (B.G.obj unit))
  dualY : d.dualY l Ω ⋙ s.inclusion.{u} l Ω Y ≅
    (s.inclusion.{u} l Ω Y).op ⋙ rawDual l Y s ((s.inclusion.{u} l Ω Y).obj (A.G.obj unit))
  componentsX (M : C.{u} l Ω X (s.stage l)) :
    dualX.hom.app (op M) = r.homX.hom.app (op M, B.G.obj unit)
  componentsY (M : C.{u} l Ω Y (s.stage l)) :
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
(blueprint: def-sf-verdier-exchange-data). -/
structure StageScalar {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation.{u} l Ω X Y s} {As : Operation.{u} l Ω Y S s}
    {Bs : Operation.{u} l Ω X S s} {us : C.{u} l Ω S s}
    {Ft : Operation.{u} l Ω X Y t} {At : Operation.{u} l Ω Y S t}
    {Bt : Operation.{u} l Ω X S t} {ut : C.{u} l Ω S t}
    (ds : StageData l Ω s Fs As Bs us) (dt : StageData l Ω t Ft At Bt ut)
    (TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t) (TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t)
    (TS : C.{u} l Ω S s ⥤ C.{u} l Ω S t) where
  exceptional : FieldComparison.{u} l Ω Fs Ft TX TY
  structureY : FieldComparison.{u} l Ω As At TY TS
  structureX : FieldComparison.{u} l Ω Bs Bt TX TS
  unit : TS.obj us ≅ ut
  tensorX : ds.closedX.tensor ⋙ TX ≅ (TX.prod TX) ⋙ dt.closedX.tensor
  tensorY : ds.closedY.tensor ⋙ TY ≅ (TY.prod TY) ⋙ dt.closedY.tensor
  pull : ds.pull ⋙ TX ≅ TY ⋙ dt.pull
  projection (K : C.{u} l Ω Y s) (M : C.{u} l Ω X s) :
    TY.map (ds.projection K M).hom ≫ tensorY.hom.app (K, Fs.F.obj M) ≫
        dt.closedY.tensor.map (Prod.mkHom (𝟙 _) ((exceptional.q l Ω).hom.app M)) =
      (exceptional.q l Ω).hom.app (ds.closedX.tensor.obj (ds.pull.obj K, M)) ≫
        Ft.F.map (tensorX.hom.app (ds.pull.obj K, M) ≫
          dt.closedX.tensor.map (Prod.mkHom (pull.hom.app K) (𝟙 _))) ≫
        (dt.projection (TY.obj K) (TX.obj M)).hom

/-- The coefficient comparison on omega_X is b_a evaluated at the unit, followed by
its canonical unit identification. Source: blueprint proof step 8
(blueprint: def-sf-verdier-exchange-data). -/
def StageScalar.kappaX {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation.{u} l Ω X Y s} {As : Operation.{u} l Ω Y S s}
    {Bs : Operation.{u} l Ω X S s} {us : C.{u} l Ω S s}
    {Ft : Operation.{u} l Ω X Y t} {At : Operation.{u} l Ω Y S t}
    {Bt : Operation.{u} l Ω X S t} {ut : C.{u} l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
    {TS : C.{u} l Ω S s ⥤ C.{u} l Ω S t} (a : StageScalar l Ω ds dt TX TY TS) :
    TX.obj (Bs.G.obj us) ≅ Bt.G.obj ut :=
  (a.structureX.b l Ω).app us ≪≫ Bt.G.mapIso a.unit

/-- The identical construction on Y. Source: blueprint proof step 8
(blueprint: def-sf-verdier-exchange-data). -/
def StageScalar.kappaY {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation.{u} l Ω X Y s} {As : Operation.{u} l Ω Y S s}
    {Bs : Operation.{u} l Ω X S s} {us : C.{u} l Ω S s}
    {Ft : Operation.{u} l Ω X Y t} {At : Operation.{u} l Ω Y S t}
    {Bt : Operation.{u} l Ω X S t} {ut : C.{u} l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
    {TS : C.{u} l Ω S s ⥤ C.{u} l Ω S t} (a : StageScalar l Ω ds dt TX TY TS) :
    TY.obj (As.G.obj us) ≅ At.G.obj ut :=
  (a.structureY.b l Ω).app us ≪≫ At.G.mapIso a.unit

/-- Scalar comparison for the displayed dual on X, defined by extending evaluation
and transposing it. There is no arbitrary-input internal-Hom isomorphism hypothesis.
Source: blueprint proof step 8 (blueprint: def-sf-verdier-exchange-data). -/
def StageScalar.dualX {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation.{u} l Ω X Y s} {As : Operation.{u} l Ω Y S s}
    {Bs : Operation.{u} l Ω X S s} {us : C.{u} l Ω S s}
    {Ft : Operation.{u} l Ω X Y t} {At : Operation.{u} l Ω Y S t}
    {Bt : Operation.{u} l Ω X S t} {ut : C.{u} l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
    {TS : C.{u} l Ω S s ⥤ C.{u} l Ω S t} (a : StageScalar l Ω ds dt TX TY TS)
    (M : C.{u} l Ω X s) :
    TX.obj ((ds.dualX l Ω).obj (op M)) ⟶ (dt.dualX l Ω).obj (op (TX.obj M)) :=
  dt.closedX.transpose _ (TX.obj M) (Bt.G.obj ut)
    (a.tensorX.inv.app ((ds.dualX l Ω).obj (op M), M) ≫
      TX.map (ds.closedX.evaluation M (Bs.G.obj us)) ≫ (a.kappaX l Ω).hom)

/-- Scalar comparison for the dual on Y, with the same evaluation normalization.
Source: blueprint proof step 8 (blueprint: def-sf-verdier-exchange-data). -/
def StageScalar.dualY {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation.{u} l Ω X Y s} {As : Operation.{u} l Ω Y S s}
    {Bs : Operation.{u} l Ω X S s} {us : C.{u} l Ω S s}
    {Ft : Operation.{u} l Ω X Y t} {At : Operation.{u} l Ω Y S t}
    {Bt : Operation.{u} l Ω X S t} {ut : C.{u} l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
    {TS : C.{u} l Ω S s ⥤ C.{u} l Ω S t} (a : StageScalar l Ω ds dt TX TY TS)
    (M : C.{u} l Ω Y s) :
    TY.obj ((ds.dualY l Ω).obj (op M)) ⟶ (dt.dualY l Ω).obj (op (TY.obj M)) :=
  dt.closedY.transpose _ (TY.obj M) (At.G.obj ut)
    (a.tensorY.inv.app ((ds.dualY l Ω).obj (op M), M) ≫
      TY.map (ds.closedY.evaluation M (As.G.obj us)) ≫ (a.kappaY l Ω).hom)

/-- Direct-image coefficient comparison as the counit-normalized mate of pullback
comparison. Its domain is precisely the specified constructible coefficient domain.
Source: blueprint final coefficient sentence (blueprint: def-sf-verdier-exchange-data). -/
def StageScalar.star {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation.{u} l Ω X Y s} {As : Operation.{u} l Ω Y S s}
    {Bs : Operation.{u} l Ω X S s} {us : C.{u} l Ω S s}
    {Ft : Operation.{u} l Ω X Y t} {At : Operation.{u} l Ω Y S t}
    {Bt : Operation.{u} l Ω X S t} {ut : C.{u} l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
    {TS : C.{u} l Ω S s ⥤ C.{u} l Ω S t} (a : StageScalar l Ω ds dt TX TY TS)
    (M : C.{u} l Ω X s) : TY.obj (ds.star.obj M) ⟶ dt.star.obj (TX.obj M) :=
  dt.adjunction.homEquiv _ _
    (a.pull.inv.app (ds.star.obj M) ≫ TX.map (ds.adjunction.counit.app M))

/-- The two actual coefficient squares: c is preserved under b and the unit, and epsilon
is preserved under the evaluation-defined Hom map and direct-image mate. These equations
cover quotient maps, ramified scalar changes, integral reduction and field descent.
Source: blueprint proof steps 6--8 (blueprint: def-sf-verdier-exchange-data). -/
structure ScalarConclusion {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation.{u} l Ω X Y s} {As : Operation.{u} l Ω Y S s}
    {Bs : Operation.{u} l Ω X S s} {us : C.{u} l Ω S s}
    {Ft : Operation.{u} l Ω X Y t} {At : Operation.{u} l Ω Y S t}
    {Bt : Operation.{u} l Ω X S t} {ut : C.{u} l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
    {TS : C.{u} l Ω S s ⥤ C.{u} l Ω S t} (a : StageScalar l Ω ds dt TX TY TS) : Prop where
  dualizing : TX.map ds.dualizing.hom ≫ (a.kappaX l Ω).hom =
    (a.exceptional.b l Ω).hom.app (As.G.obj us) ≫
      Ft.G.map (a.kappaY l Ω).hom ≫ dt.dualizing.hom
  exchange (M : C.{u} l Ω X s) :
    TY.map (ds.epsilon l Ω M) ≫ a.star l Ω ((ds.dualX l Ω).obj (op M)) ≫
        dt.star.map (a.dualX l Ω M) =
      a.dualY l Ω (Fs.F.obj M) ≫
        (dt.dualY l Ω).map ((a.exceptional.q l Ω).inv.app M).op ≫
        dt.epsilon l Ω (TX.obj M)

/-- Shift compatibility of the evaluation-transposed coefficient arrows, on exactly
these dualizing pairs. This transports the integral signed normalization to fields.
The arrows are not assumed invertible on additional ambient inputs.
Source: blueprint coefficient and shift clauses (blueprint: def-sf-verdier-exchange-data). -/
structure ScalarShifts {X Y S : Scheme.{u}} {s t : Stage.{u} l}
    {Fs : Operation.{u} l Ω X Y s} {As : Operation.{u} l Ω Y S s}
    {Bs : Operation.{u} l Ω X S s} {us : C.{u} l Ω S s}
    {Ft : Operation.{u} l Ω X Y t} {At : Operation.{u} l Ω Y S t}
    {Bt : Operation.{u} l Ω X S t} {ut : C.{u} l Ω S t}
    {ds : StageData l Ω s Fs As Bs us} {dt : StageData l Ω t Ft At Bt ut}
    (cs : StageConclusion l Ω ds) (ct : StageConclusion l Ω dt)
    {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
    {TS : C.{u} l Ω S s ⥤ C.{u} l Ω S t} (b : StageScalar l Ω ds dt TX TY TS) where
  dualX : ds.dualX l Ω ⋙ TX ⟶ TX.op ⋙ dt.dualX l Ω
  dualY : ds.dualY l Ω ⋙ TY ⟶ TY.op ⋙ dt.dualY l Ω
  star : ds.star ⋙ TY ⟶ TX ⋙ dt.star
  componentsX (M : C.{u} l Ω X s) : dualX.app (op M) = b.dualX l Ω M
  componentsY (M : C.{u} l Ω Y s) : dualY.app (op M) = b.dualY l Ω M
  componentsStar (M : C.{u} l Ω X s) : star.app M = b.star l Ω M
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
(blueprint: def-sf-verdier-exchange-data). -/
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
Source: blueprint projection construction (blueprint: def-sf-verdier-exchange-data). -/
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
(blueprint: def-sf-verdier-exchange-data). -/
structure RingProjection {X Y S : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (s : RingStage.{u} l)
    {F : Operation.{u} l Ω X Y (s.stage l)} {A : Operation.{u} l Ω Y S (s.stage l)}
    {B : Operation.{u} l Ω X S (s.stage l)} {unit : C.{u} l Ω S (s.stage l)}
    {d : StageData l Ω (s.stage l) F A B unit}
    (r : RingRealization l Ω f s d) (left : LeftRealization.{u} l Ω c s F) where
  tensorX : ProjectionTensor l X s r.modelX
  tensorY : ProjectionTensor l Y s r.modelY
  tensorBar : ProEtaleTensorModel c.Z ((s.coefficients l).ring c.Z)
  pullComposition : (s.coefficients l).pull (c.i ≫ c.g) =
    proEtaleRingCompositeCoefficients c.i c.g
      ((s.coefficients l).ring Y) ((s.coefficients l).ring c.Z)
      ((s.coefficients l).ring X) ((s.coefficients l).pull c.g) ((s.coefficients l).pull c.i)
  projectionIso (M : C.{u} l Ω X (s.stage l)) (K : C.{u} l Ω Y (s.stage l)) :
    r.modelY.closed.tensor.obj
        ((PurCompactSupport.image (s.coefficients l) c).obj ((s.inclusion.{u} l Ω X).obj M),
          (s.inclusion.{u} l Ω Y).obj K) ≅
      (PurCompactSupport.image (s.coefficients l) c).obj
        (r.modelX.closed.tensor.obj ((s.inclusion.{u} l Ω X).obj M,
          (PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion.{u} l Ω Y).obj K)))
  projectionMap (M : C.{u} l Ω X (s.stage l)) (K : C.{u} l Ω Y (s.stage l)) :
    (projectionIso M K).hom =
      ((PurCompactSupport.projectionMap (s.coefficients l) c
        tensorX.toModel tensorBar tensorY.toModel pullComposition).app
          ((s.inclusion.{u} l Ω X).obj M)).app ((s.inclusion.{u} l Ω Y).obj K)
  normalized (K : C.{u} l Ω Y (s.stage l)) (M : C.{u} l Ω X (s.stage l)) :
    (s.inclusion.{u} l Ω Y).map (d.projection K M).hom =
      left.hom.app (d.closedX.tensor.obj (d.pull.obj K, M)) ≫
        (PurCompactSupport.image (s.coefficients l) c).map
          (r.tensorX.hom.app (d.pull.obj K, M) ≫
            r.modelX.closed.tensor.map (Prod.mkHom (r.pull.hom.app K) (𝟙 _)) ≫
            (r.modelX.symmetric.braiding
              ((PurCompactSupport.pull (s.coefficients l) f).obj ((s.inclusion.{u} l Ω Y).obj K))
              ((s.inclusion.{u} l Ω X).obj M)).hom) ≫
        (projectionIso M K).inv ≫
        (r.modelY.symmetric.braiding
          ((PurCompactSupport.image (s.coefficients l) c).obj ((s.inclusion.{u} l Ω X).obj M))
          ((s.inclusion.{u} l Ω Y).obj K)).hom ≫
        r.modelY.closed.tensor.map (Prod.mkHom (𝟙 _) (left.inv.app M)) ≫
        r.tensorY.inv.app (K, F.F.obj M)

/-- The actual regular-module morphism induced by a map of coefficient sheaves.
Source: blueprint coefficient-unit comparison (blueprint: def-sf-verdier-exchange-data). -/
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
Source: blueprint coefficient-unit comparison (blueprint: def-sf-verdier-exchange-data). -/
def ringUnitRestriction {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (T : Scheme.{u}) :
    ringUnit l T s ⟶ (pbcDerivedRestrict (a.map T)).obj (ringUnit l T t) :=
  (DerivedCategory.singleFunctor _ 0).map (ringUnitRestrictionSheaf l a T) ≫
    ((pbcRestrict (a.map T)).mapDerivedCategorySingleFunctor 0).inv.app
      (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((t.coefficients l).ring T)))

/-- The coefficient-unit extension map is the transpose of the preceding actual map.
Source: blueprint coefficient-unit comparison (blueprint: def-sf-verdier-exchange-data). -/
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
  (Sf : System.{u} l Ω D hl (f := f)) (Sg : System.{u} l Ω D hl (f := g))
  (Sfg : System.{u} l Ω D hl (f := f ≫ g))
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- The already normalized completed compositor expressed through the three recorded
left realizations. Its unique full-subcategory preimage is used before taking its mate.
No maps of normalized towers are recovered merely from their evaluations.
Source: blueprint proof steps 2 and 7; Stacks 0F7J
(blueprint: def-sf-verdier-exchange-data). -/
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

end Geometry

end VerdierExchange
end WeilConjectures
