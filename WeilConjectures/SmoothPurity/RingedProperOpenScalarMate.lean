/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareData
public import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import WeilConjectures.SixFunctors.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.DiagramSiteRealization
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProperOpenClopenProjector
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Scalar change preserves the ringed proper/open mate

Source: the current blueprint, `sec-smooth-purity/sk-prop-sp-composition/`
`sk-prop-sp-composition-comparisons.proof.md`, paragraphs (2)--(3).
(blueprint: lem-pur-ringed-proper-open-scalar-mate).

We use the published composite presentations `J_k = J_s ⋙ J_b` and
`P_r = P_q ⋙ P_s`. Rings on V are restricted first to W_S and then to V;
the canonical restriction compositor identifies this with k-inverse image.
The mode parameter retains both ordinary coefficients and arbitrary strict
inverse systems on the whole vertical diagram sites, before evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedProperOpenScalarMate

/-- Only the geometry, arbitrary structural ring maps, and compatible scalar
maps are input. The structural maps are written in adjoint sectionwise form.
In systems mode these are ring objects on the entire vertical diagram sites.
Source: blueprint (2)--(3), Stacks 03D7, 00Z4 and 0F7B.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
structure SquareInput (m : Mode) where
  V : Scheme.{u}
  W : Scheme.{u}
  S : Scheme.{u}
  T : Scheme.{u}
  k : V ⟶ W
  i : S ⟶ T
  r : V ⟶ S
  p : W ⟶ T
  comm : k ≫ p = r ≫ i
  [k_open : IsOpenImmersion k]
  [i_open : IsOpenImmersion i]
  [k_qc : QuasiCompact k]
  [i_qc : QuasiCompact i]
  [r_proper : IsProper r]
  [p_proper : IsProper p]
  RT : Sheaf (topology m T) CommRingCat.{u + 1}
  RW : Sheaf (topology m W) CommRingCat.{u + 1}
  RT' : Sheaf (topology m T) CommRingCat.{u + 1}
  RW' : Sheaf (topology m W) CommRingCat.{u + 1}
  c : RT ⟶ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology m T) (topology m W)).obj RW
  c' : RT' ⟶ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology m T) (topology m W)).obj RW'
  aT : RT ⟶ RT'
  aW : RW ⟶ RW'
  coefficients : c ≫ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology m T) (topology m W)).map aW = aT ≫ c'

attribute [instance] SquareInput.k_open SquareInput.i_open SquareInput.k_qc SquareInput.i_qc
  SquareInput.r_proper SquareInput.p_proper

/-- The canonical Cartesian open square W_S inside the noncartesian input.
Source: Stacks 0F7B and the published input constructor.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def SquareInput.base {m : Mode} (d : SquareInput.{u} m) : OpenTensorNormalization.Input m :=
  ClopenComparisonTensorSquare.input m d.p d.i d.RT d.RW d.c

/-- The identical Cartesian geometry with the changed coefficient rings.
Source: blueprint (2) (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def SquareInput.changed {m : Mode} (d : SquareInput.{u} m) :
    OpenTensorNormalization.Input m :=
  ClopenComparisonTensorSquare.input m d.p d.i d.RT' d.RW' d.c'

/-- The lift (k,r), without a cartesianness assumption on Q.
Source: Stacks 0F7B (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
abbrev SquareInput.s {m : Mode} (d : SquareInput.{u} m) :
    d.V ⟶ CategoryTheory.Limits.pullback d.p d.i :=
  AlgebraicGeometry.ProEtale.StrictTower.squareLift d.k d.r d.p d.i d.comm

/-- The existing clopen-lift instance, obtained by typeclass inference from
properness and openness. Source: Stacks 0F7B.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
instance s_open {m : Mode} (d : SquareInput.{u} m) : IsOpenImmersion d.s := inferInstance

/-- Literal restriction of a coefficient map to an open subscheme.
Source: Stacks 0F6Z (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def restrictMap {m : Mode} {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {R R' : Sheaf (topology m X) CommRingCat.{u + 1}} (a : R ⟶ R') :
    restrictRing m j R ⟶ restrictRing m j R' :=
  ((openInclusion m j).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology m U) (topology m X)).map a

/-- The existing restriction of scalars on section modules.
Source: Stacks 03D7 (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
abbrev scalarRestriction {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ R') :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)

/-- A presentation of actual derived scalar extension, with ordinary unit
1 tensor x. The existing model retains its universal counit and K-flat law.
Source: Stacks 06YY, 03EL and 07A6.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
structure Scalar {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ R') where
  model : DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
    (J := J) (O := R) (S := R') a
  ordinaryAdjunction : model.E ⊣ scalarRestriction a
  unit : ∀ (M : Mod R) (U : Cᵒᵖ) (x : M.val.obj U),
    (ordinaryAdjunction.unit.app M).val.app U x =
      (eqToHom (model.obj_eq M).symm).val.app U
        (SuccessiveDerivedQuotient.pure a M U 1 x)

/-- The right-derived partner of a specified module pullback, including the
K-flat/K-injective Hom formula fixing its derived adjunction.
Source: Stacks 07A4, 07A6 and 0D6E.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
structure RightDerived {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    {V : Mod S ⥤ Mod R} (p : Pullback R S V) where
  [additive : V.Additive]
  functor : Der S ⥤ Der R
  eta : V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso (Mod S) (.up ℤ))
  injective : ∀ I : CochainComplex (Mod S) ℤ, I.IsKInjective → IsIso (eta.app I)
  adjunction : p.derived ⊣ functor
  normalized : ∀ (P : CochainComplex (Mod R) ℤ) (I : CochainComplex (Mod S) ℤ),
    resolving R P → I.IsKInjective →
    ∀ b : P ⟶ (V.mapHomologicalComplex (.up ℤ)).obj I,
      (adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).symm
          (DerivedCategory.Q.map b ≫ eta.app I) =
        derivedPullbackComplexComparison p.ordinary p.derived p.epsilon P ≫
          DerivedCategory.Q.map
            (((p.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm b)

/-- Balanced scalar/pullback comparison, fixed by identity on direct-image
sections, ordinary adjunction conjugation, and its K-flat representative square.
Source: Stacks 03EL, 0D6D and 0G7E.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
structure Balance {m : Mode} {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R R' : Sheaf (topology m Y) CommRingCat.{u + 1}}
    {S S' : Sheaf (topology m X) CommRingCat.{u + 1}}
    {c : R ⟶ ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj S}
    {c' : R' ⟶ ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj S'}
    {aY : R ⟶ R'} {aX : S ⟶ S'}
    (p : Pullback R S (direct m f R S c))
    (p' : Pullback R' S' (direct m f R' S' c')) (tY : Scalar aY) (tX : Scalar aX) where
  right : direct m f R' S' c' ⋙ scalarRestriction aY ≅
    scalarRestriction aX ⋙ direct m f R S c
  sections : ∀ (N : Mod S') (U : (Site m Y)ᵒᵖ),
    HEq (fun x => ((right.hom.app N).val.app U) x)
      (fun x : N.val.obj ((baseChange m f).op.obj U) => x)
  ordinary : tY.model.E ⋙ p'.ordinary ≅ p.ordinary ⋙ tX.model.E
  ordinary_eq : ordinary =
    (tY.ordinaryAdjunction.comp p'.adjunction).leftAdjointUniq
      ((p.adjunction.comp tX.ordinaryAdjunction).ofNatIsoRight right.symm)
  derived : tY.model.T ⋙ p'.derived ≅ p.derived ⋙ tX.model.T
  representative : ∀ (P : CochainComplex (Mod R) ℤ), resolving R P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        tX.model.T.map
          (derivedPullbackComplexComparison p.ordinary p.derived p.epsilon P) ≫
        tX.model.ε.app ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
      p'.derived.map (tY.model.ε.app P) ≫
        derivedPullbackComplexComparison p'.ordinary p'.derived p'.epsilon
          ((tY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)

/-- Scalar/open comparison, fixed by restricted sections and by exact
localization of its ordinary adjunction conjugate on K-flat representatives.
Source: Stacks 03DI, 03DJ and 0GL1.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
structure OpenBalance {m : Mode} {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {R R' : Sheaf (topology m X) CommRingCat.{u + 1}} {a : R ⟶ R'}
    (e : OpenExtension m j R) (e' : OpenExtension m j R')
    (tX : Scalar a) (tU : Scalar (restrictMap j a)) where
  right : OpenTensorNormalization.restrict m j R' ⋙ scalarRestriction (restrictMap j a) ≅
    scalarRestriction a ⋙ OpenTensorNormalization.restrict m j R
  sections : ∀ (N : Mod R') (W : (Site m U)ᵒᵖ),
    HEq (fun x => ((right.hom.app N).val.app W) x)
      (fun x : N.val.obj ((openInclusion m j).op.obj W) => x)
  ordinary : e.ordinary ⋙ tX.model.E ≅ tU.model.E ⋙ e'.ordinary
  ordinary_eq : ordinary =
    (e.adjunction.comp tX.ordinaryAdjunction).leftAdjointUniq
      ((tU.ordinaryAdjunction.comp e'.adjunction).ofNatIsoRight right)
  derived : e.ordinary.mapDerivedCategory ⋙ tX.model.T ≅
    tU.model.T ⋙ e'.ordinary.mapDerivedCategory
  representative : ∀ P : CochainComplex (Mod (restrictRing m j R)) ℤ,
    resolving (restrictRing m j R) P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        e'.ordinary.mapDerivedCategory.map (tU.model.ε.app P) ≫
        e'.ordinary.mapDerivedCategoryFactors.hom.app
          ((tU.model.E.mapHomologicalComplex (.up ℤ)).obj P) =
      tX.model.T.map (e.ordinary.mapDerivedCategoryFactors.hom.app P) ≫
        tX.model.ε.app ((e.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P)

/-- Canonical presentations for the original coefficients, with the published
open-normalized beta and clopen reverse exact adjunction. Its counit is the
inverse open unit, so its unit is the projector diag(1,0).
Source: Stacks 0F7B, 04TS and 07A6.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
structure Presentation {m : Mode} (d : SquareInput.{u} m) where
  site : SiteSquare d.base
  opens : OpenTensorNormalization.Operations d.base site
  assertion : OpenTensorNormalization.Assertion opens
  clopen : ClopenComparisonTensorSquare.Data opens d.s
  pRight : RightDerived opens.gPull
  qRight : RightDerived opens.gUPull

/-- The same canonical presentations for the changed coefficients.
Source: blueprint (2) (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
structure ChangedPresentation {m : Mode} (d : SquareInput.{u} m) where
  site : SiteSquare d.changed
  opens : OpenTensorNormalization.Operations d.changed site
  assertion : OpenTensorNormalization.Assertion opens
  clopen : ClopenComparisonTensorSquare.Data opens d.s
  pRight : RightDerived opens.gPull
  qRight : RightDerived opens.gUPull

/-- Scalar presentations at all five vertices. The scalar/restriction map at
s is fixed as the open-adjunction mate of delta_s. These are canonical
presentation witnesses, not a scalar compatibility hypothesis on alpha.
Source: Stacks 06YY, 0GL1, 0D6D and 07A7.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
structure Comparisons {m : Mode} {d : SquareInput.{u} m}
    (o : Presentation d) (o' : ChangedPresentation d) where
  scalarT : Scalar d.aT
  scalarW : Scalar d.aW
  scalarS : Scalar (restrictMap d.i d.aT)
  scalarH : Scalar (restrictMap (pullback.fst d.p d.i) d.aW)
  scalarV : Scalar (restrictMap d.s (restrictMap (pullback.fst d.p d.i) d.aW))
  lambdaP : Balance d.p o.opens.gPull o'.opens.gPull scalarT scalarW
  lambdaQ : Balance (pullback.snd d.p d.i) o.opens.gUPull o'.opens.gUPull scalarS scalarH
  deltaI : OpenBalance d.i o.opens.opens.extension o'.opens.opens.extension scalarT scalarS
  deltaB : OpenBalance (pullback.fst d.p d.i) o.opens.opens.extension'
    o'.opens.opens.extension' scalarW scalarH
  deltaS : OpenBalance d.s o.clopen.extensionS o'.clopen.extensionS scalarH scalarV
  lambdaS : scalarH.model.T ⋙
      (OpenTensorNormalization.restrict m d.s
        (restrictRing m (pullback.fst d.p d.i) d.RW')).mapDerivedCategory ≅
    (OpenTensorNormalization.restrict m d.s
      (restrictRing m (pullback.fst d.p d.i) d.RW)).mapDerivedCategory ⋙ scalarV.model.T
  lambdaS_mate : lambdaS.inv =
    (mateEquiv (exactDerivedAdjunction o.clopen.extensionS.adjunction)
      (exactDerivedAdjunction o'.clopen.extensionS.adjunction)
      (TwoSquare.mk _ _ _ _ deltaS.derived.inv)).natTrans

/-- The canonical consecutive-open presentation of k-extension by zero.
Source: Stacks 03DI (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
abbrev Presentation.Jk {m : Mode} {d : SquareInput.{u} m} (o : Presentation d) :=
  o.clopen.extensionS.ordinary.mapDerivedCategory ⋙ o.opens.opens.jShriek'

/-- The changed consecutive-open extension.
Source: Stacks 03DI (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
abbrev ChangedPresentation.Jk {m : Mode} {d : SquareInput.{u} m}
    (o : ChangedPresentation d) :=
  o.clopen.extensionS.ordinary.mapDerivedCategory ⋙ o.opens.opens.jShriek'

/-- The canonical derived adjunction for r=qs in the composite presentation.
Source: Stacks 0D6D and 04TS.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
abbrev Presentation.rAdj {m : Mode} {d : SquareInput.{u} m} (o : Presentation d) :=
  o.qRight.adjunction.comp (exactDerivedAdjunction o.clopen.rightAdjunction)

/-- The changed composite proper adjunction.
Source: Stacks 0D6D and 04TS.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
abbrev ChangedPresentation.rAdj {m : Mode} {d : SquareInput.{u} m}
    (o : ChangedPresentation d) :=
  o.qRight.adjunction.comp (exactDerivedAdjunction o.clopen.rightAdjunction)

/-- Alpha is exactly beta followed by J_b of the clopen projector. The
associators explicitly realize the canonical two final compositors.
Source: Stacks 0F7B (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def Presentation.alpha {m : Mode} {d : SquareInput.{u} m} (o : Presentation d) :
    o.opens.opens.jShriek ⋙ o.opens.gPull.derived ⟶
      (o.opens.gUPull.derived ⋙
        (OpenTensorNormalization.restrict m d.s
          (restrictRing m (pullback.fst d.p d.i) d.RW)).mapDerivedCategory) ⋙ o.Jk :=
  o.assertion.beta.hom ≫
    Functor.whiskerRight (Functor.rightUnitor _).inv _ ≫
    Functor.whiskerRight (Functor.whiskerLeft _ o.clopen.rho) _ ≫
    (Functor.isoWhiskerRight (Functor.associator _ _ _).symm _).hom ≫
    (Functor.associator _ _ _).hom

/-- Alpha for the changed coefficients, with the same normalized factors.
Source: Stacks 0F7B (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def ChangedPresentation.alpha {m : Mode} {d : SquareInput.{u} m}
    (o : ChangedPresentation d) :
    o.opens.opens.jShriek ⋙ o.opens.gPull.derived ⟶
      (o.opens.gUPull.derived ⋙
        (OpenTensorNormalization.restrict m d.s
          (restrictRing m (pullback.fst d.p d.i) d.RW')).mapDerivedCategory) ⋙ o.Jk :=
  o.assertion.beta.hom ≫
    Functor.whiskerRight (Functor.rightUnitor _).inv _ ≫
    Functor.whiskerRight (Functor.whiskerLeft _ o.clopen.rho) _ ≫
    (Functor.isoWhiskerRight (Functor.associator _ _ _).symm _).hom ≫
    (Functor.associator _ _ _).hom

/-- The proper/open mate is the actual unit--alpha--counit transformation.
Source: Stacks 07A7 (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def Presentation.gamma {m : Mode} {d : SquareInput.{u} m} (o : Presentation d) :=
  (mateEquiv o.rAdj o.pRight.adjunction (TwoSquare.mk _ _ _ _ o.alpha)).natTrans

/-- The changed proper/open mate.
Source: Stacks 07A7 (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def ChangedPresentation.gamma {m : Mode} {d : SquareInput.{u} m}
    (o : ChangedPresentation d) :=
  (mateEquiv o.rAdj o.pRight.adjunction (TwoSquare.mk _ _ _ _ o.alpha)).natTrans

/-- Lambda_r is the balanced comparison for q followed by that for s.
Source: Stacks 0D6D (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def Comparisons.lambdaR {m : Mode} {d : SquareInput.{u} m}
    {o : Presentation d} {o' : ChangedPresentation d} (c : Comparisons o o') :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight c.lambdaQ.derived _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ c.lambdaS ≪≫
    (Functor.associator _ _ _).symm

/-- Chi_p is exactly the proper-adjunction mate of the balanced comparison.
Source: Stacks 07A7 (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def Comparisons.chiP {m : Mode} {d : SquareInput.{u} m}
    {o : Presentation d} {o' : ChangedPresentation d} (c : Comparisons o o') :=
  (mateEquiv o.pRight.adjunction o'.pRight.adjunction
    (TwoSquare.mk _ _ _ _ c.lambdaP.derived.hom)).natTrans

/-- Chi_r is its composite-proper counterpart, with no invertibility assertion.
Source: Stacks 07A7 (blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def Comparisons.chiR {m : Mode} {d : SquareInput.{u} m}
    {o : Presentation d} {o' : ChangedPresentation d} (c : Comparisons o o') :=
  (mateEquiv o.rAdj o'.rAdj (TwoSquare.mk _ _ _ _ c.lambdaR.hom)).natTrans

/-- The scalar/consecutive-open comparison, explicitly delta_b followed by
J_b' of delta_s. Source: Stacks 03DI and 0GL1.
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def Comparisons.deltaK {m : Mode} {d : SquareInput.{u} m}
    {o : Presentation d} {o' : ChangedPresentation d} (c : Comparisons o o') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ c.deltaB.derived ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c.deltaS.derived _ ≪≫
    Functor.associator _ _ _

/-- Equality of the two paths on the whole ordinary unbounded derived
category, naturally in M. In systems mode it is an equality of whole-system
natural transformations before any evaluation or total inverse limit.
Source: blueprint (2)--(3).
(blueprint: lem-pur-ringed-proper-open-scalar-mate). -/
def Law {m : Mode} {d : SquareInput.{u} m} {o : Presentation d}
    {o' : ChangedPresentation d} (c : Comparisons o o') : Prop :=
  Functor.whiskerRight o.gamma c.scalarT.model.T ≫
      Functor.whiskerLeft o.Jk c.chiP ≫
      Functor.whiskerRight c.deltaK.hom o'.pRight.functor =
    Functor.whiskerLeft _ c.deltaI.derived.hom ≫
      Functor.whiskerRight c.chiR o'.opens.opens.jShriek ≫
      Functor.whiskerLeft c.scalarV.model.T o'.gamma

/-- Scalar change preserves the ringed proper/open mate, for ordinary
coefficients and arbitrary compatible strict inverse systems. All normalized
presentations exist, and every such presentation satisfies the equation.
No flatness, boundedness, constructibility, completeness, cartesianness, or
invertibility of either proper mate is assumed.
Source: current blueprint comparisons proof, paragraphs (2)--(3).
(blueprint: lem-pur-ringed-proper-open-scalar-mate).

Proof: the balanced ordinary tensor comparison commutes with composition;
its K-flat representative square gives the derived equation. The inverse
open base-change words have the same open-unit transpose, which proves the
scalar beta equation. The clopen reverse adjunction unit is diag(1,0) under
the two-piece exact decomposition. Derived scalar extension is componentwise,
so it preserves that projector, including empty pieces. Paste the two
squares with the consecutive-open scalar comparison to obtain the scalar
alpha equation. Proper-adjunction mate pasting now yields Law: the mates
of lambda are exactly chi, and the mate of alpha is gamma. For systems all
these constructions and the clopen decomposition take place on the vertical
diagram sites and commute with every semilinear transition. No evaluation or
inverse-limit test for equality is used. -/
theorem scalar_mate (m : Mode) (d : SquareInput.{u} m) :
    (∃ (o : Presentation d) (o' : ChangedPresentation d), Nonempty (Comparisons o o')) ∧
      ∀ (o : Presentation d) (o' : ChangedPresentation d) (c : Comparisons o o'), Law c := by
  sorry

end SheafOfModules.RingedProperOpenScalarMate
