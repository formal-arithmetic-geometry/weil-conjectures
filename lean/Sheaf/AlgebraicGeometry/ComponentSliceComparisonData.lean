/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.AlgebraicGeometry.ComponentPullbackUnboundedEvaluation
public import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Normalized component pullback on slices

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), equation (4.2);
Stacks Project, Tags 08JA, 08JB and 08J9
(blueprint: def-sfb-component-slice-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v d z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- The genuine coefficient-module category on a profinite slice.
Source: HRS Section 3 (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev Modules (S : Profinite.{u}) :=
  Mod (Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1})
    (profiniteCoefficient Λ.X S)

/-- The underlying restriction along a continuous map of profinite bases.
Source: Stacks 03DH (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev restrictSheaf {S T : Profinite.{u}} (f : T ⟶ S) :=
  (coherentTopology Profinite.{u}).overMapPullback Ab.{u + 1} f

/-- Coefficient transport for literal sectionwise restriction.
Source: Stacks 03DH (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev RestrictionCoefficient {S T : Profinite.{u}} (f : T ⟶ S) :=
  (restrictSheaf f).mapMon.obj (Mon.mk (profiniteCoefficient Λ.X S)) ≅
    Mon.mk (profiniteCoefficient Λ.X T)

/-- Actual restriction of modules, transporting the canonical restricted coefficient.
Source: Stacks 03DH (blueprint: def-sfb-component-slice-comparison-data). -/
def restrictModules {S T : Profinite.{u}} (f : T ⟶ S)
    [(restrictSheaf f).Braided]
    (b : RestrictionCoefficient Λ f) : Modules Λ S ⥤ Modules Λ T :=
  (restrictSheaf f).mapMod (profiniteCoefficient Λ.X S) ⋙ Mod.comap b.inv.hom

/-- Canonical restriction infrastructure. The strong structure extends the existing
sectionwise lax tensor maps, and the coefficient comparison is identity on sections.
Source: Stacks 03DH, 03EL
(blueprint: def-sfb-component-slice-comparison-data). -/
structure RestrictionData {S T : Profinite.{u}} (f : T ⟶ S) where
  braided : (restrictSheaf f).Braided
  lax_eq : HEq braided.toMonoidal.toLaxMonoidal
    (inferInstance : (restrictSheaf f).LaxMonoidal)
  colimits : PreservesFiniteColimits (restrictSheaf f)
  coefficient : letI := braided; RestrictionCoefficient Λ f
  coefficient_sections : ∀ (V : Over T) (x :
      (profiniteCoefficient Λ.X S).obj.obj (op ((Over.map f).obj V))),
    HEq (coefficient.hom.hom.hom.app (op V) x) x
  moduleLimits : letI := braided
    PreservesFiniteLimits (restrictModules Λ f coefficient)
  moduleColimits : letI := braided
    PreservesFiniteColimits (restrictModules Λ f coefficient)
  moduleMonoidal : letI := braided; (restrictModules Λ f coefficient).Monoidal
  tensor_normalization : letI := braided; letI := moduleMonoidal
    ∀ M N : Modules Λ S,
      Mod.tensorObjπ ((restrictModules Λ f coefficient).obj M)
          ((restrictModules Λ f coefficient).obj N) ≫
        (Functor.LaxMonoidal.μ (restrictModules Λ f coefficient) M N).hom =
      Functor.LaxMonoidal.μ (restrictSheaf f) M.X N.X ≫
        (restrictSheaf f).map (Mod.tensorObjπ M N)


namespace RestrictionData
variable {Λ} {S T : Profinite.{u}} {f : T ⟶ S} (r : RestrictionData Λ f)
/-- Literal restriction on modules with its specified scalar identification.
Source: Stacks 03DH (blueprint: def-sfb-component-slice-comparison-data). -/
def modules := letI := r.braided; restrictModules Λ f r.coefficient
/-- Finite limits are computed on underlying restricted abelian sheaves.
Source: Stacks 03DH (blueprint: def-sfb-component-slice-comparison-data). -/
instance limits : PreservesFiniteLimits r.modules := r.moduleLimits
/-- Exactness of restriction on module sheaves.
Source: Stacks 03DJ (blueprint: def-sfb-component-slice-comparison-data). -/
instance colimitsModules : PreservesFiniteColimits r.modules := r.moduleColimits
/-- The tensor structure fixed by the sectionwise balanced tensor equation.
Source: Stacks 03EL (blueprint: def-sfb-component-slice-comparison-data). -/
instance monoidal : r.modules.Monoidal := r.moduleMonoidal
/-- Additivity of exact restriction.
Source: Stacks 03DJ (blueprint: def-sfb-component-slice-comparison-data). -/
instance additive : r.modules.Additive := Functor.additive_of_preserves_binary_products _
/-- The induced functor on all unbounded complexes localized at quasi-isomorphisms.
Source: Stacks 015F (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev derived := r.modules.mapDerivedCategory
end RestrictionData

/-- The component pullback data, with the coefficient factorization fixed at Lambda.
This packages the existing evaluation theorem's data without choosing a new inverse image.
Source: HRS (4.1)--(4.2)
(blueprint: def-sfb-component-slice-comparison-data). -/
structure PullbackData (W : Scheme.{u}) [IsAffine W] where
  continuous : (componentTests W).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
    (Scheme.ProEt.topology W)
  braided : letI := continuous; (componentInverse W).Braided
  limits : letI := continuous; PreservesFiniteLimits (componentInverse W)
  colimits : letI := continuous; PreservesFiniteColimits (componentInverse W)
  coefficient : letI := continuous; letI := braided
    (componentInverse W).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace W))) ≅
        Mon.mk (condensedRingObj Λ.X W)
  factorization : letI := continuous; letI := braided
    ∃ beta : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
        (affineComponentSpace W) ⋙ componentInverse W ≅ upperStarFromPoint W,
      NatTrans.IsMonoidal beta.hom ∧ coefficient.hom.hom = beta.hom.app Λ.X
  evaluation : letI := continuous; letI := braided
    letI := limits; letI := colimits
    ComponentPullbackUnboundedEvaluation Λ W coefficient

namespace PullbackData
variable {Λ} {W : Scheme.{u}} [IsAffine W] (d : PullbackData Λ W)
/-- The already defined module pullback, with its recorded coefficient identification.
Source: HRS (4.1) (blueprint: def-sfb-component-slice-comparison-data). -/
def modules :=
  letI := d.continuous; letI := d.braided; letI := d.limits; letI := d.colimits
  componentModules Λ.X W d.coefficient
/-- Exact component pullback preserves finite limits.
Source: HRS Section 3 (blueprint: def-sfb-component-slice-comparison-data). -/
instance modulesLimits : PreservesFiniteLimits d.modules :=
  letI := d.continuous; letI := d.braided; letI := d.limits; letI := d.colimits
  inferInstanceAs (PreservesFiniteLimits (componentModules Λ.X W d.coefficient))
/-- Exact component pullback preserves finite colimits.
Source: HRS Section 3 (blueprint: def-sfb-component-slice-comparison-data). -/
instance modulesColimits : PreservesFiniteColimits d.modules :=
  letI := d.continuous; letI := d.braided; letI := d.limits; letI := d.colimits
  inferInstanceAs (PreservesFiniteColimits (componentModules Λ.X W d.coefficient))
/-- Its ordinary balanced tensor comparison is the mapMod/comap comparison.
Source: Stacks 03EL (blueprint: def-sfb-component-slice-comparison-data). -/
instance modulesMonoidal : d.modules.Monoidal :=
  letI := d.continuous; letI := d.braided; letI := d.limits; letI := d.colimits
  inferInstanceAs (componentModules Λ.X W d.coefficient).Monoidal
/-- Additivity of the existing module pullback.
Source: HRS Section 3 (blueprint: def-sfb-component-slice-comparison-data). -/
instance modulesAdditive : d.modules.Additive :=
  letI := d.continuous; letI := d.braided; letI := d.limits; letI := d.colimits
  inferInstanceAs (componentModules Λ.X W d.coefficient).Additive
/-- The ordinary unbounded termwise derived component pullback.
Source: HRS Section 3 (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev derived := d.modules.mapDerivedCategory
end PullbackData

/-- The actual component map attached to an affine pro-etale test.
Source: HRS (4.2) (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev componentMap (W : Scheme.{u}) [IsAffine W] (U : W.ProEt) [IsAffine U.left] :
    affineComponentSpace U.left ⟶ affineComponentSpace W :=
  (componentAffineObject W U).hom

/-- Monoidality of a comparison square, including its coefficient-unit equation.
Factoring this generic predicate keeps large sheaf tensor structures opaque.
Source: Stacks 03EL (blueprint: def-sfb-component-slice-comparison-data). -/
def MonoidalSquare {C : Type c} {D : Type d} {E : Type v} {H : Type z}
    [Category C] [Category D] [Category E] [Category H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    (F : C ⥤ D) (G : E ⥤ H) (R : C ⥤ E) (S : D ⥤ H)
    [F.Monoidal] [G.Monoidal] [R.Monoidal] [S.Monoidal]
    (e : F ⋙ S ≅ R ⋙ G) : Prop := NatTrans.IsMonoidal e.hom

section Generic
variable {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]

/-- The usual unbounded derived sections, from the coefficient unit.
Source: Stacks 07A5 and 08JA
(blueprint: def-sfb-component-slice-comparison-data). -/
abbrev sections : C ⥤ Ab.{u + 1} := preadditiveCoyoneda.obj (op (𝟙_ C))
/-- Right derived global sections, with no cohomological truncation.
Source: Stacks 08JA (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev derivedSections : DerivedCategory C ⥤ DerivedCategory Ab.{u + 1} :=
  (sections (C := C)).rightDerivedFunctor

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.Monoidal] [PreservesColimitsOfSize.{0, 0} F]

/-- The tensor structure on exact unbounded pullback is fixed on all complex
representatives, including its ordinary coefficient unit. This is the standard
localization normalization, written generically for the four functors of the square.
Source: Stacks 07A4, 015F
(blueprint: def-sfb-component-slice-comparison-data). -/
def DerivedMonoidalNormalization [F.mapDerivedCategory.Monoidal] : Prop :=
  (∀ P Q : HomotopyCategory C (.up ℤ),
    Functor.LaxMonoidal.μ F.mapDerivedCategory
        (DerivedCategory.Qh.obj P) (DerivedCategory.Qh.obj Q) ≫
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Qh P Q) ≫
      F.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
      DerivedCategory.Qh.map
        (Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) P Q) =
    (F.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((F.mapHomotopyCategory (.up ℤ)).obj P)
        ((F.mapHomotopyCategory (.up ℤ)).obj Q)) ∧
  (Functor.LaxMonoidal.ε F.mapDerivedCategory ≫
      F.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
      F.mapDerivedCategoryFactorsh.hom.app (𝟙_ _) ≫
      DerivedCategory.Qh.map
        (Functor.OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) =
    Functor.LaxMonoidal.ε DerivedCategory.Qh)

/-- The actual evaluation-adjoint comparison. Its uncurrying is pulled-back
counit after the inverse tensorator, by the definition of ihomComparison.
Source: Stacks 08J9 (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev homComparison [F.mapDerivedCategory.Monoidal] (K L : DerivedCategory C) :=
  (Functor.LaxMonoidal.ihomComparison F.mapDerivedCategory K).natTrans.app L

/-- Apply the functor to a shifted morphism and use its termwise shift comparison.
Source: Stacks 015F (blueprint: def-sfb-component-slice-comparison-data). -/
def shiftedHomMap (K L : DerivedCategory C) (n : ℤ) (f : K ⟶ L⟦n⟧) :
    F.mapDerivedCategory.obj K ⟶ (F.mapDerivedCategory.obj L) ⟦n⟧ :=
  F.mapDerivedCategory.map f ≫ (F.mapDerivedCategory.commShiftIso n).hom.app L

/-- The native derived coefficient unit agrees with the ordinary unit in degree zero.
Source: Stacks 0FPT (blueprint: def-sfb-component-slice-comparison-data). -/
def unitDerivedIso : 𝟙_ (DerivedCategory C) ≅
    (DerivedCategory.singleFunctor C 0).obj (𝟙_ C) :=
  (DerivedCategory.singleFunctorObjUnitIso C).symm

variable [PreservesFiniteLimits (sections (C := C))]
  [PreservesFiniteColimits (sections (C := C))]

/-- The class of the identity section of the coefficient unit, through the canonical
exact-section and degree-zero comparisons.
Source: Stacks 08JA (blueprint: def-sfb-component-slice-comparison-data). -/
def unitClass : (DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
    ((derivedSections (C := C)).obj (𝟙_ (DerivedCategory C))) :=
  ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).map
    ((derivedSections (C := C)).map (unitDerivedIso (C := C)).inv))
    (((DerivedCategory.homologyFunctor Ab.{u + 1} 0).map
      ((sections (C := C)).singleFunctorCompRightDerivedFunctorIso.inv.app (𝟙_ C)))
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso Ab.{u + 1} 0).inv.app
        ((sections (C := C)).obj (𝟙_ C))) (𝟙 (𝟙_ C))))

/-- Turn a derived section of degree n into the corresponding cohomology class of
actual derived sections. Every comparison is canonical and induced by exact evaluation.
Source: Stacks 08JA (blueprint: def-sfb-component-slice-comparison-data). -/
def sectionClass (X : DerivedCategory C) (n : ℤ)
    (a : 𝟙_ (DerivedCategory C) ⟶ X⟦n⟧) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((derivedSections (C := C)).obj X) :=
  ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).shiftIso n 0 n (add_zero n)).hom.app
    ((derivedSections (C := C)).obj X)
    (((DerivedCategory.homologyFunctor Ab.{u + 1} 0).map
      ((derivedSections (C := C)).map a ≫
        ((derivedSections (C := C)).commShiftIso n).hom.app X)) (unitClass (C := C)))

/-- The shift structure on internal Hom is the right-adjoint mate of tensor's
standard signed shift structure.
Source: Stacks 08J9 (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev homShift (K : DerivedCategory C) : (ihom K).CommShift ℤ :=
  (ihom.adjunction K).rightAdjointCommShift ℤ

/-- Transpose a degree-n section, using the unit and the canonical shift mate.
Source: Stacks 08JA, 08J9
(blueprint: def-sfb-component-slice-comparison-data). -/
def sectionTranspose (K L : DerivedCategory C) (n : ℤ)
    (a : 𝟙_ (DerivedCategory C) ⟶ ((ihom K).obj L) ⟦n⟧) : K ⟶ L⟦n⟧ :=
  letI := homShift K
  (ρ_ K).inv ≫ MonoidalClosed.uncurry (a ≫ ((ihom K).commShiftIso n).inv.app L)

/-- Canonical derived-Hom sections identification, fixed on every actual section by
evaluation and transposition; no unnormalized equivalence of groups is accepted.
Source: Stacks 08JA (blueprint: def-sfb-component-slice-comparison-data). -/
structure HomSectionsIdentification where
  equiv : ∀ (K L : DerivedCategory C) (n : ℤ),
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((derivedSections (C := C)).obj ((ihom K).obj L)) ≃+ (K ⟶ L⟦n⟧)
  normalization : ∀ (K L : DerivedCategory C) (n : ℤ)
    (a : 𝟙_ (DerivedCategory C) ⟶ ((ihom K).obj L) ⟦n⟧),
    equiv K L n (sectionClass ((ihom K).obj L) n a) = sectionTranspose K L n a

/-- Pullback of global sections with its unit formula, and its entire unbounded
right-derived comparison normalized on every homotopy representative.
Source: HRS (4.2), Stacks 015F
(blueprint: def-sfb-component-slice-comparison-data). -/
structure SectionComparison where
  ordinary : sections (C := C) ≅ F ⋙ sections (C := D)
  ordinary_formula : ∀ (M : C) (a : 𝟙_ C ⟶ M),
    ordinary.hom.app M a = Functor.LaxMonoidal.ε F ≫ F.map a
  derived : derivedSections (C := C) ≅ F.mapDerivedCategory ⋙ derivedSections (C := D)
  derived_formula : ∀ P : HomotopyCategory C (.up ℤ),
    (sections (C := C)).rightDerivedFunctorUnit.app P ≫
        derived.hom.app (DerivedCategory.Qh.obj P) =
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory ordinary.hom (.up ℤ)).app P) ≫
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit F (sections (C := D))).app P

/-- The map of full derived sections obtained by pulling back and then transposing
pulled-back evaluation. This is an actual morphism, with fixed comparisons.
Source: HRS (4.2), Stacks 08J9
(blueprint: def-sfb-component-slice-comparison-data). -/
def localSectionsComparison [F.mapDerivedCategory.Monoidal] (e : SectionComparison F)
    (K L : DerivedCategory C) :
    (derivedSections (C := C)).obj ((ihom K).obj L) ⟶
      (derivedSections (C := D)).obj
        ((ihom (F.mapDerivedCategory.obj K)).obj (F.mapDerivedCategory.obj L)) :=
  e.derived.hom.app ((ihom K).obj L) ≫
    (derivedSections (C := D)).map (homComparison F K L)

/-- Transport an internal Hom along a specified comparison of its two inputs.
Source: Stacks 08JB (blueprint: def-sfb-component-slice-comparison-data). -/
def transportHom {E : Type z} [Category.{u + 1} E]
    [MonoidalCategory E] [MonoidalClosed E]
    (P Q : DerivedCategory C ⥤ E) (e : P ≅ Q) (K L : DerivedCategory C) :
    (ihom (P.obj K)).obj (P.obj L) ⟶ (ihom (Q.obj K)).obj (Q.obj L) :=
  (MonoidalClosed.pre (e.inv.app K)).app (P.obj L) ≫
    (ihom (Q.obj K)).map (e.hom.app L)

end Generic

/-- The normalized exact-functor square, including entire derived sections and
its evaluation-adjoint map in every cohomological degree. The four functors and
all their localization comparisons are supplied, rather than replaced by models.
Source: HRS (4.2), Stacks 08JA, 08JB, 08J9
(blueprint: def-sfb-component-slice-comparison-data). -/
structure ExactSquareComparison
    {C : Type c} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type d} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    {E : Type v} [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
    [MonoidalClosed E] [BraidedCategory E] [Abelian.HasFunctorialFlatResolution E]
    {H : Type z} [Category.{u + 1} H] [Abelian H]
    [IsGrothendieckAbelian.{u + 1} H] [MonoidalCategory H] [MonoidalPreadditive H]
    [MonoidalClosed H] [BraidedCategory H] [Abelian.HasFunctorialFlatResolution H]
    (F : C ⥤ D) (G : E ⥤ H) (R : C ⥤ E) (S : D ⥤ H)
    [F.Additive] [G.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Monoidal]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.Monoidal]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] [R.Monoidal]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] [S.Monoidal]
    (derivedIso : F.mapDerivedCategory ⋙ S.mapDerivedCategory ≅
      R.mapDerivedCategory ⋙ G.mapDerivedCategory) where
  smallW : PreservesColimitsOfSize.{0, 0} F
  smallU : PreservesColimitsOfSize.{0, 0} G
  smallT : PreservesColimitsOfSize.{0, 0} R
  smallR : PreservesColimitsOfSize.{0, 0} S
  monoidalW : F.mapDerivedCategory.Monoidal
  monoidalU : G.mapDerivedCategory.Monoidal
  monoidalT : R.mapDerivedCategory.Monoidal
  monoidalR : S.mapDerivedCategory.Monoidal
  normalizationW : letI := smallW; letI := monoidalW
    DerivedMonoidalNormalization F
  normalizationU : letI := smallU; letI := monoidalU
    DerivedMonoidalNormalization G
  normalizationT : letI := smallT; letI := monoidalT
    DerivedMonoidalNormalization R
  normalizationR : letI := smallR; letI := monoidalR
    DerivedMonoidalNormalization S
  monoidal_iso : letI := monoidalW; letI := monoidalU
    letI := monoidalT; letI := monoidalR
    NatTrans.IsMonoidal derivedIso.hom
  sectionsT_limits : PreservesFiniteLimits
    (sections (C := E))
  sectionsT_colimits : PreservesFiniteColimits
    (sections (C := E))
  sectionsU_limits : PreservesFiniteLimits (sections (C := H))
  sectionsU_colimits : PreservesFiniteColimits (sections (C := H))
  sectionsPullback : SectionComparison G
  sectionsHomT : letI := sectionsT_limits; letI := sectionsT_colimits
    HomSectionsIdentification (C := E)
  sectionsHomU : letI := sectionsU_limits; letI := sectionsU_colimits
    HomSectionsIdentification (C := H)
  sliceHomT : letI := monoidalT
    ∀ K L : DerivedCategory (C),
      IsIso (homComparison R K L)
  sliceHomR : letI := monoidalR
    ∀ K L : DerivedCategory (D),
      IsIso (homComparison S K L)
  evaluation_square : letI := monoidalW; letI := monoidalU
    letI := monoidalT; letI := monoidalR
    ∀ K L : DerivedCategory (C),
      S.mapDerivedCategory.map (homComparison F K L) ≫
        homComparison S (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L) ≫
        transportHom _ _ derivedIso K L =
      derivedIso.hom.app ((ihom K).obj L) ≫
        G.mapDerivedCategory.map (homComparison R K L) ≫
        homComparison G (R.mapDerivedCategory.obj K) (R.mapDerivedCategory.obj L)
  derived_sections_square : letI := monoidalW; letI := monoidalU
    letI := monoidalT; letI := monoidalR
    letI (K L : DerivedCategory C) := sliceHomT K L
    ∀ K L : DerivedCategory (C),
      (derivedSections (C := E)).map
          (inv (homComparison R K L)) ≫
        sectionsPullback.derived.hom.app (R.mapDerivedCategory.obj ((ihom K).obj L)) ≫
        (derivedSections (C := H)).map
          (derivedIso.inv.app ((ihom K).obj L)) ≫
        (derivedSections (C := H)).map
          (S.mapDerivedCategory.map
            (homComparison F K L)) ≫
        (derivedSections (C := H)).map
          (homComparison S (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L) ≫
            transportHom _ _ derivedIso K L) =
      localSectionsComparison G sectionsPullback
        (R.mapDerivedCategory.obj K) (R.mapDerivedCategory.obj L)
  cohomology_formula : letI := monoidalU
    letI := sectionsT_limits; letI := sectionsT_colimits
    letI := sectionsU_limits; letI := sectionsU_colimits
    ∀ (K L : DerivedCategory (E)) (n : ℤ)
      (x : (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
        ((derivedSections (C := E)).obj
          ((ihom K).obj L))),
      sectionsHomU.equiv (G.mapDerivedCategory.obj K) (G.mapDerivedCategory.obj L) n
        ((DerivedCategory.homologyFunctor Ab.{u + 1} n).map
          (localSectionsComparison G sectionsPullback K L) x) =
      shiftedHomMap G K L n (sectionsHomT.equiv K L n x)
  fully_faithful_test : letI := monoidalW; letI := monoidalR
    Nonempty G.mapDerivedCategory.FullyFaithful →
      ∀ K L : DerivedCategory (C),
        IsIso ((derivedSections (C := H)).map
          (S.mapDerivedCategory.map
            (homComparison F K L)))


/-- Scheme-slice restriction, represented by the actual inverse image with its
canonical coefficient transport. For pro-etale U this is literal localization.
Source: Stacks 0951, 03DH
(blueprint: def-sfb-component-slice-comparison-data). -/
def schemeRestriction (W : Scheme.{u}) (U : W.ProEt) :
    supportModules Λ.X W ⥤ supportModules Λ.X U.left := supportPullback Λ.X U.hom

/-- The fixed ordinary tensor structure transported from the native module
inverse image along its already defined coefficient-transport isomorphism.
Source: Stacks 03EL (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev schemeCanonicalMonoidal (W : Scheme.{u}) (U : W.ProEt) :
    (schemeRestriction Λ W U).Monoidal :=
  Functor.Monoidal.transport (supportPullbackIsoUpperStar Λ.X U.hom).symm

/-- Exactness of scheme-slice inverse image on finite limits.
Source: Stacks 03DJ (blueprint: def-sfb-component-slice-comparison-data). -/
instance schemeRestrictionLimits (W : Scheme.{u}) (U : W.ProEt) :
    PreservesFiniteLimits (schemeRestriction Λ W U) :=
  inferInstanceAs (PreservesFiniteLimits (supportPullback Λ.X U.hom))
/-- Exactness of scheme-slice inverse image on finite colimits.
Source: Stacks 03DJ (blueprint: def-sfb-component-slice-comparison-data). -/
instance schemeRestrictionColimits (W : Scheme.{u}) (U : W.ProEt) :
    PreservesFiniteColimits (schemeRestriction Λ W U) :=
  inferInstanceAs (PreservesFiniteColimits (supportPullback Λ.X U.hom))
/-- Additivity of scheme-slice restriction.
Source: Stacks 03DJ (blueprint: def-sfb-component-slice-comparison-data). -/
instance schemeRestrictionAdditive (W : Scheme.{u}) (U : W.ProEt) :
    (schemeRestriction Λ W U).Additive :=
  inferInstanceAs (supportPullback Λ.X U.hom).Additive

/-- Compose a test of the slice with its structure map to W.
Source: Stacks 0951 (blueprint: def-sfb-component-slice-comparison-data). -/
abbrev compositeTest (W : Scheme.{u}) (U : W.ProEt) (V : U.left.ProEt) : W.ProEt :=
  Scheme.ProEt.mk (V.hom ≫ U.hom)

/-- Composition changes no underlying test scheme.
Source: Stacks 0951 (blueprint: def-sfb-component-slice-comparison-data). -/
instance compositeTestAffine (W : Scheme.{u}) (U : W.ProEt)
    (V : U.left.ProEt) [IsAffine V.left] : IsAffine (compositeTest W U V).left :=
  inferInstanceAs (IsAffine V.left)
/-- The same underlying affine ring remains w-contractible.
Source: Stacks 0951 (blueprint: def-sfb-component-slice-comparison-data). -/
instance compositeTestWContractible (W : Scheme.{u}) (U : W.ProEt)
    (V : U.left.ProEt) [IsWContractibleRing Γ(V.left, ⊤)] :
    IsWContractibleRing Γ((compositeTest W U V).left, ⊤) :=
  inferInstanceAs (IsWContractibleRing Γ(V.left, ⊤))

/-- Components of a composite test agree with the composite of component maps.
Source: HRS (4.2) (blueprint: def-sfb-component-slice-comparison-data). -/
def componentCompositionIso (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left] (V : U.left.ProEt) [IsAffine V.left] :
    componentAffineObject W (compositeTest W U V) ≅
      (Over.map (componentMap W U)).obj (componentAffineObject U.left V) :=
  Over.isoMk (Iso.refl _) (by
    ext z
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
    rfl)

/-- The prescribed component evaluation, forgetting only the already identified scalars.
Its choice is determined by the Kan-unit normalization in the dependency theorem.
Source: HRS (4.2) (blueprint: def-sfb-component-slice-comparison-data). -/
def basisSections {W : Scheme.{u}} [IsAffine W] (dW : PullbackData Λ W)
    (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)]
    (M : Modules Λ (affineComponentSpace W)) :
    M.X.obj.obj (op (componentAffineObject W U)) ≃+
      (dW.modules.obj M).X.obj.obj (op U) :=
  letI := dW.continuous
  letI := dW.braided
  letI := dW.limits
  letI := dW.colimits
  ((Classical.choose (Classical.choose_spec dW.evaluation) U).app M).toLinearEquiv.toAddEquiv

/-- The canonical localization comparison on the underlying abelian sheaf.
Source: Stacks 0951 (blueprint: def-sfb-component-slice-comparison-data). -/
def restrictionSections (W : Scheme.{u}) (U : W.ProEt)
    (M : supportModules Λ.X W) (V : U.left.ProEt) :
    ((schemeRestriction Λ W U).obj M).X.obj.obj (op V) ≃+
      M.X.obj.obj (op (compositeTest W U V)) :=
  AddEquiv.ofBijective
    (((ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} U.hom
      inferInstance).app M.X).hom.hom.app (op V)).hom
    (ConcreteCategory.bijective_of_isIso _)

/-- The identity formula for the component-slice comparison on every basis test.
Factoring it leaves sheaf and coefficient structures opaque in the assertion record.
Source: HRS (4.2) (blueprint: def-sfb-component-slice-comparison-data). -/
def OrdinaryBasisFormula
    (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left]
    (dW : PullbackData Λ W) (dU : PullbackData Λ U.left)
    (r : RestrictionData Λ (componentMap W U))
    (iso : dW.modules ⋙ schemeRestriction Λ W U ≅ r.modules ⋙ dU.modules) : Prop :=
  ∀ (V : U.left.ProEt) [IsAffine V.left]
  [IsWContractibleRing Γ(V.left, ⊤)] (M : Modules Λ (affineComponentSpace W))
  (x : M.X.obj.obj (op (componentAffineObject W (compositeTest W U V)))),
  HEq ((iso.hom.app M).hom.hom.app (op V)
    ((restrictionSections Λ W U (dW.modules.obj M) V).symm
      (basisSections Λ dW (compositeTest W U V) M x)))
    (basisSections Λ dU V (r.modules.obj M)
      (M.X.obj.map (componentCompositionIso W U V).inv.op x))

/-- The actual module-slice comparison and its identity formula on every
w-contractible affine basis test. Monoidality includes coefficients and units.
Source: HRS Proposition 4.3(1), Stacks 03EL, 08JB
(blueprint: def-sfb-component-slice-comparison-data). -/
structure OrdinaryComparison (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left]
    (dW : PullbackData Λ W) (dU : PullbackData Λ U.left)
    (r : RestrictionData Λ (componentMap W U)) where
  iso : dW.modules ⋙ schemeRestriction Λ W U ≅ r.modules ⋙ dU.modules
  basis_formula : OrdinaryBasisFormula Λ W U dW dU r iso

/-- Coefficient, tensor and unit compatibility of the normalized ordinary square.
Source: HRS (4.2), Stacks 03EL
(blueprint: def-sfb-component-slice-comparison-data). -/
def OrdinaryMonoidal (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left]
    (dW : PullbackData Λ W) (dU : PullbackData Λ U.left)
    (r : RestrictionData Λ (componentMap W U))
    (m : (schemeRestriction Λ W U).Monoidal)
    (e : OrdinaryComparison Λ W U dW dU r) : Prop :=
  letI := m
  m = schemeCanonicalMonoidal Λ W U ∧
    MonoidalSquare dW.modules dU.modules r.modules (schemeRestriction Λ W U) e.iso

/-- Localize the displayed ordinary isomorphism, retaining its exact termwise
normalization on all unbounded complexes.
Source: Stacks 015F (blueprint: def-sfb-component-slice-comparison-data). -/
def OrdinaryComparison.derived {W : Scheme.{u}} [IsAffine W]
    {U : W.ProEt} [IsAffine U.left] {dW : PullbackData Λ W}
    {dU : PullbackData Λ U.left} {r : RestrictionData Λ (componentMap W U)}
    (e : OrdinaryComparison Λ W U dW dU r) :
    dW.derived ⋙ (schemeRestriction Λ W U).mapDerivedCategory ≅
      r.derived ⋙ dU.derived :=
  (Functor.mapDerivedCategoryCompIso dW.modules (schemeRestriction Λ W U)).symm ≪≫
    Functor.mapDerivedCategoryNatIso e.iso ≪≫
    Functor.mapDerivedCategoryCompIso r.modules dU.modules

/-- Specialize the generic normalized square to the actual component and
localization functors. Its ordinary isomorphism is localized termwise.
Source: HRS Proposition 4.3(1), (4.2)
(blueprint: def-sfb-component-slice-comparison-data). -/
def DerivedComparison (W : Scheme.{u}) [IsAffine W]
    (U : W.ProEt) [IsAffine U.left]
    (dW : PullbackData Λ W) (dU : PullbackData Λ U.left)
    (r : RestrictionData Λ (componentMap W U))
    (m : (schemeRestriction Λ W U).Monoidal)
    (e : OrdinaryComparison Λ W U dW dU r) : Type _ :=
  letI := m
  ExactSquareComparison dW.modules dU.modules r.modules (schemeRestriction Λ W U) e.derived

end AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice
