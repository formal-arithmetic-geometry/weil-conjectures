/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Sheaf.Paper.CompletedIntegralScalarRegular
import Sheaf.Paper.CompletedIntegralProjectionDivisibility
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree

/-! # Regular completed coefficients and quotient Koszul fibers

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower, proof paragraph 1;
Bhatt--Scholze, The pro-etale topology for schemes, Section 3.5
(blueprint: lem-sp-ell-coefficient-fiber).

All natural-number level indices denote the positive exponent index+1. The site
and field universes are independent. The completed ring and all finite constant
rings are the existing coefficient-tower objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u vC uC r

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- The existing abelian module-sheaf structure, with sheafification fixed in the
coefficient universe. This explicit specialization prevents the small-site default from
identifying the coefficient universe with the site-object universe. Source: Stacks,
Modules on Sites, and the coefficient setup in sk-lem-sp-tower
(blueprint: lem-sp-ell-coefficient-fiber). -/
instance (priority := 2000) spCoefficientModulesAbelian
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}) :
    Abelian (SheafOfModules.{max u (t + 1)} R) := by
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  exact SheafOfModules.instAbelian R

/-- The ell-power projection of the existing completion, through the uniquely normalized
cofinal-limit comparison. Source: coefficient setup in sk-lem-sp-tower, paragraph 1
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spCompletedEllProjection (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E T ⟶ spCoefficientRing l E T n :=
  (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
    limit.π (spCoefficientRings l E T) (op n)

/-- The underlying module map of a ring-sheaf map, with its natural restriction action.
It is the linear map determined by the section one. Source: the quotient projections in
sk-lem-sp-tower, paragraph 1 (blueprint: lem-sp-ell-coefficient-fiber). -/
def spRingModuleMap {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (q : R ⟶ S) :
    SheafOfModules.unit R ⟶
      (SheafOfModules.restrictScalars q).obj (SheafOfModules.unit S) :=
  SheafOfModules.unitHomEquiv _ |>.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : S.obj.obj U))
      (fun {_ _} f ↦ (S.obj.map f).hom.map_one))

/-- The module B_(n+1) over the existing completed coefficient ring. Source: coefficient
setup in sk-lem-sp-tower, paragraph 1 (blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spCompletedEllModule (n : ℕ) :=
  (SheafOfModules.restrictScalars (spCompletedEllProjection l E T n)).obj
    (SheafOfModules.unit (spCoefficientRing l E T n))

/-- The module (O/pi^(j+1))_T over the same completion. Source: coefficient setup in
sk-lem-sp-tower, paragraph 1 (blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spCompletedPiModule (j : ℕ) :=
  (SheafOfModules.restrictScalars
    (limit.π (integralCoefficientSheafSystem l E T) (op j))).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E T j))

/-- A constant integral scalar as a compatible section of the completed ring. Source:
coefficient setup in sk-lem-sp-tower, paragraph 1
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spCompletedScalar (a : Padic.coefficientExtensionIntegers l E) :
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (integralConstantToCompletionOfUniverses l E T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
            (ULift.up a)))
    (by
      intro U V f
      change (completedIntegralCoefficientSheafUnrestricted l E T).obj.map f _ = _
      rw [← RingCat.comp_apply, ← NatTrans.naturality]
      change (integralConstantToCompletionOfUniverses l E T).hom.app V
        (((constantSheaf _ CommRingCat.{max u (t + 1)}).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))).obj.map
            f _) = _
      congr 1
      exact (ConcreteCategory.congr_hom
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).naturality
              f) (ULift.up a)).symm)

/-- Regular scalars, finite quotients, and the canonically augmented finite free K-flat
resolutions over R. Source: sk-lem-sp-tower, proof paragraph 1; the expanded coefficient
calculation (blueprint: lem-sp-ell-coefficient-fiber).

Proof: factor ell in the DVR O as u*pi^e. Its absolute value is less than one, so e>0;
the two ideal filtrations are cofinal. The finite-residue-field DVR quotient theorem
makes both quotient rings finite. Identify R with its existing uniformizer-power limit.
The completed scalar regularity theorem gives injectivity of pi powers on sections;
the unit factorization gives the same for ell powers. Projection divisibility identifies
its kernel with pi^(j+1)R. Constant sheafification locally supplies O-representatives,
so the projection is locally surjective. Its categorical cokernel is therefore the
finite constant quotient, with the indicated normalization. Apply the cofinal ell-power
comparison for the other quotient. The two principal Koszul cones have no negative
cohomology by regularity and have the asserted quotient in degree zero. Hence their
augmentations are quasi-isomorphisms. Tensoring either scalar cone with an acyclic
complex is the cone of an endomorphism of that acyclic complex; tensor-cone two-out-of-three
gives K-flatness. Each cone has two copies of the rank-one free module in degrees -1,0. -/
theorem sp_completed_coefficients_regular :
    (∃ (e : ℕ) (v : (Padic.coefficientExtensionIntegers l E)ˣ),
      1 ≤ e ∧ (l : Padic.coefficientExtensionIntegers l E) =
        (v : Padic.coefficientExtensionIntegers l E) *
          Padic.coefficientExtensionUniformizer l E ^ e) ∧
    ((∀ n : ℕ, ∃ m : ℕ,
      spEllIdeal l E ^ m ≤ Padic.coefficientExtensionIdeal l E n) ∧
      (∀ n : ℕ, ∃ m : ℕ,
        Padic.coefficientExtensionIdeal l E m ≤ spEllIdeal l E ^ n)) ∧
    (∀ n : ℕ, Finite (Padic.coefficientExtensionIntegers l E ⧸
      spEllIdeal l E ^ (n + 1)) ∧ Finite (Padic.coefficientExtensionRing l E (n + 1))) ∧
    (∀ a : Padic.coefficientExtensionIntegers l E,
      a = l ∨ a = Padic.coefficientExtensionUniformizer l E →
      ∀ m : ℕ,
        Mono (endoPow (globalSectionMultiplication
          (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T a)) (m + 1))) ∧
    (∀ n : ℕ,
      ∃ e : principalQuotient (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) n ≅ spCompletedEllModule l E T n,
        cokernel.π (endoPow (globalSectionMultiplication
          (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l)) (n + 1)) ≫ e.hom =
            spRingModuleMap (spCompletedEllProjection l E T n) ∧
        CochainComplex.IsKFlatResolutionIndependentCoefficients.{t + 1, t, max u (t + 1)}
          (R := completedIntegralCommRingSheafUnrestricted l E T)
          (principalAugmentation (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalar l E T l) n ≫
              (CochainComplex.singleFunctor _ 0).map e.hom)) ∧
    (∀ j : ℕ,
      ∃ e : principalQuotient (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T (Padic.coefficientExtensionUniformizer l E)) j ≅
            spCompletedPiModule l E T j,
        cokernel.π (endoPow (globalSectionMultiplication
          (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T (Padic.coefficientExtensionUniformizer l E))) (j + 1)) ≫
            e.hom = spRingModuleMap
              (limit.π (integralCoefficientSheafSystem l E T) (op j)) ∧
        CochainComplex.IsKFlatResolutionIndependentCoefficients.{t + 1, t, max u (t + 1)}
          (R := completedIntegralCommRingSheafUnrestricted l E T)
          (principalAugmentation (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalar l E T (Padic.coefficientExtensionUniformizer l E)) j ≫
              (CochainComplex.singleFunctor _ 0).map e.hom)) := by
  sorry


/-- The recorded total tensor B_(n+1)[0] tensor K_(m+1) over the completed ring,
using the existing sheaf tensor and totalization. Source: sk-lem-sp-tower, displayed
tensor product (blueprint: lem-sp-ell-coefficient-fiber). -/
def spCompletedQuotientTensor (n m : ℕ) :=
  (koszulTensorFunctor (completedIntegralCommRingSheafUnrestricted l E T)
    (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
      (spCompletedScalar l E T l) m)).obj
        ((CochainComplex.singleFunctor _ 0).obj (spCompletedEllModule l E T n))

/-- The explicit two-term model really computes the total tensor used in the node.
Source: sk-lem-sp-tower, proof paragraph 1, displayed coefficient tensor product
(blueprint: lem-sp-ell-coefficient-fiber).

Proof: the only nonzero summands of the total tensor are B_(n+1) tensor R in
degrees -1 and 0. The tensor unit constraint identifies each with B_(n+1).
The totalization differential is multiplication by ell^(m+1), since the first
factor has degree zero. These termwise identifications commute with the
differentials and give the displayed isomorphism. The same identifications are
linear over B_(n+1), so restriction to any common upper coefficient gives the
relative scalar cones used below. -/
theorem sp_ell_coefficient_tensor (n m : ℕ) (_hm : m ≤ n) :
    Nonempty (spCompletedQuotientTensor l E T n m ≅
      CochainComplex.mappingCone ((CochainComplex.singleFunctor _ 0).map
        (l ^ (m + 1) • 𝟙 (spCompletedEllModule l E T n)))) := by
  sorry

/-- Any quotient reduction between positive coefficient levels. Source: sk-lem-sp-tower,
coefficient tensor calculation (blueprint: lem-sp-ell-coefficient-fiber). -/
def spLevelReduction (n m : ℕ) (h : m ≤ n) :
    spCoefficientRing l E T n ⟶ spCoefficientRing l E T m :=
  (spCoefficientRings l E T).map (homOfLE h).op

/-- B_(n+1), viewed as a module over B_(N+1) by its actual quotient action. Keeping an
arbitrary common upper level permits the transition square to live in one module
category. Source: sk-lem-sp-tower, coefficient tensor calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spRelativeCoefficient (N n : ℕ) (h : n ≤ N) :=
  (SheafOfModules.restrictScalars (spLevelReduction l E T N n h)).obj
    (SheafOfModules.unit (spCoefficientRing l E T n))

/-- The canonical module map induced by a commuting triangle of ring-sheaf maps.
This factors the scalar-action verification independently of the coefficient construction.
Source: sk-lem-sp-tower, quotient reduction maps
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRestrictionModuleMap {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} {R S A : Sheaf J RingCat.{r}}
    (q : R ⟶ S) (s : S ⟶ A) (p : R ⟶ A) (h : q ≫ s = p) :
    (SheafOfModules.restrictScalars q).obj (SheafOfModules.unit S) ⟶
      (SheafOfModules.restrictScalars p).obj (SheafOfModules.unit A) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars q).obj (SheafOfModules.unit S)).val.obj U)
        (Y := ((SheafOfModules.restrictScalars p).obj (SheafOfModules.unit A)).val.obj U)
        { toFun := s.hom.app U
          map_add' := map_add _
          map_smul' := by
            intro a x
            change S.obj.obj U at x
            change s.hom.app U
              (Mul.mul (α := S.obj.obj U) (q.hom.app U a) x) =
                Mul.mul (α := A.obj.obj U) (p.hom.app U a) (s.hom.app U x)
            exact ((s.hom.app U).hom.map_mul (q.hom.app U a) x).trans
              (congrArg (fun z : A.obj.obj U ↦ z * s.hom.app U x)
                (RingHom.congr_fun (congrArg (fun f : R ⟶ A ↦ (f.hom.app U).hom) h) a)) }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change S.obj.obj U at x
        exact RingHom.congr_fun (congrArg RingCat.Hom.hom (s.hom.naturality f)) x }

/-- The actual quotient map between two coefficients as a linear map over a common
upper level. Source: sk-lem-sp-tower, coefficient reductions
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeReduction (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n) :
    spRelativeCoefficient l E T N n hn ⟶
      spRelativeCoefficient l E T N m (hm.trans hn) :=
  spRestrictionModuleMap (spLevelReduction l E T N n hn)
    (spLevelReduction l E T n m hm) (spLevelReduction l E T N m (hm.trans hn))
    ((spCoefficientRings l E T).map_comp (homOfLE hn).op (homOfLE hm).op).symm

/-- The two-term scalar map defining B_(n+1) tensor K_(m+1), before taking its cone.
Source: sk-lem-sp-tower, displayed coefficient tensor product
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeKoszulArrow (N n m : ℕ) (h : n ≤ N) :=
  (CochainComplex.singleFunctor _ 0).map
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n h))

/-- The explicit two-term complex [B_(n+1) --ell^(m+1)--> B_(n+1)]. It is the
scalar cone model of B_(n+1) tensor K_(m+1), in degrees -1,0. Source:
sk-lem-sp-tower, displayed coefficient tensor product
(blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spRelativeKoszul (N n m : ℕ) (h : n ≤ N) :=
  CochainComplex.mappingCone (spRelativeKoszulArrow l E T N n m h)

/-- Projection to the degree -1 coefficient in the scalar cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeKoszulLeft (N n m : ℕ) (h : n ≤ N) :
    (spRelativeKoszul l E T N n m h).X (-1) ⟶ spRelativeCoefficient l E T N n h :=
  HomologicalComplex.homotopyCofiber.fstX (spRelativeKoszulArrow l E T N n m h)
      (-1) 0 (by decide) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (spRelativeCoefficient l E T N n h)).hom

/-- Projection to the degree zero coefficient in the scalar cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeKoszulRight (N n m : ℕ) (h : n ≤ N) :
    (spRelativeKoszul l E T N n m h).X 0 ⟶ spRelativeCoefficient l E T N n h :=
  HomologicalComplex.homotopyCofiber.sndX (spRelativeKoszulArrow l E T N n m h) 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (spRelativeCoefficient l E T N n h)).hom

/-- The actual shifted mapping cone of an augmentation to B_(m+1)[0]. Source:
sk-lem-sp-tower, coefficient fiber (blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spRelativeFiber (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn))) :=
  (CochainComplex.mappingCone ε)⟦(-1 : ℤ)⟧

/-- The degree -1 coordinate of the shifted augmentation cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeFiberLeft (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn))) :
    (spRelativeFiber l E T N n m hn hm ε).X (-1) ⟶
      spRelativeCoefficient l E T N n hn :=
  (CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone ε)
    (-1) (-1) (-2) rfl).hom ≫
      HomologicalComplex.homotopyCofiber.fstX ε (-2) (-1) (by decide) ≫
        spRelativeKoszulLeft l E T N n m hn

/-- The degree zero coordinate of the shifted augmentation cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeFiberMiddle (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn))) :
    (spRelativeFiber l E T N n m hn hm ε).X 0 ⟶
      spRelativeCoefficient l E T N n hn :=
  (CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone ε)
    (-1) 0 (-1) rfl).hom ≫
      HomologicalComplex.homotopyCofiber.fstX ε (-1) 0 (by decide) ≫
        spRelativeKoszulRight l E T N n m hn

/-- The degree one coordinate of the shifted augmentation cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeFiberRight (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn))) :
    (spRelativeFiber l E T N n m hn hm ε).X 1 ⟶
      spRelativeCoefficient l E T N m (hm.trans hn) :=
  (CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone ε)
    (-1) 1 0 rfl).hom ≫
      HomologicalComplex.homotopyCofiber.sndX ε 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (spRelativeCoefficient l E T N m (hm.trans hn))).hom


/-- The coordinate normalization of the quotient fiber comparison, including its
quasi-isomorphism assertion. Source: sk-lem-sp-tower, coefficient tensor and fiber
calculation (blueprint: lem-sp-ell-coefficient-fiber). -/
def SpRelativeFiberComparison (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn)))
    (a : spRelativeCoefficient l E T N m (hm.trans hn) ⟶
      spRelativeCoefficient l E T N n hn)
    (i : (CochainComplex.singleFunctor _ (-1)).obj
      (spRelativeCoefficient l E T N m (hm.trans hn)) ⟶
        spRelativeFiber l E T N n m hn hm ε) : Prop :=
  CochainComplex.mappingCone.inr (spRelativeKoszulArrow l E T N n m hn) ≫ ε =
      (CochainComplex.singleFunctor _ 0).map (spRelativeReduction l E T N n m hn hm) ∧
    spRelativeReduction l E T N n m hn hm ≫ a =
      l ^ (n - m) • 𝟙 (spRelativeCoefficient l E T N n hn) ∧
    Mono a ∧
    i.f (-1) ≫ spRelativeFiberLeft l E T N n m hn hm ε =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-1)
        (spRelativeCoefficient l E T N m (hm.trans hn))).hom ≫ a ∧
    QuasiIso i

/-- The quotient Koszul fiber with its power-multiplication transition square.
All complexes in a comparison are regarded over an arbitrary common upper coefficient
B_(N+1). Taking N=n gives the assertion of B_(n+1)-linearity; taking N=n' expresses
both sides of a transition in exactly the same category, by restriction of scalars.
Source: sk-lem-sp-tower, proof paragraph 1; expanded coefficient calculation
(blueprint: lem-sp-ell-coefficient-fiber).

Proof: reduction B_(n+1) -> B_(m+1) kills ell^(m+1), so it uniquely augments the
scalar cone. Locally lift a section of B_(m+1) to R and multiply it by ell^(n-m).
Changing a lift by ell^(m+1)y changes its image by ell^(n+1)y=0. The local maps
glue and are linear over B_(n+1). The completed scalar injectivity already stated
above gives cancellation: the map is injective and identifies B_(m+1) with the
kernel of ell^(m+1) on B_(n+1). That kernel is also the image ell^(n-m)B_(n+1).
The cokernel is B_(m+1). The shifted augmentation cone has the three terms
B_(n+1) --ell^(m+1)--> B_(n+1) --(-reduction)--> B_(m+1) in degrees -1,0,1.
Its only cohomology is therefore the left kernel. Inserting the indicated kernel
map in degree -1 is a quasi-isomorphism from B_(m+1)[1]. Coefficient reduction
on the three terms is (reduction,reduction,identity). On a local lift x its
composite with the comparison is ell^(n'-m)x mod ell^(n+1), equal to
ell^(n-m)(ell^(n'-n)x) mod ell^(n+1). This is the asserted chain-level square.
When n=m the first differential is zero, the kernel map is identity and the
remaining two terms form the contractible complex [B_m --(-1)--> B_m]. -/
theorem sp_ell_coefficient_fiber (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n) :
    ∃ (ε : spRelativeKoszul l E T N n m hn ⟶
        (CochainComplex.singleFunctor _ 0).obj
          (spRelativeCoefficient l E T N m (hm.trans hn)))
      (a : spRelativeCoefficient l E T N m (hm.trans hn) ⟶
        spRelativeCoefficient l E T N n hn)
      (i : (CochainComplex.singleFunctor _ (-1)).obj
        (spRelativeCoefficient l E T N m (hm.trans hn)) ⟶
          spRelativeFiber l E T N n m hn hm ε),
      SpRelativeFiberComparison l E T N n m hn hm ε a i ∧
      Nonempty ((spRelativeKoszul l E T N n m hn).homology (-1) ≅
        image (l ^ (n - m) • 𝟙 (spRelativeCoefficient l E T N n hn))) ∧
      Nonempty (image (l ^ (n - m) • 𝟙 (spRelativeCoefficient l E T N n hn)) ≅
        spRelativeCoefficient l E T N m (hm.trans hn)) ∧
      Nonempty ((spRelativeKoszul l E T N n m hn).homology 0 ≅
        spRelativeCoefficient l E T N m (hm.trans hn)) ∧
      ∀ (n' : ℕ) (hn' : n' ≤ N) (h : n ≤ n')
        (ε' : spRelativeKoszul l E T N n' m hn' ⟶
          (CochainComplex.singleFunctor _ 0).obj
            (spRelativeCoefficient l E T N m ((hm.trans h).trans hn')))
        (a' : spRelativeCoefficient l E T N m ((hm.trans h).trans hn') ⟶
          spRelativeCoefficient l E T N n' hn')
        (i' : (CochainComplex.singleFunctor _ (-1)).obj
          (spRelativeCoefficient l E T N m ((hm.trans h).trans hn')) ⟶
            spRelativeFiber l E T N n' m hn' (hm.trans h) ε'),
        SpRelativeFiberComparison l E T N n' m hn' (hm.trans h) ε' a' i' →
        ∃ r : spRelativeFiber l E T N n' m hn' (hm.trans h) ε' ⟶
            spRelativeFiber l E T N n m hn hm ε,
          r.f (-1) ≫ spRelativeFiberLeft l E T N n m hn hm ε =
            spRelativeFiberLeft l E T N n' m hn' (hm.trans h) ε' ≫
              spRelativeReduction l E T N n' n hn' h ∧
          r.f 0 ≫ spRelativeFiberMiddle l E T N n m hn hm ε =
            spRelativeFiberMiddle l E T N n' m hn' (hm.trans h) ε' ≫
              spRelativeReduction l E T N n' n hn' h ∧
          r.f 1 ≫ spRelativeFiberRight l E T N n m hn hm ε =
            spRelativeFiberRight l E T N n' m hn' (hm.trans h) ε' ∧
          i' ≫ r = (l ^ (n' - n) • 𝟙 _) ≫ i := by
  sorry

end AlgebraicGeometry.ProEtale
