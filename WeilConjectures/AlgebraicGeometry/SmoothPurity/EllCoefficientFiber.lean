/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import WeilConjectures.Algebra.Homology.Finite.FiniteFreeMonoCokernelKFlat
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
public import WeilConjectures.Algebra.Homology.TwoTermCone.TwoTermConeFiber
public import WeilConjectures.AlgebraicGeometry.EllCoefficientExactRow

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

/-- The ell-power projection of the existing completion, through the uniquely normalized
cofinal-limit comparison. Source: coefficient setup in sk-lem-sp-tower, paragraph 1
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spCompletedEllProjection (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E T ⟶ spCoefficientRing l E T n :=
  (sp_completed_coefficient_limit l E T).exists.choose.hom ≫
    limit.π (spCoefficientRings l E T) (op n)

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
  CochainComplex.TwoTermCone.arrow
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n h))

/-- The explicit two-term complex [B_(n+1) --ell^(m+1)--> B_(n+1)]. It is the
scalar cone model of B_(n+1) tensor K_(m+1), in degrees -1,0. Source:
sk-lem-sp-tower, displayed coefficient tensor product
(blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spRelativeKoszul (N n m : ℕ) (h : n ≤ N) :=
  CochainComplex.TwoTermCone.complex
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n h))

/-- Projection to the degree -1 coefficient in the scalar cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeKoszulLeft (N n m : ℕ) (h : n ≤ N) :
    (spRelativeKoszul l E T N n m h).X (-1) ⟶ spRelativeCoefficient l E T N n h :=
  CochainComplex.TwoTermCone.left
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n h))

/-- Projection to the degree zero coefficient in the scalar cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeKoszulRight (N n m : ℕ) (h : n ≤ N) :
    (spRelativeKoszul l E T N n m h).X 0 ⟶ spRelativeCoefficient l E T N n h :=
  CochainComplex.TwoTermCone.right
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n h))

/-- The actual shifted mapping cone of an augmentation to B_(m+1)[0]. Source:
sk-lem-sp-tower, coefficient fiber (blueprint: lem-sp-ell-coefficient-fiber). -/
abbrev spRelativeFiber (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn))) :=
  CochainComplex.TwoTermCone.fiber
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n hn)) ε

/-- The degree -1 coordinate of the shifted augmentation cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeFiberLeft (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn))) :
    (spRelativeFiber l E T N n m hn hm ε).X (-1) ⟶
      spRelativeCoefficient l E T N n hn :=
  CochainComplex.TwoTermCone.fiberLeft
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n hn)) ε

/-- The degree zero coordinate of the shifted augmentation cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeFiberMiddle (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn))) :
    (spRelativeFiber l E T N n m hn hm ε).X 0 ⟶
      spRelativeCoefficient l E T N n hn :=
  CochainComplex.TwoTermCone.fiberMiddle
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n hn)) ε

/-- The degree one coordinate of the shifted augmentation cone. Source:
sk-lem-sp-tower, chain-coordinate calculation
(blueprint: lem-sp-ell-coefficient-fiber). -/
def spRelativeFiberRight (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (ε : spRelativeKoszul l E T N n m hn ⟶
      (CochainComplex.singleFunctor _ 0).obj
        (spRelativeCoefficient l E T N m (hm.trans hn))) :
    (spRelativeFiber l E T N n m hn hm ε).X 1 ⟶
      spRelativeCoefficient l E T N m (hm.trans hn) :=
  CochainComplex.TwoTermCone.fiberRight
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n hn)) ε

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
  CochainComplex.TwoTermCone.normalizedComparison
    (l ^ (m + 1) • 𝟙 (spRelativeCoefficient l E T N n hn))
    (spRelativeReduction l E T N n m hn hm)
    (l ^ (n - m) • 𝟙 (spRelativeCoefficient l E T N n hn)) ε a i

private lemma relativeReduction_comp (N n' n m : ℕ) (hn' : n' ≤ N)
    (h : n ≤ n') (hm : m ≤ n) :
    spRelativeReduction l E T N n' n hn' h ≫
      spRelativeReduction l E T N n m (h.trans hn') hm =
      spRelativeReduction l E T N n' m hn' (hm.trans h) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (spLevelReduction l E T n m hm).hom.app U
    ((spLevelReduction l E T n' n h).hom.app U x) =
      (spLevelReduction l E T n' m (hm.trans h)).hom.app U x
  exact RingHom.congr_fun
    (congrArg (fun f => (f.hom.app U).hom)
      ((spCoefficientRings l E T).map_comp (homOfLE h).op (homOfLE hm).op)).symm x

private lemma scalar_kernel_square {C : Type uC} [Category.{vC} C] [Preadditive C]
    {X X' D : C} (q : X ⟶ D) (q' : X' ⟶ D) [Epi q']
    (a : D ⟶ X) (a' : D ⟶ X') (β : X' ⟶ X)
    (n' n m : ℕ) (h : n ≤ n') (hm : m ≤ n)
    (hq : β ≫ q = q')
    (ha : q ≫ a = l ^ (n - m) • 𝟙 X)
    (ha' : q' ≫ a' = l ^ (n' - m) • 𝟙 X') :
    a' ≫ β = (l ^ (n' - n) • 𝟙 D) ≫ a := by
  apply (cancel_epi q').1
  have hqa : q' ≫ a = l ^ (n - m) • β := by
    rw [← hq, Category.assoc, ha, Preadditive.comp_nsmul, Category.comp_id]
  calc
    q' ≫ (a' ≫ β) = l ^ (n' - m) • β := by
      rw [← Category.assoc, ha', Preadditive.nsmul_comp, Category.id_comp]
    _ = l ^ (n' - n) • (l ^ (n - m) • β) := by
      rw [smul_smul, ← pow_add, show n' - n + (n - m) = n' - m by omega]
    _ = q' ≫ ((l ^ (n' - n) • 𝟙 D) ≫ a) := by
      simp only [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, hqa]

private theorem scalarAssembly {C : Type uC} [Category.{vC} C] [Abelian C]
    (l n m : ℕ) (hm : m ≤ n) {X D : C}
    (q : X ⟶ D) (a : D ⟶ X) [Mono a] [Epi q]
    (ha : q ≫ a = l ^ (n - m) • 𝟙 X)
    (had : a ≫ (l ^ (m + 1) • 𝟙 X) = 0)
    (hdq : (l ^ (m + 1) • 𝟙 X) ≫ q = 0)
    (hleft : (ShortComplex.mk a (l ^ (m + 1) • 𝟙 X) had).Exact)
    (hright : (ShortComplex.mk (l ^ (m + 1) • 𝟙 X) q hdq).Exact) :
    ∃ (ε : complex (l ^ (m + 1) • 𝟙 X) ⟶ single D)
      (i : (CochainComplex.singleFunctor C (-1)).obj D ⟶
        fiber (l ^ (m + 1) • 𝟙 X) ε),
      CochainComplex.TwoTermCone.normalizedComparison (l ^ (m + 1) • 𝟙 X) q
        (l ^ (n - m) • 𝟙 X) ε a i ∧
      Nonempty ((complex (l ^ (m + 1) • 𝟙 X)).homology (-1) ≅
        image (l ^ (n - m) • 𝟙 X)) ∧
      Nonempty (image (l ^ (n - m) • 𝟙 X) ≅ D) ∧
      Nonempty ((complex (l ^ (m + 1) • 𝟙 X)).homology 0 ≅ D) ∧
      ∀ (n' : ℕ) (_h : n ≤ n') (X' : C) (q' : X' ⟶ D) [Epi q']
        (β : X' ⟶ X) (_hq : β ≫ q = q')
        (ε' : complex (l ^ (m + 1) • 𝟙 X') ⟶ single D)
        (a' : D ⟶ X')
        (i' : (CochainComplex.singleFunctor C (-1)).obj D ⟶
          fiber (l ^ (m + 1) • 𝟙 X') ε'),
        CochainComplex.TwoTermCone.normalizedComparison (l ^ (m + 1) • 𝟙 X') q'
          (l ^ (n' - m) • 𝟙 X') ε' a' i' →
        ∃ r : fiber (l ^ (m + 1) • 𝟙 X') ε' ⟶ fiber (l ^ (m + 1) • 𝟙 X) ε,
          r.f (-1) ≫ fiberLeft (l ^ (m + 1) • 𝟙 X) ε =
            fiberLeft (l ^ (m + 1) • 𝟙 X') ε' ≫ β ∧
          r.f 0 ≫ fiberMiddle (l ^ (m + 1) • 𝟙 X) ε =
            fiberMiddle (l ^ (m + 1) • 𝟙 X') ε' ≫ β ∧
          r.f 1 ≫ fiberRight (l ^ (m + 1) • 𝟙 X) ε =
            fiberRight (l ^ (m + 1) • 𝟙 X') ε' ∧
          i' ≫ r = (l ^ (n' - n) • 𝟙 _) ≫ i := by
  let d : X ⟶ X := l ^ (m + 1) • 𝟙 X
  obtain ⟨i, hi, hqi, ⟨eneg⟩, ⟨ezero⟩, htrans⟩ :=
    exact_row_fiber d q a had hdq hleft hright
  let ε := augmentation d q hdq
  let : StrongEpi q := strongEpi_of_epi q
  let eim : D ≅ image (l ^ (n - m) • 𝟙 X) := image.isoStrongEpiMono q a ha
  refine ⟨ε, i, ⟨inr_augmentation d q hdq, ha, inferInstance, hi, hqi⟩,
    ⟨eneg ≪≫ eim⟩, ⟨eim.symm⟩, ⟨ezero⟩, ?_⟩
  intro n' h X' q' _ β hq ε' a' i' hc'
  have hβ : (l ^ (m + 1) • 𝟙 X') ≫ β = β ≫ d := by
    simp only [d, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id]
  have haβ : a' ≫ β = (l ^ (n' - n) • 𝟙 D) ≫ a :=
    scalar_kernel_square l q q' a a' β n' n m h hm hq ha hc'.2.1
  obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ := htrans X' (l ^ (m + 1) • 𝟙 X') q' a'
    (l ^ (n' - n) • 𝟙 D) β hβ hq haβ ε' i' hc'.1 hc'.2.2.2.1
  refine ⟨r, hr₁, hr₂, hr₃, ?_⟩
  simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using hr₄

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
  let A := SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T N)
  let X : A := spRelativeCoefficient l E T N n hn
  let D : A := spRelativeCoefficient l E T N m (hm.trans hn)
  let q : X ⟶ D := spRelativeReduction l E T N n m hn hm
  obtain ⟨a, ha, hmono, hepi, had, hdq, hleft, hright⟩ :=
    sp_ell_coefficient_exact_row l E T N n m hn hm
  let : Mono a := hmono
  let : Epi q := hepi
  obtain ⟨ε, i, hc, hneg, him, hzero, htrans⟩ :=
    scalarAssembly l n m hm q a ha had hdq hleft hright
  refine ⟨ε, a, i, hc, hneg, him, hzero, ?_⟩
  intro n' hn' h ε' a' i' hc'
  let q' := spRelativeReduction l E T N n' m hn' (hm.trans h)
  let : Epi q' := spRelativeReduction_epi l E T N n' m hn' (hm.trans h)
  exact htrans n' h (spRelativeCoefficient l E T N n' hn') q'
    (spRelativeReduction l E T N n' n hn' h)
    (relativeReduction_comp l E T N n' n m hn' h hm) ε' a' i' hc'

end AlgebraicGeometry.ProEtale
