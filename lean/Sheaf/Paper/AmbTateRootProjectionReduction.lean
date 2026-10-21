/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.Paper.PurInverseImageTensorHomDefinitions
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.CategoryTheory.TorsionSheafConstantModule
import Sheaf.Paper.PurTwistRootTransitions
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage

/-! # Root-projection reduction of finite ramified Tate coefficients

Source: Stacks Project, Tags 0990, 090K, 03EK and 03EL; the explicit nine-step
root-limit argument in the DAG (blueprint: lem-amb-tate-root-projection-reduction).

All levels below are positive: index `r` means exponent `r + 1`, and coefficient
index `n` means quotient by the uniformizer to exponent `n + 1`. Pullback maps
are specified by their direct-image adjuncts. This retains the specified maps,
and expresses their coherence using the actual fibre-product comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

/-- The schemes allowed in the statement, including the empty scheme.
Source: the hypothesis on T (blueprint: lem-amb-tate-root-projection-reduction). -/
abbrev AmbTateBase := {T : Scheme.{u} // ∀ x : T, IsUnit (l : T.presheaf.stalk x)}

/-- Admissible positive root exponents, with only the annihilation condition on A.
Source: the hypothesis on r (blueprint: lem-amb-tate-root-projection-reduction). -/
abbrev AmbTateLevel :=
  {r : ℕ // ((l ^ (r + 1) : ℕ) : Padic.coefficientExtensionRing l E (n + 1)) = 0}

/-- Restrict the existing coordinatewise root action to the constant Z_l sheaf.
Source: proof step 1 (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateConstantRootModule (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (purTwistRing T (purTwistZlConstant T l)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l)

/-- The composite constant scalar map Z_l to O_E to A.
Source: proof step 1 (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateScalar (T : Scheme.{u}) :
    purTwistZlConstant T l ⟶ WeilConjectures.integralCoefficientCommRingSheaf l E T n :=
  purTwistConstantIntegersMap T l E ≫ purTwistIntegralQuotient T l E n

/-- The ordinary tensor H = L tensor over the constant Z_l sheaf with A.
Source: proof step 1 (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateReduced (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T n) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (ambTateScalar l E n T) (ambTateConstantRootModule l T)

/-- A pure tensor in H, with the coefficient written first as in change of rings.
Source: Stacks Tag 03EK (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateReducedPure (T : Scheme.{u}) (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (ambTateReduced l E n T).val.obj (op U) :=
  purScalarSection (purTwistZlConstant T l)
    (WeilConjectures.integralCoefficientCommRingSheaf l E T n)
    (ambTateScalar l E n T) (ambTateConstantRootModule l T) U a x

/-- The unique finite scalar map, constructed using the characteristic divisibility
criterion; it requires no flatness. Source: Stacks Tag 03EK
(blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateFiniteScalar (T : Scheme.{u}) (r : AmbTateLevel l E n) :
    purTwistFiniteRing T l r.val ⟶
      WeilConjectures.integralCoefficientCommRingSheaf l E T n :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom
        ((CharP.cast_eq_zero_iff (Padic.coefficientExtensionRing l E (n + 1))
          (ringChar (Padic.coefficientExtensionRing l E (n + 1))) (l ^ (r.val + 1))).mp
            r.property) (Padic.coefficientExtensionRing l E (n + 1))).comp
        ULift.ringEquiv.toRingHom)))

attribute [irreducible] ambTateFiniteScalar

/-- D_r is the recorded finite roots module tensored over the constant Z/l^r with A.
Source: Stacks Tag 03EK (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateFiniteRoots (T : Scheme.{u}) (r : AmbTateLevel l E n) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T n) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val)

/-- Pure tensors in D_r, using the existing sheafification unit.
Source: Stacks Tag 03EK (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateFinitePure (T : Scheme.{u}) (r : AmbTateLevel l E n) (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1))).obj.obj (op U)) :
    (ambTateFiniteRoots l E n T r).val.obj (op U) :=
  purScalarSection (purTwistFiniteRing T l r.val)
    (WeilConjectures.integralCoefficientCommRingSheaf l E T n)
    (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val) U a x

/-- The double pure tensor in the prescribed P = (L tensor O_E) tensor A.
Source: proof step 1 (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateSourcePure (T : Scheme.{u}) (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (b : (purTwistIntegralConstant T l E).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (purTwistFiniteOne T l E n).val.obj (op U) :=
  purScalarSection (purTwistIntegralConstant T l E)
    (WeilConjectures.integralCoefficientCommRingSheaf l E T n)
    (purTwistIntegralQuotient T l E n) (purTwistIntegralOne T l E) U a
    (purTwistIntegralTensor T l E (op U) b x)

/-- The existing constant-coefficient direct image, with its coefficient type displayed.
Source: Stacks Tag 03D1 (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateDirectImage {T T' : Scheme.{u}} (v : T' ⟶ T) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T' n) ⥤
      SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T n) :=
  proEtaleConstantModuleDirectImage v (Padic.coefficientExtensionRing l E (n + 1))

/-- Evaluation of an adjunct on a local section, exposing its target section type.
Source: Stacks Tag 03D1 (blueprint: lem-amb-tate-root-projection-reduction). -/
def ambTateDirectSection {T T' : Scheme.{u}} (v : T' ⟶ T)
    {M : SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T n)}
    {N : SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T' n)}
    (f : M ⟶ (ambTateDirectImage l E n v).obj N) (U : T.ProEt)
    (x : M.val.obj (op U)) : N.val.obj (op ((proEtaleBaseChange v).obj U)) :=
  f.val.app (op U) x

/-- The conclusion, with every map fixed by its specified root or tensor formula.
The fields c and b are the direct-image adjuncts of c_L and b_v. The square is
therefore exactly the adjunct of the displayed inverse-image square in the node.
Source: the full statement and proof steps 1--9
(blueprint: lem-amb-tate-root-projection-reduction). -/
structure AmbTateRootProjectionData where
  /-- Reassociation for the prescribed finite twist. -/
  j : ∀ T : AmbTateBase l, purTwistFiniteOne T.val l E n ≅ ambTateReduced l E n T.val
  /-- Reassociation is (x tensor b) tensor a to x tensor ba. -/
  j_pure : ∀ (T : AmbTateBase l) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (b : (purTwistIntegralConstant T.val l E).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)),
    (j T).hom.val.app (op U) (ambTateSourcePure l E n T.val U a b x) =
      ambTateReducedPure l E n T.val U
        (a * (purTwistIntegralQuotient T.val l E n).hom.app (op U) b) x
  /-- Projection-induced finite reduction is an isomorphism at every admissible level. -/
  theta : ∀ (T : AmbTateBase l) (r : AmbTateLevel l E n),
    purTwistFiniteOne T.val l E n ≅ ambTateFiniteRoots l E n T.val r
  /-- The precise p_r normalization of theta. -/
  theta_pure : ∀ (T : AmbTateBase l) (r : AmbTateLevel l E n) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)),
    (theta T r).hom.val.app (op U)
        ((j T).inv.val.app (op U) (ambTateReducedPure l E n T.val U a x)) =
      ambTateFinitePure l E n T.val r U a
        ((limit.π (proEtaleRootsOfUnityTower T.val l (Fact.out : l.Prime))
          (op r.val)).hom.app (op U) x)
  /-- Tensor of the power transition, over the different finite coefficient rings. -/
  transition : ∀ (T : AmbTateBase l) (r s : AmbTateLevel l E n) (_h : r.val ≤ s.val),
    ambTateFiniteRoots l E n T.val s ⟶ ambTateFiniteRoots l E n T.val r
  /-- Its normalization on every root tensor. -/
  transition_pure : ∀ (T : AmbTateBase l) (r s : AmbTateLevel l E n) (h : r.val ≤ s.val)
    (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T.val (l ^ (s.val + 1))).obj.obj (op U)),
    (transition T r s h).val.app (op U) (ambTateFinitePure l E n T.val s U a x) =
      ambTateFinitePure l E n T.val r U a
        ((proEtaleRootsOfUnityTransition T.val (l ^ (r.val + 1)) (l ^ (s.val + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
          (pow_dvd_pow l (Nat.add_le_add_right h 1))).hom.app (op U) x)
  /-- Compatibility with theta at all larger levels. -/
  transition_theta : ∀ (T : AmbTateBase l) (r s : AmbTateLevel l E n) (h : r.val ≤ s.val),
    (theta T s).hom ≫ transition T r s h = (theta T r).hom
  /-- Invertibility uses only the annihilation condition in AmbTateLevel. -/
  transition_isIso : ∀ (T : AmbTateBase l) (r s : AmbTateLevel l E n) (h : r.val ≤ s.val),
    IsIso (transition T r s h)
  /-- Identity transition. -/
  transition_id : ∀ (T : AmbTateBase l) (r : AmbTateLevel l E n),
    transition T r r le_rfl = 𝟙 _
  /-- Composition of transitions. -/
  transition_comp : ∀ (T : AmbTateBase l) (r s t : AmbTateLevel l E n)
    (h : r.val ≤ s.val) (k : s.val ≤ t.val),
    transition T s t k ≫ transition T r s h = transition T r t (h.trans k)
  /-- Adjunct of the comparison to the target root limit. -/
  c : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val),
    purTwistZlOne T.val l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T'.val l)
  /-- Every projection agrees with the specified pullback-of-units map. -/
  c_projection : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (s : ℕ),
    c v ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T'.val l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T.val l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))
  /-- Limit uniqueness, equivalently uniqueness of c_L under adjunction. -/
  c_unique : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val)
    (d : purTwistZlOne T.val l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T'.val l)),
    (∀ s : ℕ, d ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T'.val l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T.val l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))) → d = c v
  /-- Adjunct of b_v for the canonical constant-ring module pullback. -/
  b : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val),
    purTwistFiniteOne T.val l E n ⟶
      (ambTateDirectImage l E n v).obj
        (purTwistFiniteOne T'.val l E n)
  /-- Transport of c_L tensor 1 through j, stated on the double pure tensors. -/
  b_pure : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (z : (purTwistIntegralConstant T.val l E).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)),
    ambTateDirectSection l E n v (b v) U (ambTateSourcePure l E n T.val U a z x) =
      ambTateSourcePure l E n T'.val ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U) a)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionIntegers l E)).hom.app (op U) z)
        ((c v).hom.app (op U) x)
  /-- Adjunct of the tensor of the canonical finite root map with 1. -/
  delta : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n),
    ambTateFiniteRoots l E n T.val r ⟶
      (ambTateDirectImage l E n v).obj
        (ambTateFiniteRoots l E n T'.val r)
  /-- The specified finite root map, rather than an arbitrary comparison. -/
  delta_pure : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n)
    (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T.val (l ^ (r.val + 1))).obj.obj (op U)),
    ambTateDirectSection l E n v (delta v r) U (ambTateFinitePure l E n T.val r U a x) =
      ambTateFinitePure l E n T'.val r ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U) a)
        ((proEtaleRootsOfUnityDirectImageMap v (l ^ (r.val + 1))).hom.app (op U) x)
  /-- The displayed base-change square, transposed under the module adjunction. -/
  square : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n),
    b v ≫ (ambTateDirectImage l E n v).map (theta T' r).hom =
      (theta T r).hom ≫ delta v r
  /-- Identity law for c_L, under the canonical identity fibre-product comparison. -/
  c_id : ∀ (T : AmbTateBase l) (U : T.val.ProEt)
    (x : (purTwistZlOne T.val l).obj.obj (op U)),
    (c (𝟙 T.val)).hom.app (op U) x = (purTwistZlOne T.val l).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T.val).hom.app U).op x
  /-- Composition law for c_L, under the canonical iterated pullback comparison. -/
  c_comp : ∀ {T T' T'' : AmbTateBase l} (v : T'.val ⟶ T.val) (w : T''.val ⟶ T'.val)
    (U : T.val.ProEt) (x : (purTwistZlOne T.val l).obj.obj (op U)),
    (c (w ≫ v)).hom.app (op U) x = (purTwistZlOne T''.val l).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      ((c w).hom.app (op ((proEtaleBaseChange v).obj U)) ((c v).hom.app (op U) x))
  /-- Identity law for b_v under the same canonical identity comparison. -/
  b_id : ∀ (T : AmbTateBase l) (U : T.val.ProEt)
    (x : (purTwistFiniteOne T.val l E n).val.obj (op U)),
    ambTateDirectSection l E n (𝟙 T.val) (b (𝟙 T.val)) U x = (purTwistFiniteOne T.val l E n).val.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T.val).hom.app U).op x
  /-- Composition law for b_v under the same canonical iterated pullback comparison. -/
  b_comp : ∀ {T T' T'' : AmbTateBase l} (v : T'.val ⟶ T.val) (w : T''.val ⟶ T'.val)
    (U : T.val.ProEt) (x : (purTwistFiniteOne T.val l E n).val.obj (op U)),
    ambTateDirectSection l E n (w ≫ v) (b (w ≫ v)) U x = (purTwistFiniteOne T''.val l E n).val.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      (ambTateDirectSection l E n w (b w) ((proEtaleBaseChange v).obj U)
        (ambTateDirectSection l E n v (b v) U x))

/-- Root-projection reduction with arbitrary ramification and annihilated finite coefficients.
Source: Stacks Tags 0990, 090K, 03EK and 03EL; explicit root-limit proof below
(blueprint: lem-amb-tate-root-projection-reduction).

Proof:

1. Give $L_T$ its $Z_T$-action by $(a x)_s=x_s^{a\bmod\ell^s}$; the power transitions respect
reduction of the exponent, so this is an action on compatible tuples. In additive module notation,
define $j_T((x\otimes b)\otimes a)=x\otimes ba$ and its inverse by $x\otimes
a\mapsto(x\otimes1)\otimes a$. The balancing relations make both maps well defined, and their
composites are the identity on pure tensors. Sheafify these natural sectionwise formulas. The
definition of $P_T$ identifies the first source with the prescribed finite twist.

2. The projections $p_{r,T}$ are locally surjective. Indeed, apply lem-pur-twist-root-transitions
to every consecutive power map. The general-site abelian epi criterion makes it locally surjective
on underlying sets, and the set epi criterion makes it an epimorphism of set sheaves. Given an
object $U$ and $u\in\mu_{\ell^r}(U)$, cover $U$ by the affine objects $V_i$ weakly contractible
for the full $T_{\mathrm{proet}}$ site. On each fixed $V_i$, every consecutive transition is
surjective on sections by that precise weak contractibility assertion. Set $x_r=u|_{V_i}$, define
$x_s=u|_{V_i}^{\ell^{r-s}}$ for $s<r$, and choose recursively $x_{s+1}$ above $x_s$ for $s\geq r$.
This gives a compatible tuple, hence an element of $L_T(V_i)$ with $r$th projection $u|_{V_i}$.
All uses are on the full site; no infinite refinement of etale covers is asserted.

3. Compute the kernel on every object $U$. If $x=(x_s)_s\in L_T(U)$ has $x_r=1$, put
$y_s=x_{s+r}$. Since $x_{s+r}^{\ell^s}=x_r=1$, this really belongs to $\mu_{\ell^s}(U)$, and
$y_{s+1}^\ell=y_s$. Also $y_s^{\ell^r}=x_s$. Conversely $(\ell^r y)_r=y_r^{\ell^r}=1$ for every
$y$. Thus in additive notation $\ker p_r(U)=\ell^rL_T(U)$, with an explicit division map on the
kernel, compatible with restrictions.

4. Put $H=L_T\otimes_{Z_T}A_T$, which is killed by $\ell^r$ since $\ell^rA=0$. For local sections
$u$ of $\mu_{\ell^r}$ and $a$ of $A_T$, choose local lifts $x$ of $u$ by step 2 and set
$B(u,a)=x\otimes a$. Two lifts differ by $\ell^r y$ by step 3, so their tensors differ by
$y\otimes\ell^ra=0$. The local outputs therefore glue uniquely and commute with restrictions.
Addition in either input follows by choosing lifts $x+x'$ and by distributivity of the tensor. For
fixed $a$ this is an additive map to $H$ on the slice site, so lem-pur-torsion-sheaf-constant-
module (2) makes it $R_{r,T}$-linear; both source and target are killed by $\ell^r$. Consequently
$B(cu,a)=B(u,ca)$ for local $c\in R_{r,T}$, and $B(u,aa')=a'B(u,a)$. The universal property of the
sheaf tensor gives an $A_T$-linear map $D_{r,T}\to H$. Conversely $x\otimes a\mapsto p_r(x)\otimes
a$ is $Z_T$-balanced, since the action in step 1 projects to exponent reduction. Both composites
are identity: on $x\otimes a$ choose the lift $x$, and on $u\otimes a$ use any local lift of $u$.
The pure-tensor determination statement proves equality of the resulting sheaf maps. Compose
$H\cong D_{r,T}$ with $j_T$ to obtain precisely $\theta_{r,T}$. No exactness of tensoring with $A$
was used.

5. For $r'\geq r$, apply both sides of the asserted transition equation to $j_T^{-1}(x\otimes a)$.
They give respectively $x_{r'}^{\ell^{r'-r}}\otimes a$ and $x_r\otimes a$, which agree by
compatibility of the tuple. Pure tensors determine the maps, so
$(P_{r',r}\otimes1)\theta_{r',T}=\theta_{r,T}$. In particular the transition is
$\theta_{r,T}\theta_{r',T}^{-1}$ and is invertible. For three levels, the exponent identity
$\ell^{r''-r'}\ell^{r'-r}=\ell^{r''-r}$ proves composition; at equal levels the exponent is $1$.
The tensors over the different finite rings are well defined because each power map is linear
after restriction to the larger finite ring and $A$ factors through the smaller quotient.

6. For $v:T'\to T$, lem-pur-roots-of-unity-inverse-image-iso (1)-(2) says exactly that $c^v_s$
commutes with the power transitions and is semilinear over the constant finite ring maps. It also
obeys identity and composition laws under the canonical inverse-image identifications: by def-pur-
roots-of-unity-inverse-image its adjunct on an object $U\to T$ is the pullback of the same unit
along $T'\times_TU\to U$. For $w:T''\to T'$, the iterated pullback on
$T''\times_{T'}(T'\times_TU)$ is the pullback on $T''\times_TU$, because the canonical fibre-
product identification commutes with the projections and pullback of global functions respects
composition. Hence these adjuncts are equal, and the adjunction bijection gives $c^{v\circ
w}_s=c^w_s\,w^{-1}(c^v_s)$ after the comparison isomorphism. The identity projection gives
$c^{\mathrm{id}}_s=\mathrm{id}$. These are equalities of the specified maps, rather than choices
of isomorphisms.

7. The maps $c^v_s\,v^{-1}p_{s,T}$ form a cone by the transition equation in step 6. Apply the
universal property of the limit on $T'_{\mathrm{proet}}$ to obtain $c^v_L:v^{-1}L_T\to L_{T'}$.
Its projection equations are exactly those of the statement, and joint uniqueness of maps to a
limit proves uniqueness. It is semilinear for the constant $\mathbf Z_\ell$ map: after $p_{s,T'}$
this says that pulling back an exponent and reducing it modulo $\ell^s$ gives the same scalar as
reducing first, followed by the finite constant-ring map. This is the semilinearity in step 6 and
the coordinatewise action in step 1, so the projections prove the assertion. This construction
uses a cone into $L_{T'}$, never an assertion that $v^{-1}$ preserves the infinite limit.

8. The structure maps $c^v_\Lambda:v^{-1}\Lambda_T\to\Lambda_{T'}$ of the constant coefficient
rings ($\Lambda=\mathbf Z_\ell,\mathbf Z/\ell^r,A$) are the canonical ring-sheaf isomorphisms of
lem-pe-constant-left-module-inverse-image for the geometric morphism $v_{\mathrm{proet}}$; this is
the identification of the statement. Apply lem-weil-pbc-ringed-topoi-module-pullback-tensor to the
pro-etale geometric morphism and these constant coefficient ring maps. Together with $j_T,j_{T'}$
this identifies $v^*P_T$ with $v^{-1}L_T\otimes_{v^{-1}Z_T}A_{T'}$. The semilinear map of step 7
induces $x\otimes a\mapsto c^v_L(x)\otimes a$; this is the required $b_v$ after the stated
identifications. On a pure tensor, the two sides of the required square are
$p_{r,T'}c^v_L(x)\otimes a$ and $c^v_r(v^{-1}p_{r,T}(x))\otimes a$. Step 7 equates these
expressions. The pure-tensor determination property gives equality of the sheaf morphisms, proving
the full square with the specified root maps.

9. For the identity morphism, every projection of $c_L^{\mathrm{id}}$ equals $p_s$, so
$c_L^{\mathrm{id}}=\mathrm{id}$. For $T''\xrightarrow w T'\xrightarrow v T$, project
$c_L^w\,w^{-1}(c_L^v)$ to level $s$. Using step 7 twice gives $c_s^w\,w^{-1}(c_s^v)\,(v\circ
w)^{-1}p_{s,T}$ after the canonical comparison; step 6 identifies this with $c_s^{v\circ
w}\,(v\circ w)^{-1}p_{s,T}$. Limit uniqueness gives the composition law for $c_L$. On a pure
tensor both the composite pullback map for $b_w,w^*b_v$ and $b_{v\circ w}$ therefore send
$x\otimes a$ to $c_L^{v\circ w}(x)\otimes a$. Identity and composition follow from pure-tensor
determination, the canonical monoidal inverse-image comparisons, and the compatibility of the
constant-ring identifications with composition of geometric morphisms stated in lem-pe-constant-
left-module-inverse-image. On the empty scheme all these formulas are the unique maps of zero
sheaves. Every inverse constructed in step 4 uses only $\ell^rA=0$, so the proof imposes neither
flatness over $\mathbf Z/\ell^r$ nor any divisibility of $n$ by the ramification index.
-/
theorem ambTateRootProjectionReduction :
    Nonempty (AmbTateRootProjectionData l E n) := by
  sorry

end AlgebraicGeometry.Scheme
