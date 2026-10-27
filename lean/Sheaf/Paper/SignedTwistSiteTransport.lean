/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.SignedTwistSiteTransportData
public import Sheaf.Paper.SignedLineScalarTensorTower
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import all Sheaf.AlgebraicGeometry.FiniteRootSiteComparison
import Sheaf.Paper.RootTowerFiniteTensor
import Sheaf.Paper.SignedTwistGeometricCompatibility
import Sheaf.Paper.SignedTwistProductCompatibility
import Sheaf.Paper.SignedTwistEvaluationExtension

/-! # Evaluation-normalized signed finite Tate site comparison

Source: Stacks Project, Tags 07A4, 03EL, 0GMX and 0FNY; the root-normalized signed
refinement of the coefficient identification in def-pur-frame-class
(blueprint: lem-pur-signed-twist-site-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalExponent

set_option maxHeartbeats 1000000 in
-- The local-root calculation unfolds both scalar-extension presentations.
private theorem root_normalized
    (P : PurityFiniteSetting.{u}) (n : ℕ) (hlevel : P.level = n + 1)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (b : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X (k : ℤ)) ≅ P.signedSitePro n X (k : ℤ))
    (hb : ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      IsFiniteTateSiteComparison P.coefficients.l P.extension n X n hA k (b X a k))
    (θ : P.SignedSiteTheta n hA) (hθ : P.SignedSiteThetaNormalized n hA θ)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k))
    (U : X.Etaleᵒᵖ) (W : X.ProEtᵒᵖ) (f : W.unop ⟶ (toProEt X).obj U.unop)
    (z : (X.rootsOfUnitySheaf (P.coefficients.l ^ (n + 1))).obj.obj U) :
    (θ X a).hom.hom.app W
      ((b X a 1).hom.hom.app W
        (P.signedSiteImage n hA X 1 U W f
          (finiteEtaleTateOneGenerator (P.signedSiteCoefficient n)
            (P.coefficients.l ^ (n + 1)) X hA U 1 z))) =
    finiteRootProGenerator (P.signedSiteCoefficient n) (P.coefficients.l ^ (n + 1))
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA X W 1
      ((ProEtale.cartierRootsIso X (P.coefficients.l ^ (n + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (by simpa [diagonalExponent, hlevel] using P.diagonalExponent_isUnit a)).hom.hom.app W
          (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj
            (X.rootsOfUnitySheaf (P.coefficients.l ^ (n + 1)))).obj.map f.op
              (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
                (X.rootsOfUnitySheaf (P.coefficients.l ^ (n + 1)))).hom.app U z))) := by
  let m := P.coefficients.l ^ (n + 1)
  have hm : 0 < m := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  have hX : IsUnit (m : Γ(X, ⊤)) := by
    simpa [m, diagonalExponent, hlevel] using P.diagonalExponent_isUnit a
  let p := rootTowerProjection X P.coefficients.l n
  have : Sheaf.IsLocallySurjective p :=
    (rootTower_finite_tensor X P.coefficients.l
      (P.coefficientPrime_isUnit_stalk X a) n).1
  let zpro := (ProEtale.cartierRootsIso X m hm hX).hom.hom.app W
    (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj
      (X.rootsOfUnitySheaf m)).obj.map f.op
        (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
          (X.rootsOfUnitySheaf m)).hom.app U z))
  apply (finiteRootProTensor (P.signedSiteCoefficient n) m hm hA X).property.isSeparated _ _
    (Presheaf.imageSieve_mem (ProEt.topology X) p.hom zpro)
  intro V g hg
  obtain ⟨x, hx⟩ := hg
  change p.hom.app (op V) x =
    (proEtaleRootsOfUnitySheaf X m).obj.map g.op zpro at hx
  erw [← NatTrans.naturality_apply (θ X a).hom.hom,
    ← NatTrans.naturality_apply (b X a 1).hom.hom]
  have himage (r : ℤ) (y : (P.signedSiteEtale n hA X r).obj.obj U) :
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X r)).obj.map g.op
          (P.signedSiteImage n hA X r U W f y) =
      P.signedSiteImage n hA X r U (op V) (g ≫ f) y := by
    dsimp only [signedSiteImage]
    rw [op_comp, Functor.map_comp]
    rfl
  erw [himage (1 : ℤ)]
  have hroot : finiteTateLimitRootValue P.coefficients.l X n (op V) x =
      Units.map (g ≫ f).left.appTop.hom.toMonoidHom
        (finiteTateEtaleRootValue X m U z) := by
    have hnat := NatTrans.naturality_apply
      (ProEtale.cartierRootsIso X m hm hX).hom.hom g.op
      (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj
        (X.rootsOfUnitySheaf m)).obj.map f.op
          (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
            (X.rootsOfUnitySheaf m)).hom.app U z))
    have hz := rootComparison_unit X m hm hX U (op V) (g ≫ f) z
    dsimp only [finiteTateLimitRootValue, finiteTateEtaleRootValue]
    change Additive.toMul
      ((proEtaleRootsOfUnityInclusion X m).hom.app (op V) (p.hom.app (op V) x)).down = _
    rw [hx]
    rw [← hnat]
    convert hz using 1 <;>
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    all_goals rfl
  have hb' := hb X a 1 U (op V) (g ≫ f) 1 (fun _ ↦ z) (fun _ ↦ x)
    (fun _ ↦ hroot)
  change (b X a 1).hom.hom.app (op V)
    (P.signedSiteImage n hA X 1 U (op V) (g ≫ f)
      (finiteEtaleTateOneGenerator (P.signedSiteCoefficient n) m X hA U 1 z)) =
      finiteTateProGenerator P.coefficients.l P.extension n X (op V) 1 x at hb'
  rw [hb', hθ X a (op V) 1 x]
  rw [proGenerator_map, ← hx]

/-- The fixed nonnegative comparison has its unique evaluation-normalized signed
extension. It respects ordered multiplication in every sign combination, the
negative root/dual geometric pullback squares, identity and composition, and the
precise degree-one coefficient map. The predecessor n represents the source's
positive level n+1; hlevel identifies it with the given purity setting.
The proof hA spells out the annihilation already implied by that setting.

Source: Stacks Project, sites-cohomology.tex, Tag 07A4; sites-modules.tex, Tags
03EL, 0GMX, 0FNY, 03EO; the root-normalized refinement of def-pur-frame-class
(blueprint: lem-pur-signed-twist-site-transport).

Proof:
1. Since ell belongs to (varpi_E), ell^(n+1) kills A, and ell differs from p,
so this exponent is invertible on each k-scheme. The finite etale twist theorem
makes every signed power a locally free line. Finite-root site comparison fixes
the same-root map, with constant scalars unchanged. Root-projection reduction
identifies theta by its generator formula, giving q_1=theta^-1(c tensor 1).
Its scheme square and the root-site square give the positive pullback square.
Iterate the natural tensor comparison to obtain exactly the fixed positive powers.
2. The coefficient-ring comparison is an isomorphism, so site module pullback is
exact inverse image. Apply signed-line-derived-base-change and finite-free dual
pullback to each positive power. Precompose the pulled functional by q_d^-1.
It evaluates on q_d(x) to the pulled value phi(x). This proves the displayed
evaluation equation, invertibility and uniqueness of every negative comparison.
3. On a cover trivializing the line choose e and f=q_1(e). Tensor recursion and
evaluation give q_r(e_r)=f_r for every signed r. The ordered product concatenates
positive tensors, multiplies negative functionals, and contracts opposite pairs.
In all cases it sends e_r tensor e_s to e_(r+s), including zero and equal opposite
exponents. The inverse-image tensor comparison preserves pure tensors. Both
routes of the multiplication square therefore send e_r tensor e_s to f_(r+s).
Linearity and sheaf gluing prove equality, independent of a change e to u e,
which scales the two routes by u^(r+s). This is also SignedLineProductNormalized.
4. Pair both negative pullback routes with the common positive route. The two
evaluation formulas and the fixed positive pullback square give the same pulled
evaluation. On a local basis each negative route sends e_d^dual to f_d'^dual,
so the maps agree. The canonical comparison mate is natural also on the unit.
The same uniqueness gives the identity and composition laws and geometric
evaluation compatibility, with no exchange of inverse image and an infinite limit.
5. The degree-one comparison was retained: on each local root z it sends
z tensor 1 to theta^-1(c(z) tensor 1)=sigma_X(c(z)). This is the stated
coefficient-sheaf morphism equality, before taking cohomology.
-/
theorem signedTwistSiteTransport (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hlevel : P.level = n + 1)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (b : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X (k : ℤ)) ≅ P.signedSitePro n X (k : ℤ))
    (hb : ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
      IsFiniteTateSiteComparison P.coefficients.l P.extension n X n hA k (b X a k))
    (θ : P.SignedSiteTheta n hA) (hθ : P.SignedSiteThetaNormalized n hA θ)
    (μ : P.SignedSiteProducts n)
    (hμ : ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)),
      SheafOfModules.SignedLineProductNormalized.{u + 1, u, u + 1}
      (R := integralCoefficientCommRingSheaf P.coefficients.l P.extension X n)
      (purTwistFiniteOne X P.coefficients.l P.extension n) (μ X a)) :
    ∃! q : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X r) ≅ P.signedSitePro n X r,
      (∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (k : ℕ), q X a k = b X a k) ∧
      P.SignedSiteEvaluation n hA q ∧
      P.SignedSiteMultiplication n hlevel hA μ q ∧
      (∃ τ : P.SignedSiteGeometric n,
        P.SignedSiteGeometricLaws n τ ∧ P.SignedSitePullbackSquare n hlevel hA τ q) ∧
      P.SignedSiteRootCoefficient n hlevel hA θ q := by
  classical
  obtain ⟨q, ⟨hq, he⟩, hqunique⟩ :=
    signedTwistEvaluationExtension P n hlevel hA b hb
  refine ⟨q, ⟨hq, he, ?_, ?_, ?_⟩, ?_⟩
  · exact signedTwistProductCompatibility P n hlevel hA b hb q hq he μ hμ
  · exact signedTwistGeometricCompatibility P n hlevel hA b hb q hq he
  · intro X a U W f z
    erw [show q X a (1 : ℤ) = b X a 1 from hq X a 1]
    have hr := root_normalized P n hlevel hA b hb θ hθ X a U W f z
    have hi := congrArg (fun x => (θ X a).inv.hom.app W x) hr
    have hinv (x : (P.signedSitePro n X 1).obj.obj W) :
        (θ X a).inv.hom.app W ((θ X a).hom.hom.app W x) = x :=
      ConcreteCategory.congr_hom (congr_app
        (congrArg (fun t => t.hom) (θ X a).hom_inv_id) W) x
    rw [hinv] at hi
    exact hi
  · intro q' hq'
    exact hqunique q' ⟨hq'.1, hq'.2.1⟩

end WeilConjectures.PurityFiniteSetting
