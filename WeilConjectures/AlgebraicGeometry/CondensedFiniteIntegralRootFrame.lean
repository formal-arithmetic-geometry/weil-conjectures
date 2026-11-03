/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsShortExact
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Kummer.PurityFiniteKummerLevel
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit

/-! # Compatible finite and integral condensed root frames

Source: latest blueprint, `def-weil-frobenius-coefficient-twists`, order 2855,
finite reduction and scalar extension; `def-coefficient-twists-detailed`, order 1251.
(blueprint: lem-pur-condensed-finite-integral-root-frame).

All indices below are zero-based: index n denotes exponent n+1. The finite and integral
objects are exactly the published coefficient root lines, not coordinate replacements.
The elementary helpers merely spell out constant labels, pulled-back root sections,
pure tensors, and the unit section of an internal ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.ProEtale

/-- A constant residue label on any pro-etale test, through sheafification.
Source: order 2855, j maps to zeta^j
(blueprint: lem-pur-condensed-finite-integral-root-frame). -/
def condensedRootFrameLabel (X : Scheme.{u}) (N : ℕ) (U : X.ProEtᵒᵖ) (j : ZMod N) :
    ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))).obj.obj U :=
  (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app U (ULift.up j)

/-- Restrict a primitive field root to any test over Spec k and sheafify it.
Source: order 2855, the whole-site root coordinate
(blueprint: lem-pur-condensed-finite-integral-root-frame). -/
def condensedRootFrameSection (k : Type u) [Field k] (N : ℕ) [NeZero N]
    (ζ : k) (hζ : IsPrimitiveRoot ζ N) (U : (Spec (.of k)).ProEtᵒᵖ) :
    (rootsOfUnitySheaf (Spec (.of k)) N).obj.obj U :=
  (toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    (rootsOfUnityPresheaf (Spec (.of k)) N)).app U
      ((CommRingCat.rootsOfUnityFunctor N).map
        ((Scheme.ΓSpecIso (.of k)).inv ≫ U.unop.hom.appTop)
          (ULift.up (Additive.ofMul hζ.toRootsOfUnity)))

/-- The sheafified pure tensor a tensor zeta in the published free internal module.
Source: order 1251, balanced finite root tensor
(blueprint: lem-pur-condensed-finite-integral-root-frame). -/
def condensedRootFrameTensor (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (N : ℕ) (U : X.ProEtᵒᵖ) (a : R.obj.obj U)
    (z : (rootsOfUnitySheaf X N).obj.obj U) :
    ((Mod.freeFunctor R).obj (rootsOfUnitySheaf X N)).X.obj.obj U :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    R (rootsOfUnitySheaf X N)).app U (a ⊗ₜ[ℤ] z)

/-- The unit of the reconstructed section ring, with the underlying abelian carrier.
Source: order 2855, integral generator e_E = b_E(1)
(blueprint: lem-pur-condensed-finite-integral-root-frame). -/
def condensedRootFrameOne (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (U : X.ProEtᵒᵖ) : R.obj.obj U :=
  (1 : (InternalAbelianSheafModule.sectionRingSheaf
    (Scheme.ProEt.topology X) R).obj.obj U)

/-- Reduction on constant residue sheaves at consecutive positive exponents.
Source: order 2855, residue reduction
(blueprint: lem-pur-condensed-finite-integral-root-frame). -/
def condensedRootFrameReduction (X : Scheme.{u}) (l n : ℕ) :
    (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (n + 2))))) ⟶
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) :=
  (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
    (AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1)))).toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom)))

/-- The actual consecutive root-power map, with the exponent equality made explicit.
Source: order 1251, u maps to u^ell
(blueprint: lem-pur-condensed-finite-integral-root-frame). -/
def condensedRootFramePower (X : Scheme.{u}) (l n : ℕ) :
    rootsOfUnitySheaf X (l ^ (n + 2)) ⟶ rootsOfUnitySheaf X (l ^ (n + 1)) :=
  eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' l (n + 1))) ≫
    rootsOfUnitySheafPow X (l ^ (n + 1)) l

/-- Compatible primitive roots give normalized frames of all finite root lines and their
actual integral limit, including the scalar adjoints of the limit projections.

Source: latest blueprint, order 2855, natural Weil isomorphism and finite-reduction clause;
order 1251, finite tensors, Kummer comparisons and integral inverse limit.
(blueprint: lem-pur-condensed-finite-integral-root-frame).

Proof:
1. Choose a primitive ell-th root by lem-sc-primitive-root. Recursively take ell-th roots
in the algebraically closed field. A lift has order ell^(r+1), since its ell-th power
has order ell^r. This gives the compatible sequence, beginning at exponent one.
2. For any such sequence, use lem-pur-relative-kummer-coefficient-normalization with
E_0 = Q_ell and exponent r. The discrete constant comparison of
lem-pe-condensed-point-discrete-constant-comparisons and the root-only isomorphism of
lem-amb-finite-root-site-comparison give b_r on the entire pro-etale site. Their
normalization sends the constant j to zeta_r^j, also on disconnected and empty tests.
3. Power transitions commute with b_r by zeta_(r+1)^ell = zeta_r. Balanced scalar
extension (def-pur-sheaf-tensor-product) gives b_n^E(a) = zeta_n tensor a. Its inverse
sends zeta_n^j tensor a to ja. Balancing proves both inverse identities after sheafification.
4. The actual finite transition reduces a and takes the ell-th power of the root.
The recursion therefore gives the displayed square, and the inverse frames commute too.
5. Restrict scalars to O_E and take the inverse limit (def-pur-sheaf-inverse-limit).
The coordinatewise frames and inverses are inverse module maps. The canonical coefficient
limit of det-prop-sfb-qlbar-colimit-x-integral-limit gives b_E from the regular condensed
integral module. Its projection squares specify it as this limit map, and at 1 give
exactly the compatible tuple (zeta_n tensor 1)_n.
6. The adjoint of the actual n-th projection sends v tensor a to a P_n(v). In the frames
it sends (ce_E) tensor a to bar(c)a e_n. Its inverse sends b_n^E(a) to e_E tensor a;
balancing and P_n(e_E) = e_n prove the two inverse identities, without exchanging an
infinite limit with tensor or assuming flatness.
7. At any other annihilating exponent use a maps to zeta_r tensor a. The specified
Kummer comparison takes zeta_(r+k) to zeta_r by iteration of the recursion, so preserves
these frames. This proves the comparison formulas for every ordered pair of annihilating
exponents, including the chosen exponent n.
-/
theorem condensedFiniteIntegralRootFrame
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hlp : l ≠ D.p) (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (∃ ζ : ℕ → D.k, (∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1))) ∧
      ∀ n, ζ (n + 1) ^ l = ζ n) ∧
    ∀ (ζ : ℕ → D.k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ (n + 1)))
      (_hcompat : ∀ n, ζ (n + 1) ^ l = ζ n),
    ∃ b : ∀ n : ℕ,
      (constantSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) ≅
        rootsOfUnitySheaf (Spec (.of D.k)) (l ^ (n + 1)),
    ∃ B : ∀ n : ℕ,
      Mod.regular (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k))) ≅
        coefficientFiniteTwistOne l E (Spec (.of D.k)) n,
    ∃ e : Mod.regular (condensedRingObj (twistIntegralRing l E) (Spec (.of D.k))) ≅
      coefficientIntegralTwistOne l E (Spec (.of D.k)),
    (∀ (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) (j : ZMod (l ^ (n + 1))),
      (b n).hom.hom.app U (condensedRootFrameLabel _ _ U j) =
        j.val • condensedRootFrameSection D.k _ (ζ n) (hζ n) U) ∧
    (∀ n : ℕ, (b (n + 1)).hom ≫ condensedRootFramePower _ l n =
      condensedRootFrameReduction _ l n ≫ (b n).hom) ∧
    (∀ (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (a : (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k))).obj.obj U),
      (B n).hom.hom.hom.app U a =
        condensedRootFrameTensor _ _ _ U a
          (condensedRootFrameSection D.k _ (ζ n) (hζ n) U)) ∧
    (∀ n : ℕ, (B (n + 1)).hom.hom ≫
        (coefficientIntegralTwistTransition l E (Spec (.of D.k)) n).hom =
      coefficientMap (twistFiniteReduction l E n) (Spec (.of D.k)) ≫ (B n).hom.hom) ∧
    (∀ n : ℕ, e.hom ≫ limit.π (coefficientIntegralTwistSystem l E (Spec (.of D.k)))
        (op n) =
      Mod.regularToComapRegular (coefficientMap (twistReduction l E n) (Spec (.of D.k))) ≫
        (Mod.comap (coefficientMap (twistReduction l E n) (Spec (.of D.k)))).map
          (B n).hom) ∧
    (∀ (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ),
      (limit.π (coefficientIntegralTwistSystem l E (Spec (.of D.k))) (op n)).hom.hom.app U
        (e.hom.hom.hom.app U (condensedRootFrameOne _
          (condensedRingObj (twistIntegralRing l E) (Spec (.of D.k))) U)) =
      condensedRootFrameTensor _ _ _ U (condensedRootFrameOne _
        (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k))) U)
        (condensedRootFrameSection D.k _ (ζ n) (hζ n) U)) ∧
    (∀ n : ℕ, IsIso (Mod.extendHom
      (coefficientMap (twistReduction l E n) (Spec (.of D.k)))
      (limit.π (coefficientIntegralTwistSystem l E (Spec (.of D.k))) (op n)))) ∧
    (∀ (n r : ℕ), (l ^ (r + 1) : Padic.coefficientExtensionRing l E (n + 1)) = 0 →
      ∃ c : Mod.regular (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k))) ≅
          coefficientFiniteRootLine l E (Spec (.of D.k)) n r,
      (∀ (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (a : (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k))).obj.obj U),
        c.hom.hom.hom.app U a = condensedRootFrameTensor _ _ _ U a
          (condensedRootFrameSection D.k _ (ζ r) (hζ r) U)) ∧
      ∀ k : ℕ,
        ∃ c' : Mod.regular (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k))) ≅
            coefficientFiniteRootLine l E (Spec (.of D.k)) n (r + k),
        (∀ (U : (Spec (.of D.k)).ProEtᵒᵖ)
          (a : (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k))).obj.obj U),
          c'.hom.hom.hom.app U a = condensedRootFrameTensor _ _ _ U a
            (condensedRootFrameSection D.k _ (ζ (r + k)) (hζ (r + k)) U)) ∧
        c'.hom ≫ coefficientFiniteRootComparison l E (Spec (.of D.k)) n r k = c.hom) := by
  sorry

end AlgebraicGeometry.ProEtale
