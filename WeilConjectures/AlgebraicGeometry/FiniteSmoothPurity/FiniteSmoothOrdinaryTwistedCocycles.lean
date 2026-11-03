/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOrdinaryTwistCocycle
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPuritySourceCocycle

/-! # FiniteSmoothOrdinaryTwistedCocycles

A step of finite smooth quotient coherence. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Root normalization and scalar tensor balancing give ordinary twisted-source coherence.
Source: blueprint sk-lem-sp-reduction-compatibilities.proof.md, part (3), and
sk-lem-sp-reduction.proof.md, coefficient associativity.
(blueprint: lem-pur-finite-smooth-ordinary-twisted-cocycles).

Proof: the maps of root sheaves compose because their composites with the kernel
inclusion into G_m are the power maps with exponents ell^(r-m) and ell^(m-n).
The product exponent is ell^(r-n), including equal indices. The kernel inclusion
is monic. Transpose the scalar-extended root-line sheaf maps under scalar
extension/restriction. Their values on every scalar/root generator coincide by
generators and the root calculation; the tensor universal property followed by
sheafification gives equality. The single-sheaf derived normalization transports
this equality to derivedIso. Scalar extension preserves the flat root lines,
so the normalized scalarSingleMap composition is tensor balancing on these
representatives, even for nonflat coefficient quotients. Induct on d in
CoefficientLineComparison.tensorPower: d=0 is scalar unit associativity; the
successor uses scalar tensor associativity, the induction hypothesis, and the
shift comparison. The latter is the mate of the exact restriction shift, whose
composition is literal on complexes. This proves the first conclusion.
For the second, expand finiteLambda and pullbackTwistComparison. The tensor
coefficient-composition square follows on flat-term K-flat representatives:
both maps send c tensor (b tensor (x tensor y)) to the same balanced tensor,
with identical total-complex signs. Localize and use naturality of the scalar
tensorator. Substitute hpull and the first conclusion in its two factors.
Functoriality of the derived tensor bifunctor and naturality of the final scalar
associator give exactly QuotientCocycle for finiteSource. The argument is valid
on every input, hence on the stated bounded constructible finite-Tor inputs. -/
theorem finiteSmoothOrdinaryTwistedCocycles
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X)
    (hpull : (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      ((ordinaryFinitePullback (coefficient ell r) f))
      ((ordinaryFinitePullback (coefficient ell m) f))
      ((ordinaryFinitePullback (coefficient ell n) f))
      (ordinaryPullbackMap (FiniteReduction.quotient ell hmr) f)
      (ordinaryPullbackMap (FiniteReduction.quotient ell hnm) f)
      (ordinaryPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K)) :
  (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
    (ordinaryScalar (FiniteReduction.quotient ell hnm) X).map
        ((twists r m (hn.trans hnm) hmr).tensorPower d).hom ≫
      ((twists m n hn hnm).tensorPower d).hom =
    (ordinaryAssociator X ell hmr hnm).hom.app
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d) ≫
      ((twists r n hn (hnm.trans hmr)).tensorPower d).hom) ∧
  (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    DerivedCategory.boundedConstructibleFiniteTor (coefficient ell r) Y K →
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      (finiteSource ell r f d)
      (finiteSource ell m f d)
      (finiteSource ell n f d)
      (finiteLambda ell hmr f d (twists r m (hn.trans hnm) hmr))
      (finiteLambda ell hnm f d (twists m n hn hnm))
      (finiteLambda ell (hnm.trans hmr) f d (twists r n hn (hnm.trans hmr))) K) := by
  constructor
  · exact ordinaryTwistCocycle ell f d hY twists
  · exact puritySourceCocycle ell f d hY twists hpull


end AlgebraicGeometry.Etale.FiniteSmoothPurity
