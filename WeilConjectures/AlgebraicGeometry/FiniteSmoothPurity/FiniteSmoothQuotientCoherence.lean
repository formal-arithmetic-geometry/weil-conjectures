/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCompactQuotientCocycle
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothOrdinaryTwistedCocycles
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothProQuotientTransport

/-! # Finite smooth quotient coherence

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity and
sk-lem-sp-reduction/compatibilities (blueprint: lem-pur-finite-smooth-quotient-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem pullback_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (hχ : χ = ψ.comp φ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A Y) :
    (ordinaryScalar ψ X).map ((scalarPullbackIso φ f).inv.app K) ≫
        (scalarPullbackIso ψ f).inv.app ((ordinaryScalar φ Y).obj K) ≫
        (ordinaryFinitePullback C f).map
          ((ProEtale.pbcFixedScalarExtensionComp Y.smallEtaleTopology φ ψ
            χ hχ).hom.app K) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
        χ hχ).hom.app ((ordinaryFinitePullback A f).obj K) ≫
        (scalarPullbackIso χ f).inv.app K := by
  subst χ
  let a := ProEtale.pbcFixedScalarExtensionComp Y.smallEtaleTopology φ ψ (ψ.comp φ) rfl
  let b := ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl
  let e := (ordinaryFinitePullback C f).mapIso (a.symm.app K) ≪≫
    (scalarPullbackIso ψ f).app ((ordinaryScalar φ Y).obj K) ≪≫
    (ordinaryScalar ψ X).mapIso ((scalarPullbackIso φ f).app K) ≪≫
    b.app ((ordinaryFinitePullback A f).obj K)
  have he : (scalarPullbackIso (ψ.comp φ) f).app K = e := by
    apply Iso.ext
    exact AlgebraicGeometry.Etale.scalarPullback_chain φ ψ f K
  have h := congrArg Iso.inv he
  dsimp only [e, Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv] at h
  dsimp only [a, b] at h
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]


/-- Quotient coherence for the actual pullback, twist, purity and transported maps.
Source: sk-lem-sp-reduction-compatibilities.proof.md, parts (2)--(3)
(blueprint: lem-pur-finite-smooth-quotient-coherence).
Proof: on the chosen compactification, open scalar comparisons are identity on the
open and zero off it. The direct and successive proper comparisons transpose to the
same proper counit tensored with the final coefficient ring: both balancing maps
send (x tensor b) tensor c to x tensor bc. Adjunction bijectivity and faithful
restriction of scalars identify these maps; pasting with the open comparison proves
the ordinary compact-support cocycle, including equal levels.
Scalar extension is left adjoint to restriction. Transpose its comparisons
through these adjunctions; direct and successive scalar maps both restrict to the
same multiplication map. This proves pullback/tensor/unit/shift associativity with
the specified quotient associator. The root power maps compose and agree on all
scalar/root generators, giving the twist cocycle, then its ordered tensor powers.
The tensor and pullback comparisons yield the purity-source cocycle. The
compact-support cocycle and the exceptional counit identities give the exceptional
cocycle by transposition, using naturality to move each comparison past the next
compact-support map. Finally the canonical comparison/scalar mates and the actual
origin counits have the same associative transposes. Substitute their formulas in
the pro comparisons, cancel inverse origin counits on the constructible domain,
and apply the ordinary cocycles. The compact-support case also cancels the two
inverse open/proper site comparisons. This proves all five pro cocycles, including
equal levels; no choice of origin or of root generators enters an equation. -/
theorem finiteSmoothQuotientCoherence
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X) :
  let proAssociator (T : Scheme.{u}) (ell : ℕ) {r m n : ℕ}
      (hmr : m ≤ r) (hnm : n ≤ m) :
      proScalar (FiniteReduction.quotient ell hmr) T ⋙
        proScalar (FiniteReduction.quotient ell hnm) T ≅
          proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T :=
    @ProEtale.pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (Scheme.ProEt.topology T)
      (coefficient ell r) (coefficient ell m) (coefficient ell n)
      inferInstance inferInstance inferInstance
      (FiniteReduction.quotient.{u} ell hmr) (FiniteReduction.quotient ell hnm)
      (FiniteReduction.quotient ell (hnm.trans hmr))
      (RingHom.ext (fun x ↦
        congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : coefficient.{u} ell n))
          (DFunLike.congr_fun
            (Subsingleton.elim
              (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
              ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
                (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down)));
  ExceptionalCoefficients.CompactSupportCocycle ell f ∧
  (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
    (ordinaryScalar (FiniteReduction.quotient ell hnm) X).map
        ((twists r m (hn.trans hnm) hmr).tensorPower d).hom ≫
      ((twists m n hn hnm).tensorPower d).hom =
    (ordinaryAssociator X ell hmr hnm).hom.app
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d) ≫
      ((twists r n hn (hnm.trans hmr)).tensorPower d).hom) ∧
  (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
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
      (ordinaryPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) ∧
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
      (finiteLambda ell (hnm.trans hmr) f d (twists r n hn (hnm.trans hmr))) K) ∧
  (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
    (proScalar (FiniteReduction.quotient ell hnm) X).map
        (proTwistMap d (twists r m (hn.trans hnm) hmr)) ≫
      proTwistMap d (twists m n hn hnm) =
    (proAssociator X ell hmr hnm).hom.app
        ((comparison (coefficient ell r) X).obj
          (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d)) ≫
      proTwistMap d (twists r n hn (hnm.trans hmr))) ∧
  (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      ((proPullback (coefficient ell r) f))
      ((proPullback (coefficient ell m) f))
      ((proPullback (coefficient ell n) f))
      (proPullbackMap (FiniteReduction.quotient ell hmr) f)
      (proPullbackMap (FiniteReduction.quotient ell hnm) f)
      (proPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) ∧
  (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) X),
    IsCtf (coefficient ell r) X K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proAssociator X ell hmr hnm)
      (proAssociator Y ell hmr hnm)
      (proCompact (coefficient ell r) f)
      (proCompact (coefficient ell m) f)
      (proCompact (coefficient ell n) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell hmr) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell hnm) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) ∧
  (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      (exceptional (coefficient ell r) f)
      (exceptional (coefficient ell m) f)
      (exceptional (coefficient ell n) f)
      (proCoefficientMap (FiniteReduction.quotient ell hmr) f)
      (proCoefficientMap (FiniteReduction.quotient ell hnm) f)
      (proCoefficientMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) ∧
  (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      (finiteProSource ell r f d)
      (finiteProSource ell m f d)
      (finiteProSource ell n f d)
      (finiteProLambda ell hmr f d (twists r m (hn.trans hnm) hmr))
      (finiteProLambda ell hnm f d (twists m n hn hnm))
      (finiteProLambda ell (hnm.trans hmr) f d (twists r n hn (hnm.trans hmr))) K) := by
  dsimp only
  have hpull : (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
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
      (ordinaryPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) := by
      intro r m n hn hnm hmr K
      have hq : FiniteReduction.quotient.{u} ell (hnm.trans hmr) =
          (FiniteReduction.quotient ell hnm).comp (FiniteReduction.quotient ell hmr) := by
        apply RingHom.ext
        intro x
        exact congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : coefficient.{u} ell n))
          (DFunLike.congr_fun
            (Subsingleton.elim
              (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
              ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
                (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down)
      exact pullback_chain (FiniteReduction.quotient ell hmr)
        (FiniteReduction.quotient ell hnm) (FiniteReduction.quotient ell (hnm.trans hmr)) hq f K
  have hcompact := finiteSmoothCompactQuotientCocycle ell f
  obtain ⟨htwist, hsource⟩ :=
    finiteSmoothOrdinaryTwistedCocycles ell f d hY twists hpull
  have hexception : (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
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
      (rightDerivedUpperShriek (coefficient ell r) f)
      (rightDerivedUpperShriek (coefficient ell m) f)
      (rightDerivedUpperShriek (coefficient ell n) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hmr) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hnm) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) := by
    intro r m n hn hnm hmr K hK
    exact (exceptional_naturality_and_cocycle ell r m d hmr (hn.trans hnm)
      f hY hcompact).2 n hnm hn K hK
  obtain ⟨hproTwist, hproPull, hproCompact, hproExceptional, hproSource⟩ :=
    finiteSmoothProQuotientTransport ell f d hY twists
      hcompact htwist hpull hsource hexception
  exact ⟨hcompact, htwist, hpull, hsource,
    hproTwist, hproPull, hproCompact, hproExceptional, hproSource⟩

end AlgebraicGeometry.Etale.FiniteSmoothPurity
