/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteProCoefficientCounitTransport
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteNormalizedOrientationScalar
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-! # Finite reduction of purity and its geometric coherences

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.md
(blueprint: thm-pur-finite-reduction-of-purity).

All five clauses use the canonical pro-etale scalar, pullback, tensor, compact-support
and exceptional counit comparisons. Finite quotient maps A_{E,n} -> A_{E,m}, including
the zero quotient, are special cases of phi between finite rings killed by a common
invertible exponent N. NormalizedSmoothDatum retains the diagonal/Rees/Kummer equation,
so its alpha is a presentation of that orientation, not a freely chosen purity map.
There is no finite-field-datum restriction: the scheme formulation applies over every
field of characteristic prime to N, as well as over an invertible-exponent base.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem inverseSquareMateNaturality
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (S : C ⥤ E) (Q : D ⥤ F)
    (delta : L₁ ⋙ Q ≅ S ⋙ L₂) {K L : D} (v : K ⟶ L) :
    S.map (R₁.map v) ≫
        a₂.homEquiv _ _ (delta.inv.app (R₁.obj L) ≫ Q.map (a₁.counit.app L)) =
      a₂.homEquiv _ _ (delta.inv.app (R₁.obj K) ≫ Q.map (a₁.counit.app K)) ≫
        R₂.map (Q.map v) := by
  rw [← a₂.homEquiv_naturality_left, ← a₂.homEquiv_naturality_right]
  apply congrArg (a₂.homEquiv _ _)
  have hn := delta.inv.naturality (R₁.map v)
  have hc := a₁.counit.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at hn hc
  rw [reassoc_of% hn, ← Q.map_comp, hc, Q.map_comp, Category.assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem originReductionNaturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) {K L : proCategory A T} (v : K ⟶ L) :
    (ordinaryScalar phi T).map ((origin A T).map v) ≫ originReductionMap phi T L =
      originReductionMap phi T K ≫ (origin B T).map ((proScalar phi T).map v) := by
  with_unfolding_all
    exact inverseSquareMateNaturality
      (ProEtale.derivedComparisonAdjunction (ModuleCat A) T)
      (ProEtale.derivedComparisonAdjunction (ModuleCat B) T)
      (ordinaryScalar phi T) (proScalar phi T) (ProEtale.pbcComparisonReduction T phi) v

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pullbackCoefficientNaturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y)
    {K L : proCategory A Y} (hK : IsCtf A Y K) (hL : IsCtf A Y L) (v : K ⟶ L) :
    (proScalar phi X).map ((proPullback A f).map v) ≫ proPullbackMap phi f L =
      proPullbackMap phi f K ≫ (proPullback B f).map ((proScalar phi Y).map v) := by
  with_unfolding_all
    have hi := originInverseNaturality A Y hK hL v
    have ha := (sitePullbackIso A f).hom.naturality ((origin A Y).map v)
    have hs := (ProEtale.pbcComparisonReduction X phi).hom.naturality
      ((ordinaryFinitePullback A f).map ((origin A Y).map v))
    have hb := (scalarPullbackIso phi f).inv.naturality ((origin A Y).map v)
    have ho := originReductionNaturality phi Y v
    have hc := (ProEtale.derivedComparisonAdjunction (ModuleCat B) Y).counit.naturality
      ((proScalar phi Y).map v)
    have ht := (sitePullbackIso B f).inv.naturality
      ((origin B Y).map ((proScalar phi Y).map v))
    dsimp only [Functor.comp_map, Functor.id_map] at ha hs hb hc ht
    have hi' := congrArg (fun z ↦ (proScalar phi X).map ((proPullback A f).map z)) hi
    have ha' := congrArg (proScalar phi X).map ha
    have hb' := congrArg (comparison B X).map hb
    have ho' := congrArg (fun z ↦ (comparison B X).map
      ((ordinaryFinitePullback B f).map z)) ho
    have hc' := congrArg (proPullback B f).map hc
    simp only [Functor.map_comp] at hi' ha' hb' ho' hc'
    simp only [proPullbackMap, pullbackToOrigin, pullbackFromOrigin,
      Functor.map_comp, Category.assoc]
    erw [reassoc_of% hi', reassoc_of% ha', reassoc_of% hs,
      reassoc_of% hb', reassoc_of% ho', reassoc_of% ht, hc']

private theorem pullbackCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (K : proCategory A Y) (hK : IsCtf A Y K) : IsCtf A X ((proPullback A f).obj K) := by
  with_unfolding_all
    obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := intrinsicOrigin A Y K hK
    have hP₀ : DerivedCategory.boundedConstructibleFiniteTor A X
        ((ordinaryFinitePullback A f).obj K₀) :=
      constructibleFiniteTor_leftDerivedUpperStar (ModuleCat A) f hK₀
    exact isCtfOfIso A X
      (((proPullback A f).mapIso eK.symm) ≪≫ (sitePullbackIso A f).app K₀).symm
      (comparisonCtf A X _ hP₀)

/-- Scalar extension and pullback preserve the intrinsic finite-Tor constructible
input, and their specified coefficient comparison is invertible.
Source: finite reduction of purity, Step 2, operation compatibilities
(blueprint: thm-pur-finite-reduction-of-purity).

Proof: scalar extension preserves ctf by a bounded flat model. Ordinary pullback
preserves constructibility and the Tor interval; transport through the site
comparison proves the intrinsic assertion. Both origin counits are invertible.
The origin-reduction map is the adjoint of the site/scalar comparison followed by
the original counit. Its scalar origin is bounded below, so the site-adjunction
unit is invertible as well. The defining factors of proPullbackMap are therefore
all isomorphisms. No flatness of the coefficient homomorphism is used. -/
theorem finiteReductionOfPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsCtf B Y ((proScalar phi Y).obj K) ∧
      IsCtf B X ((proPullback B f).obj ((proScalar phi Y).obj K)) ∧
      IsIso (proPullbackMap phi f K) := by
  with_unfolding_all
    have hBK := scalarCtf phi Y K hK
    have ha := intrinsicOriginCounit A Y K hK
    have hb := intrinsicOriginCounit B Y _ hBK
    have hp := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor phi Y _
      (actualOriginCtf A Y K hK).2
    have hu := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat B) Y
      ((ordinaryScalar phi Y).obj ((origin A Y).obj K)) hp
    have ho : IsIso (originReductionMap phi Y K) := by
      unfold originReductionMap
      rw [Adjunction.homEquiv_unit]
      infer_instance
    have ht : IsIso (pullbackToOrigin f K) := by
      unfold pullbackToOrigin originInverse
      rw [dif_pos ha]
      infer_instance
    refine ⟨hBK, pullbackCtf B f _ hBK, ?_⟩
    dsimp only [proPullbackMap, pullbackFromOrigin]
    infer_instance

/-- The invertibility and the two purity/exchange squares in finite base change.
Source: the finite-reduction theorem, Step 4, and the defining three-factor smooth
exchange (blueprint: thm-pur-finite-reduction-of-purity).

Proof: scalar extension preserves the ctf input by the bounded-flat-model argument.
Both purity factors are invertible on the original and reduced inputs. In each square,
expand exchange as inverse pulled-back purity, the source comparison, and primed
purity. Smooth tensor duality makes the unprimed purity invertible. Functoriality
of pullback and the inverse identity cancel the first two factors. No equality of
arbitrary derived arrows is inferred from their stalks. -/
theorem finiteReductionOfBaseChangePuritySquares
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    [HasCompactification f] [HasCompactification f']
    [QuasiCompact f] [QuasiCompact f'] [IsSeparated f] [IsSeparated f']
    (a : X' ⟶ X) (b : Y' ⟶ Y) (sq : IsPullback a f' f b)
    (d : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X', ⊤)))
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (DA : NormalizedSmoothDatum A N hN hA f d hX)
    (DA' : NormalizedSmoothDatum A N hN hA f' d hX')
    (DB : NormalizedSmoothDatum B N hN hB f d hX)
    (DB' : NormalizedSmoothDatum B N hN hB f' d hX')
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    let QK := (proScalar phi Y).obj K
    let PA := (proPullback A b).obj K
    let PB := (proPullback B b).obj QK
    let tA := proBaseChangeSource A N hN hA f f' a b sq hX d K
    let tB := proBaseChangeSource B N hN hB f f' a b sq hX d QK
    let exA := proSmoothExchange A N hN hA f f' a b sq hX d DA.alpha DA'.alpha K
    let exB := proSmoothExchange B N hN hB f f' a b sq hX d DB.alpha DB'.alpha QK
    IsIso exA ∧ IsIso exB ∧
    (proPullback A a).map (proGamma A f _ DA.alpha K) ≫ exA =
      tA.hom ≫ proGamma A f' _ DA'.alpha PA ∧
    (proPullback B a).map (proGamma B f _ DB.alpha QK) ≫ exB =
      tB.hom ≫ proGamma B f' _ DB'.alpha PB := by
  with_unfolding_all
    dsimp only
    have hBK := scalarCtf phi Y K hK
    have hgA := proGammaIso A N hN hA f d
      (fun y ↦ by
        simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom) _ DA.alpha K hK
    have hgB := proGammaIso B N hN hB f d
      (fun y ↦ by
        simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom) _ DB.alpha _ hBK
    have hgA' := proGammaIso A N hN hA f' d
      (fun y ↦ by
        simpa only [map_natCast] using hY'.map (Y'.presheaf.germ ⊤ y trivial).hom)
      _ DA'.alpha _ (pullbackCtf A b K hK)
    have hgB' := proGammaIso B N hN hB f' d
      (fun y ↦ by
        simpa only [map_natCast] using hY'.map (Y'.presheaf.germ ⊤ y trivial).hom)
      _ DB'.alpha _ (pullbackCtf B b _ hBK)
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold proSmoothExchange
      rw [dif_pos hgA]
      infer_instance
    · unfold proSmoothExchange
      rw [dif_pos hgB]
      infer_instance
    · unfold proSmoothExchange
      rw [dif_pos hgA]
      rw [← Functor.map_comp_assoc, IsIso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    · unfold proSmoothExchange
      rw [dif_pos hgB]
      rw [← Functor.map_comp_assoc, IsIso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]

/-- The exceptional coefficient square for smooth exchange follows from the source
coefficient square alone.
Source: finite reduction of purity, Step 4, and smooth base-change coherence
(blueprint: thm-pur-finite-reduction-of-purity).

Proof: pullback and scalar extension preserve the ctf domain. Apply the purity
coefficient square to f and f', and naturality of primed B-purity to the scalar
pullback comparison. Precompose the proposed exchange square with scalar extension
of pulled-back A-purity, an isomorphism. The two defining purity/exchange squares,
the assumed source square, and naturality of the scalar pullback comparison make
the precomposed arrows equal. Cancel the isomorphism. Thus only the source
coefficient square remains to establish; no exceptional compatibility is assumed. -/
theorem finiteReductionOfSmoothExchangeOfSource
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    [HasCompactification f] [HasCompactification f']
    [QuasiCompact f] [QuasiCompact f'] [IsSeparated f] [IsSeparated f']
    (a : X' ⟶ X) (b : Y' ⟶ Y) (sq : IsPullback a f' f b)
    (d : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X', ⊤)))
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (DA : NormalizedSmoothDatum A N hN hA f d hX)
    (DA' : NormalizedSmoothDatum A N hN hA f' d hX')
    (DB : NormalizedSmoothDatum B N hN hB f d hX)
    (DB' : NormalizedSmoothDatum B N hN hB f' d hX')
    (eX : CoefficientLineComparison phi N N hA hB X)
    (eX' : CoefficientLineComparison phi N N hA hB X')
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    let QK := (proScalar phi Y).obj K
    let PA := (proPullback A b).obj K
    let SA := proSource A f (line A N hA X d)
    let SB' := proSource B f' (line B N hB X' d)
    let tA := proBaseChangeSource A N hN hA f f' a b sq hX d K
    let tB := proBaseChangeSource B N hN hB f f' a b sq hX d QK
    let exA := proSmoothExchange A N hN hA f f' a b sq hX d DA.alpha DA'.alpha K
    let exB := proSmoothExchange B N hN hB f f' a b sq hX d DB.alpha DB'.alpha QK
    ((proScalar phi X').map tA.hom ≫ proLambda f' d eX' PA ≫
        SB'.map (proPullbackMap phi b K) =
      proPullbackMap phi a (SA.obj K) ≫ (proPullback B a).map (proLambda f d eX K) ≫
        tB.hom) →
    (proScalar phi X').map exA ≫ proCoefficientMap phi f' PA ≫
        (exceptional B f').map (proPullbackMap phi b K) =
      proPullbackMap phi a ((exceptional A f).obj K) ≫
        (proPullback B a).map (proCoefficientMap phi f K) ≫ exB := by
  with_unfolding_all
    dsimp only
    intro hsource
    have hBK := scalarCtf phi Y K hK
    have hPA := pullbackCtf A b K hK
    have hPB := pullbackCtf B b _ hBK
    have hBPA := scalarCtf phi Y' _ hPA
    have hred := finiteReductionOfPurity phi N hN hA hB f d hX hY DA DB eX K hK
    have hred' := finiteReductionOfPurity phi N hN hA hB f' d hX' hY'
      DA' DB' eX' _ hPA
    have hnat := proNaturality B f' _ DB'.alpha hBPA hPB (proPullbackMap phi b K)
    have hctf := proObjectsCtf A N hN hA f d
      (fun y ↦ by
        simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom) _ DA.alpha K hK
    have hpull := pullbackCoefficientNaturality phi a hctf.1 hctf.2
      (proGamma A f _ DA.alpha K)
    have hg := proGammaIso A N hN hA f d
      (fun y ↦ by
        simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y trivial).hom) _ DA.alpha K hK
    have hsquares := finiteReductionOfBaseChangePuritySquares phi N hN hA hB f f'
      a b sq d hX hX' hY hY' DA DA' DB DB' K hK
    dsimp only at hsquares
    apply (cancel_epi ((proScalar phi X').map
      ((proPullback A a).map (proGamma A f _ DA.alpha K)))).mp
    calc
      _ = (proScalar phi X').map
            ((proBaseChangeSource A N hN hA f f' a b sq hX d K).hom) ≫
          (proScalar phi X').map
            (proGamma A f' _ DA'.alpha ((proPullback A b).obj K)) ≫
          proCoefficientMap phi f' ((proPullback A b).obj K) ≫
          (exceptional B f').map (proPullbackMap phi b K) := by
        rw [← (proScalar phi X').map_comp_assoc, hsquares.2.2.1,
          Functor.map_comp_assoc]
      _ = (proScalar phi X').map
            ((proBaseChangeSource A N hN hA f f' a b sq hX d K).hom) ≫
          proLambda f' d eX' ((proPullback A b).obj K) ≫
          (proSource B f' (line B N hB X' d)).map (proPullbackMap phi b K) ≫
          proGamma B f' _ DB'.alpha ((proPullback B b).obj ((proScalar phi Y).obj K)) := by
        rw [reassoc_of% hred'.2.2.2, ← hnat]
      _ = proPullbackMap phi a ((proSource A f (line A N hA X d)).obj K) ≫
          (proPullback B a).map (proLambda f d eX K) ≫
          (proPullback B a).map (proGamma B f _ DB.alpha ((proScalar phi Y).obj K)) ≫
          proSmoothExchange B N hN hB f f' a b sq hX d DB.alpha DB'.alpha
            ((proScalar phi Y).obj K) := by
        rw [reassoc_of% hsource, ← hsquares.2.2.2]
      _ = _ := by
        rw [← (proPullback B a).map_comp_assoc, ← hred.2.2.2,
          (proPullback B a).map_comp_assoc, ← reassoc_of% hpull]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
