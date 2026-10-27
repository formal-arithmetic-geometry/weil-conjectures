module

public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.FiniteCompactSiteCoherence
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Counit transposes for finite exceptional composition

Source: blueprint, sec-smooth-purity/sk-prop-sp-composition/
sk-prop-sp-composition-comparisons.proof.md, (1)-(2)
(blueprint: lem-sp-finite-adjoint-compositor-transposes).

All categories below are the ordinary intrinsic constant-ring Dctf categories.
The left adjoints and scalar functors are the recorded constructions. The compositor
is normalized on every bounded-below etale witness by the proper counit mate and
open-extension comparisons, not by an arbitrary choice of natural isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The recorded compact-support restriction for a specified compactification.
Source: blueprint comparisons (1), with coefficient-independent compactifications
(blueprint: lem-sp-finite-adjoint-compositor-transposes). -/
abbrev finiteAdjointSupport (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R c.i c.g).obj M.obj)) :=
  reductionCtfCompactSupport R c.i c.g h

/-- The proper/open site comparison with the bounded-below/ambient compatibility
inserted explicitly. This is a paste of the recorded comparisons, with real data.
Source: blueprint comparisons (1); finite compact-support site coherence
(blueprint: lem-sp-finite-adjoint-compositor-transposes). -/
def finiteAdjointSiteSupportIso (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory.Plus.ι ⋙ reductionSite R X ⋙ reductionCompactSupport R c.i c.g ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c ⋙
        DerivedCategory.Plus.ι ⋙ reductionSite R Y :=
  reductionSiteCompactSupportIso R c.i c.g ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c).symm _ ≪≫
    Functor.associator _ _ _

/-- The given constructible adjunctions and the specified proper/open compositor.
The last field states its normalization through the actual site comparisons on every
etale witness whose realization belongs to Dctf. No witness of etale origin is imposed
on the objects of Dctf itself.
Source: blueprint comparisons (1)-(2); finite compact-support site coherence
(blueprint: lem-sp-finite-adjoint-compositor-transposes). -/
structure FiniteAdjointCompositorDatum (R : Type u) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) where
  hFf : ∀ M : spFiniteConstructibleTorCategory X R,
    spFiniteConstructibleTor Y R ((reductionCompactSupport R cf.i cf.g).obj M.obj)
  hFg : ∀ M : spFiniteConstructibleTorCategory Y R,
    spFiniteConstructibleTor Z R ((reductionCompactSupport R cg.i cg.g).obj M.obj)
  hFh : ∀ M : spFiniteConstructibleTorCategory X R,
    spFiniteConstructibleTor Z R ((reductionCompactSupport R ch.i ch.g).obj M.obj)
  Hf : spFiniteConstructibleTorCategory Y R ⥤ spFiniteConstructibleTorCategory X R
  Hg : spFiniteConstructibleTorCategory Z R ⥤ spFiniteConstructibleTorCategory Y R
  Hh : spFiniteConstructibleTorCategory Z R ⥤ spFiniteConstructibleTorCategory X R
  adjf : finiteAdjointSupport R cf hFf ⊣ Hf
  adjg : finiteAdjointSupport R cg hFg ⊣ Hg
  adjh : finiteAdjointSupport R ch hFh ⊣ Hh
  alpha : finiteAdjointSupport R cf hFf ⋙ finiteAdjointSupport R cg hFg ≅
    finiteAdjointSupport R ch hFh
  normalization :
    ∀ (E : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
      (hE : spFiniteConstructibleTor X R ((reductionSite R X).obj E.obj)),
      (alpha.hom.app ⟨(reductionSite R X).obj E.obj, hE⟩).hom =
        (reductionCompactSupport R cg.i cg.g).map
            ((finiteAdjointSiteSupportIso R cf).hom.app E) ≫
          (finiteAdjointSiteSupportIso R cg).hom.app
            ((Etale.rightDerivedLowerShriekOfCompactificationPlus
              (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) cf).obj E) ≫
          (reductionSite R Z).map
            ((coherenceEtaleCompositor (ULift.{u + 1, u} R) cf cg ch).hom.app E).hom ≫
          (finiteAdjointSiteSupportIso R ch).inv.app E

section Categorical

variable {C D C' D' : Type*} [Category* C] [Category* D]
  [Category* C'] [Category* D']

private theorem normalized_compositor
    {F L : C ⥤ D} {H J : D ⥤ C} (a : F ⊣ H) (b : L ⊣ J) (α : F ≅ L) :
    ∃ θ : J ≅ H,
      (∀ K, F.map (θ.hom.app K) ≫ a.counit.app K =
        α.hom.app (J.obj K) ≫ b.counit.app K) ∧
      (∀ t : J ≅ H,
        (∀ K, F.map (t.hom.app K) ≫ a.counit.app K =
          α.hom.app (J.obj K) ≫ b.counit.app K) → t = θ) := by
  let θ := (b.ofNatIsoLeft α.symm).rightAdjointUniq a
  have hθ (K : D) : F.map (θ.hom.app K) ≫ a.counit.app K =
      α.hom.app (J.obj K) ≫ b.counit.app K := by
    exact (b.ofNatIsoLeft α.symm).rightAdjointUniq_hom_app_counit a K
  refine ⟨θ, hθ, fun t ht ↦ ?_⟩
  ext K
  apply (a.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, ht, hθ]

private theorem normalized_coefficient_square
    {F L : C ⥤ D} {H J : D ⥤ C} (a : F ⊣ H) (b : L ⊣ J)
    {F' L' : C' ⥤ D'} {H' J' : D' ⥤ C'} (a' : F' ⊣ H') (b' : L' ⊣ J')
    (S : C ⥤ C') (T : D ⥤ D') (α : F ≅ L) (α' : F' ≅ L')
    (β : F ⋙ T ≅ S ⋙ F') (δ : L ⋙ T ≅ S ⋙ L')
    (θ : J ≅ H) (θ' : J' ≅ H')
    (hθ : ∀ K, F.map (θ.hom.app K) ≫ a.counit.app K =
      α.hom.app (J.obj K) ≫ b.counit.app K)
    (hθ' : ∀ K, F'.map (θ'.hom.app K) ≫ a'.counit.app K =
      α'.hom.app (J'.obj K) ≫ b'.counit.app K)
    (c : ∀ K, S.obj (H.obj K) ⟶ H'.obj (T.obj K))
    (d : ∀ K, S.obj (J.obj K) ⟶ J'.obj (T.obj K))
    (hc : ∀ K, F'.map (c K) ≫ a'.counit.app (T.obj K) =
      β.inv.app (H.obj K) ≫ T.map (a.counit.app K))
    (hd : ∀ K, L'.map (d K) ≫ b'.counit.app (T.obj K) =
      δ.inv.app (J.obj K) ≫ T.map (b.counit.app K))
    (hβ : ∀ M, T.map (α.hom.app M) ≫ δ.hom.app M =
      β.hom.app M ≫ α'.hom.app (S.obj M)) (K : D) :
    d K ≫ θ'.hom.app (T.obj K) = S.map (θ.hom.app K) ≫ c K := by
  apply (a'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hθ', α'.hom.naturality_assoc, hd]
  have hi := congrArg Iso.inv
    (show T.mapIso (α.app (J.obj K)) ≪≫ δ.app (J.obj K) =
      β.app (J.obj K) ≪≫ α'.app (S.obj (J.obj K)) from Iso.ext (hβ _))
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hi
  have hinv : α'.hom.app (S.obj (J.obj K)) ≫ δ.inv.app (J.obj K) =
      β.inv.app (J.obj K) ≫ T.map (α.hom.app (J.obj K)) := by
    rw [← cancel_epi (α'.inv.app (S.obj (J.obj K)))]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [← hi]
    simp
  rw [← Category.assoc, hinv, Category.assoc, ← T.map_comp, ← hθ, T.map_comp]
  have hn := β.inv.naturality (θ.hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hc]

end Categorical

/-- The counit-normalized exceptional compositor, its exact composite coefficient
transpose, and the resulting coefficient equation.
Source: blueprint comparisons proof (1)-(2)
(blueprint: lem-sp-finite-adjoint-compositor-transposes).

Proof:
1. Compose adjf and adjg using def-weil-pbc-composite-adjunction. Transport adjh along
   alpha to the same left adjoint. By det-sp-unique-right-adjoint there is a unique
   isomorphism theta with the displayed counit normalization, for both coefficients.
2. At K put U = Hg_A K, N = Hf_A U and a = epsilon_f,A(U). Expand the composite
   B-counit on D = c_f(U) followed by Hf_B(c_g(K)). Naturality of epsilon_f,B moves
   Hf_B(c_g(K)) through it; the f counit equation replaces the remaining pair by
   b_f(N) inverse followed by S_Y(a).
3. Use the g counit equation and naturality of b_g at a. The resulting transpose is
   b_f(N) inverse mapped by Fg_B, then b_g(Ff_A N) inverse, then S_Z(E_A(K)).
   Functors preserve inverses, so this is exactly the inverse composite shown below.
4. Precompose D with S_X(theta_A(K)). Naturality of the composite b moves theta_A
   through its inverse. Normalize theta_A and apply the assumed alpha/b equation.
   The transpose becomes alpha_B(S_X(Hh_A K)) followed by b_h(Hh_A K) inverse and
   S_Z(epsilon_h,A(K)).
5. The transpose of c_h(K) followed by theta_B(S_Z K) has precisely that value, by
   normalization of theta_B, naturality of alpha_B and the h counit equation.
   Injectivity of the composite Hom bijection proves the final equality. Every
   arrow belongs to the full B-linear derived category. No flatness is used.
-/
theorem finiteAdjointCompositorTransposes
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g))
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (DA : FiniteAdjointCompositorDatum A cf cg ch)
    (DB : FiniteAdjointCompositorDatum B cf cg ch)
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ M : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj M.obj))
    (hSZ : ∀ M : spFiniteConstructibleTorCategory Z A,
      spFiniteConstructibleTor Z B ((scalarExtensionFunctor φ Z).obj M.obj))
    (bf : finiteAdjointSupport A cf DA.hFf ⋙ reductionCtfScalar φ Y hSY ≅
      reductionCtfScalar φ X hSX ⋙ finiteAdjointSupport B cf DB.hFf)
    (bg : finiteAdjointSupport A cg DA.hFg ⋙ reductionCtfScalar φ Z hSZ ≅
      reductionCtfScalar φ Y hSY ⋙ finiteAdjointSupport B cg DB.hFg)
    (bh : finiteAdjointSupport A ch DA.hFh ⋙ reductionCtfScalar φ Z hSZ ≅
      reductionCtfScalar φ X hSX ⋙ finiteAdjointSupport B ch DB.hFh)
    (_hbf : ∀ M, (bf.hom.app M).hom =
      (reductionDirectImageComparison φ cf.i cf.g).app M.obj)
    (_hbg : ∀ M, (bg.hom.app M).hom =
      (reductionDirectImageComparison φ cg.i cg.g).app M.obj)
    (_hbh : ∀ M, (bh.hom.app M).hom =
      (reductionDirectImageComparison φ ch.i ch.g).app M.obj)
    (cfCoeff : DA.Hf ⋙ reductionCtfScalar φ X hSX ≅ reductionCtfScalar φ Y hSY ⋙ DB.Hf)
    (cgCoeff : DA.Hg ⋙ reductionCtfScalar φ Y hSY ≅ reductionCtfScalar φ Z hSZ ⋙ DB.Hg)
    (chCoeff : DA.Hh ⋙ reductionCtfScalar φ X hSX ≅ reductionCtfScalar φ Z hSZ ⋙ DB.Hh)
    (hfCounit : ∀ K,
      (finiteAdjointSupport B cf DB.hFf).map (cfCoeff.hom.app K) ≫
          DB.adjf.counit.app ((reductionCtfScalar φ Y hSY).obj K) =
        bf.inv.app (DA.Hf.obj K) ≫ (reductionCtfScalar φ Y hSY).map (DA.adjf.counit.app K))
    (hgCounit : ∀ K,
      (finiteAdjointSupport B cg DB.hFg).map (cgCoeff.hom.app K) ≫
          DB.adjg.counit.app ((reductionCtfScalar φ Z hSZ).obj K) =
        bg.inv.app (DA.Hg.obj K) ≫ (reductionCtfScalar φ Z hSZ).map (DA.adjg.counit.app K))
    (hhCounit : ∀ K,
      (finiteAdjointSupport B ch DB.hFh).map (chCoeff.hom.app K) ≫
          DB.adjh.counit.app ((reductionCtfScalar φ Z hSZ).obj K) =
        bh.inv.app (DA.Hh.obj K) ≫ (reductionCtfScalar φ Z hSZ).map (DA.adjh.counit.app K))
    (hbComp : ∀ M,
      (reductionCtfScalar φ Z hSZ).map (DA.alpha.hom.app M) ≫ bh.hom.app M =
        bg.hom.app ((finiteAdjointSupport A cf DA.hFf).obj M) ≫
          (finiteAdjointSupport B cg DB.hFg).map (bf.hom.app M) ≫
          DB.alpha.hom.app ((reductionCtfScalar φ X hSX).obj M)) :
    ∃ thetaA : DA.Hh ≅ DA.Hg ⋙ DA.Hf,
      ∃ thetaB : DB.Hh ≅ DB.Hg ⋙ DB.Hf,
        (∀ K, (finiteAdjointSupport A cf DA.hFf ⋙ finiteAdjointSupport A cg DA.hFg).map
            (thetaA.hom.app K) ≫ (DA.adjf.comp DA.adjg).counit.app K =
          DA.alpha.hom.app (DA.Hh.obj K) ≫ DA.adjh.counit.app K) ∧
        (∀ K, (finiteAdjointSupport B cf DB.hFf ⋙ finiteAdjointSupport B cg DB.hFg).map
            (thetaB.hom.app K) ≫ (DB.adjf.comp DB.adjg).counit.app K =
          DB.alpha.hom.app (DB.Hh.obj K) ≫ DB.adjh.counit.app K) ∧
        (∀ t : DA.Hh ≅ DA.Hg ⋙ DA.Hf,
          (∀ K, (finiteAdjointSupport A cf DA.hFf ⋙ finiteAdjointSupport A cg DA.hFg).map
              (t.hom.app K) ≫ (DA.adjf.comp DA.adjg).counit.app K =
            DA.alpha.hom.app (DA.Hh.obj K) ≫ DA.adjh.counit.app K) → t = thetaA) ∧
        (∀ t : DB.Hh ≅ DB.Hg ⋙ DB.Hf,
          (∀ K, (finiteAdjointSupport B cf DB.hFf ⋙ finiteAdjointSupport B cg DB.hFg).map
              (t.hom.app K) ≫ (DB.adjf.comp DB.adjg).counit.app K =
            DB.alpha.hom.app (DB.Hh.obj K) ≫ DB.adjh.counit.app K) → t = thetaB) ∧
        (∀ K : spFiniteConstructibleTorCategory Z A,
          (finiteAdjointSupport A cg DA.hFg).map
              (DA.adjf.counit.app (DA.Hg.obj K)) ≫ DA.adjg.counit.app K =
            (DA.adjf.comp DA.adjg).counit.app K) ∧
        (∀ K : spFiniteConstructibleTorCategory Z B,
          (finiteAdjointSupport B cg DB.hFg).map
              (DB.adjf.counit.app (DB.Hg.obj K)) ≫ DB.adjg.counit.app K =
            (DB.adjf.comp DB.adjg).counit.app K) ∧
        (∀ K : spFiniteConstructibleTorCategory Z A,
          ((DB.adjf.comp DB.adjg).homEquiv _ _).symm
              (cfCoeff.hom.app (DA.Hg.obj K) ≫ DB.Hf.map (cgCoeff.hom.app K)) =
            (finiteAdjointSupport B cg DB.hFg).map
                (bf.inv.app (DA.Hf.obj (DA.Hg.obj K))) ≫
              bg.inv.app
                ((finiteAdjointSupport A cf DA.hFf).obj (DA.Hf.obj (DA.Hg.obj K))) ≫
              (reductionCtfScalar φ Z hSZ).map ((DA.adjf.comp DA.adjg).counit.app K)) ∧
        (∀ K : spFiniteConstructibleTorCategory Z A,
          chCoeff.hom.app K ≫ thetaB.hom.app ((reductionCtfScalar φ Z hSZ).obj K) =
            (reductionCtfScalar φ X hSX).map (thetaA.hom.app K) ≫
              cfCoeff.hom.app (DA.Hg.obj K) ≫ DB.Hf.map (cgCoeff.hom.app K)) := by
  obtain ⟨thetaA, hthetaA, huniqA⟩ :=
    normalized_compositor (DA.adjf.comp DA.adjg) DA.adjh DA.alpha
  obtain ⟨thetaB, hthetaB, huniqB⟩ :=
    normalized_compositor (DB.adjf.comp DB.adjg) DB.adjh DB.alpha
  have htrans (K : spFiniteConstructibleTorCategory Z A) :
      ((DB.adjf.comp DB.adjg).homEquiv _ _).symm
          (cfCoeff.hom.app (DA.Hg.obj K) ≫ DB.Hf.map (cgCoeff.hom.app K)) =
        (finiteAdjointSupport B cg DB.hFg).map
            (bf.inv.app (DA.Hf.obj (DA.Hg.obj K))) ≫
          bg.inv.app
            ((finiteAdjointSupport A cf DA.hFf).obj (DA.Hf.obj (DA.Hg.obj K))) ≫
          (reductionCtfScalar φ Z hSZ).map ((DA.adjf.comp DA.adjg).counit.app K) := by
    rw [Adjunction.comp_homEquiv]
    change (DB.adjg.homEquiv _ _).symm
      ((DB.adjf.homEquiv _ _).symm
        (cfCoeff.hom.app (DA.Hg.obj K) ≫ DB.Hf.map (cgCoeff.hom.app K))) = _
    rw [Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_left_symm]
    have hf := hfCounit (DA.Hg.obj K)
    have hg := hgCounit K
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hf, hg]
    simp only [Functor.map_comp, Category.assoc]
    have hn := bg.inv.naturality (DA.adjf.counit.app (DA.Hg.obj K))
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp only [← Functor.map_comp, Adjunction.comp_counit_app]
  refine ⟨thetaA, thetaB, hthetaA, hthetaB, huniqA, huniqB,
    fun K ↦ (DA.adjf.comp_counit_app DA.adjg K).symm,
    fun K ↦ (DB.adjf.comp_counit_app DB.adjg K).symm, htrans, ?_⟩
  let beta :
      (finiteAdjointSupport A cf DA.hFf ⋙ finiteAdjointSupport A cg DA.hFg) ⋙
          reductionCtfScalar φ Z hSZ ≅
        reductionCtfScalar φ X hSX ⋙
          (finiteAdjointSupport B cf DB.hFf ⋙ finiteAdjointSupport B cg DB.hFg) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ bg ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight bf _ ≪≫
      Functor.associator _ _ _
  intro K
  apply normalized_coefficient_square (DA.adjf.comp DA.adjg) DA.adjh
    (DB.adjf.comp DB.adjg) DB.adjh (reductionCtfScalar φ X hSX)
    (reductionCtfScalar φ Z hSZ) DA.alpha DB.alpha beta bh
    thetaA thetaB hthetaA hthetaB
    (fun K ↦ cfCoeff.hom.app (DA.Hg.obj K) ≫ DB.Hf.map (cgCoeff.hom.app K))
    (fun K ↦ chCoeff.hom.app K) ?_ hhCounit ?_ K
  · intro L
    have ht := htrans L
    rw [Adjunction.homEquiv_counit] at ht
    simpa only [Functor.comp_obj, Functor.id_obj,
      beta, Iso.trans_inv,
      Iso.symm_inv, Iso.symm_hom, Functor.associator_inv_app,
      Functor.associator_hom_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht
  · intro M
    simpa only [beta, Iso.trans_hom, Iso.symm_hom, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app, Category.id_comp, Category.comp_id, Category.assoc] using hbComp M

end AlgebraicGeometry.ProEtale
