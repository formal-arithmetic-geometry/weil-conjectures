/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.SecSmoothPurity.MixedBaseChangeOperations
public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange

import Sheaf.SecSmoothPurity.MixedCompactSupportScalar
import Sheaf.SecSmoothPurity.MixedBaseChangeInput

/-!
# Mixed finite-coefficient base change

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-mixed.md`, node
(blueprint: det-sp-mixed-base-change).

The statement records the two coefficient/base-change squares for the canonical
compact-support and exceptional comparisons.  The maps are written in the ordinary
constant-ring pro-etale categories; the inputs are the existing bounded intrinsically
constructible finite-Tor categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Keep the subcategory objects and arrows shared during proof cleanup.
set_option cleanup.letToHave false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  directImageScalarPullbackIso directImageScalarComparison mixedOpenBaseChangeIso
  directImageConstantExchange directImageConstantAdjunction reductionOpenScalarIso
  completedAdicDerivedChange proEtaleRingDerivedAdjunction
  mixedCompactSupportExchange reductionDirectImageComparison

private theorem mixedIsoOfComposites
    {C : Type*} [Category C] {P Q R S T U : C}
    (x : P ⟶ Q) (y : Q ⟶ R) (z : R ⟶ S)
    (a : P ⟶ T) (b : T ⟶ U) (c : U ⟶ S)
    [IsIso x] [IsIso y] [IsIso z] [IsIso c]
    (h : x ≫ y ≫ z = a ≫ b ≫ c) : IsIso (a ≫ b) := by
  have : IsIso ((a ≫ b) ≫ c) := by
    rw [Category.assoc, ← h]
    infer_instance
  exact IsIso.of_isIso_comp_right (a ≫ b) c

private theorem mixedCancelIso
    {C : Type*} [Category C] {P Q R : C}
    (t : P ⟶ Q) (ht : IsIso t) {m n : Q ⟶ R} (h : t ≫ m = t ≫ n) : m = n := by
  let _ := ht
  exact (cancel_epi t).1 h

private theorem mixedCounitNaturality
    {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (F : C ⥤ D) (hF : ∀ M : P.FullSubcategory, Q (F.obj M.obj))
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adj : Q.lift (P.ι ⋙ F) hF ⊣ G)
    {K L : Q.FullSubcategory} (r : K ⟶ L) :
    F.map (G.map r).hom ≫ (adj.counit.app L).hom =
      (adj.counit.app K).hom ≫ r.hom := by
  exact congrArg (fun z ↦ z.hom) (adj.counit.naturality r)

private theorem mixedExceptionalCalc
    {C D C' D' C₁ D₁ C₁' D₁' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Category C₁] [Category D₁] [Category C₁'] [Category D₁']
    (FA : C ⥤ D) (FB : C₁ ⥤ D₁) (FAp : C' ⥤ D') (FBp : C₁' ⥤ D₁')
    (SX : C ⥤ C₁) (SY : D ⥤ D₁) (SXp : C' ⥤ C₁') (SYp : D' ⥤ D₁')
    (UA : C ⥤ C') (UB : C₁ ⥤ C₁') (VA : D ⥤ D') (VB : D₁ ⥤ D₁')
    (b : FA ⋙ SY ⟶ SX ⋙ FB) (bp : FAp ⋙ SYp ⟶ SXp ⋙ FBp)
    (βA : FA ⋙ VA ⟶ UA ⋙ FAp) (βB : FB ⋙ VB ⟶ UB ⋙ FBp)
    (lamX : SX ⋙ UB ≅ UA ⋙ SXp) (lamY : SY ⋙ VB ≅ VA ⋙ SYp)
    (K : D) (N : C) (NAp : C') (NB : C₁) (NBp₀ NBp₁ : C₁')
    (c : SX.obj N ⟶ NB) (cp : SXp.obj NAp ⟶ NBp₁)
    (eA : UA.obj N ⟶ NAp) (eB : UB.obj NB ⟶ NBp₀) (r : NBp₀ ⟶ NBp₁)
    (εA : FA.obj N ⟶ K) (εB : FB.obj NB ⟶ SY.obj K)
    (εAp : FAp.obj NAp ⟶ VA.obj K)
    (εBp₀ : FBp.obj NBp₀ ⟶ VB.obj (SY.obj K))
    (εBp₁ : FBp.obj NBp₁ ⟶ SYp.obj (VA.obj K))
    (hc : b.app N ≫ FB.map c ≫ εB = SY.map εA)
    (hcp : bp.app NAp ≫ FBp.map cp ≫ εBp₁ = SYp.map εAp)
    (heA : βA.app N ≫ FAp.map eA ≫ εAp = VA.map εA)
    (heB : βB.app NB ≫ FBp.map eB ≫ εBp₀ = VB.map εB)
    (hε : FBp.map r ≫ εBp₁ = εBp₀ ≫ lamY.hom.app K)
    (hmix : lamY.inv.app (FA.obj N) ≫ VB.map (b.app N) ≫ βB.app (SX.obj N) =
      SYp.map (βA.app N) ≫ bp.app (UA.obj N) ≫ FBp.map (lamX.inv.app N)) :
    (SYp.map (βA.app N) ≫ bp.app (UA.obj N)) ≫
        FBp.map (SXp.map eA ≫ cp) ≫ εBp₁ =
      (SYp.map (βA.app N) ≫ bp.app (UA.obj N)) ≫
        FBp.map (lamX.inv.app N ≫ UB.map c ≫ eB ≫ r) ≫ εBp₁ := by
  have hleft : (SYp.map (βA.app N) ≫ bp.app (UA.obj N)) ≫
      FBp.map (SXp.map eA ≫ cp) ≫ εBp₁ = SYp.map (VA.map εA) := by
    simp only [Functor.map_comp, Category.assoc]
    slice_lhs 2 3 => exact (bp.naturality eA).symm
    simp only [Functor.comp_map, Functor.comp_obj, Category.assoc]
    rw [hcp, ← SYp.map_comp, ← SYp.map_comp]
    exact congrArg SYp.map heA
  rw [hleft]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hmix), hε]
  slice_rhs 3 4 => exact (βB.naturality c).symm
  simp only [Functor.comp_map, Functor.comp_obj, Category.assoc]
  slice_rhs 4 6 => exact heB
  slice_rhs 2 4 =>
    exact (by simpa only [Functor.map_comp, Category.assoc] using congrArg VB.map hc)
  have hn := lamY.inv.naturality εA
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using
      congrArg (fun z ↦ z ≫ lamY.hom.app K) hn


set_option maxHeartbeats 600000 in
-- Elaborating the four full-subcategory adjunctions and their counit equations
-- exceeds the default heartbeat budget; the ordinary 60-second file limit is retained.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The compact-support and exceptional mixed coefficient/base-change identities.
All comparison maps are specified: beta is the proper/open composite above, c and c'
obey their actual coefficient-counit equations, and eA and eB obey the base-change
counit equations. The latter equations are written after precomposition by beta,
which is invertible on Dctf. They therefore specify exactly the transposes in the node.
The right adjoints are right adjoints on Dctf, with no assertion about ambient adjoints.

Source: main-20261015, sk-prop-sp-purity-bc-mixed.md
(blueprint: det-sp-mixed-base-change).

Proof:
1. Apply mixedCompactSupportScalar, the inverse-comparison compatibility square
   for the specified proper/open comparisons, to obtain the first identity.
2. At N = GA(K), mixedBaseChange_input certifies that the pullback is in Dctf.
   reductionDirectImage_isIso makes b(N) invertible, and mixedBaseChange_input
   makes beta_B(SN) invertible. The first identity therefore makes the common
   precomposition t = S(beta_A(N)) followed by b'(g'^*N) invertible.
3. Regard the two exceptional composites as maps from the same full-subcategory
   object and transpose under adjBp. The faithful inclusion identifies their
   transposes with the ambient counit composites. After precomposing by t,
   naturality of b', hcp and heA reduce the first transpose to S(g^*(epsilon_A)).
   For the second, the first mixed identity, counit naturality, naturality of
   beta_B, heB and hc give that same map. Naturality of the scalar/pullback
   isomorphism cancels the remaining pair of inverse comparisons. Cancel t and
   use injectivity of the adjunction Hom equivalence.
-/
theorem mixedBaseChange
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y X' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (cpt : Compactification f) [cpt.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (cpt.Z ↘ Spec (.of k))]
    [QuasiCompact (cpt.Z ↘ Spec (.of k))] [IsSeparated (cpt.Z ↘ Spec (.of k))]
    [cpt.i.IsOver (Spec (.of k))] [cpt.g.IsOver (Spec (.of k))]
    {Y' : Scheme.{u}} [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare g' f' f g)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A
        ((reductionCompactSupport A cpt.i
          cpt.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B
        ((reductionCompactSupport B cpt.i
          cpt.g).obj M.obj))
    (hFAp : ∀ M : spFiniteConstructibleTorCategory X' A,
      spFiniteConstructibleTor Y' A
        ((reductionCompactSupport A (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).obj M.obj))
    (hFBp : ∀ M : spFiniteConstructibleTorCategory X' B,
      spFiniteConstructibleTor Y' B
        ((reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).obj M.obj))
    (hSX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj K.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hSXp : ∀ K : spFiniteConstructibleTorCategory X' A,
      spFiniteConstructibleTor X' B ((scalarExtensionFunctor φ X').obj K.obj))
    (hSYp : ∀ K : spFiniteConstructibleTorCategory Y' A,
      spFiniteConstructibleTor Y' B ((scalarExtensionFunctor φ Y').obj K.obj))
    (hVA : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y' A ((proEtaleConstantRingDerivedPullback A g).obj K.obj))
    (hVB : ∀ K : spFiniteConstructibleTorCategory Y B,
      spFiniteConstructibleTor Y' B ((proEtaleConstantRingDerivedPullback B g).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (GAp : spFiniteConstructibleTorCategory Y' A ⥤ spFiniteConstructibleTorCategory X' A)
    (GBp : spFiniteConstructibleTorCategory Y' B ⥤ spFiniteConstructibleTorCategory X' B)
    (adjA : reductionCtfCompactSupport A cpt.i cpt.g hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B cpt.i cpt.g hFB ⊣ GB)
    (adjAp : reductionCtfCompactSupport A (mixedPullbackCompactification sq cpt).i
      (mixedPullbackCompactification sq cpt).g hFAp ⊣ GAp)
    (adjBp : reductionCtfCompactSupport B (mixedPullbackCompactification sq cpt).i
      (mixedPullbackCompactification sq cpt).g hFBp ⊣ GBp)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (cp : GAp ⋙ reductionCtfScalar φ X' hSXp ⟶ reductionCtfScalar φ Y' hSYp ⋙ GBp)
    (hc : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj ≫
        (reductionCompactSupport B cpt.i cpt.g).map (c.app K).hom ≫
        (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
      (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom)
    (hcp : ∀ K : spFiniteConstructibleTorCategory Y' A,
      (reductionDirectImageComparison φ (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).app (GAp.obj K).obj ≫
        (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).map (cp.app K).hom ≫
        (adjBp.counit.app ((reductionCtfScalar φ Y' hSYp).obj K)).hom =
      (scalarExtensionFunctor φ Y').map (adjAp.counit.app K).hom)
    (eA : ∀ K : spFiniteConstructibleTorCategory Y A,
      (proEtaleConstantRingDerivedPullback A g').obj (GA.obj K).obj ⟶
        (GAp.obj ((mixedCtfPullback A g hVA).obj K)).obj)
    (eB : ∀ K : spFiniteConstructibleTorCategory Y B,
      (proEtaleConstantRingDerivedPullback B g').obj (GB.obj K).obj ⟶
        (GBp.obj ((mixedCtfPullback B g hVB).obj K)).obj)
    (heA : ∀ K : spFiniteConstructibleTorCategory Y A,
      (mixedCompactSupportExchange A sq cpt).app (GA.obj K).obj ≫
        (reductionCompactSupport A (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).map (eA K) ≫
        (adjAp.counit.app ((mixedCtfPullback A g hVA).obj K)).hom =
      (proEtaleConstantRingDerivedPullback A g).map (adjA.counit.app K).hom)
    (heB : ∀ K : spFiniteConstructibleTorCategory Y B,
      (mixedCompactSupportExchange B sq cpt).app (GB.obj K).obj ≫
        (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).map (eB K) ≫
        (adjBp.counit.app ((mixedCtfPullback B g hVB).obj K)).hom =
      (proEtaleConstantRingDerivedPullback B g).map (adjB.counit.app K).hom) :
    (∀ M : spFiniteConstructibleTorCategory X A,
      (directImageScalarPullbackIso φ g).inv.app
          ((reductionCompactSupport A cpt.i cpt.g).obj M.obj) ≫
        (proEtaleConstantRingDerivedPullback B g).map
          ((reductionDirectImageComparison φ cpt.i cpt.g).app M.obj) ≫
        (mixedCompactSupportExchange B sq cpt).app
          ((scalarExtensionFunctor φ X).obj M.obj) =
      (scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq cpt).app M.obj) ≫
        (reductionDirectImageComparison φ (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).app
            ((proEtaleConstantRingDerivedPullback A g').obj M.obj) ≫
        (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).map
            ((directImageScalarPullbackIso φ g').inv.app M.obj)) ∧
    (∀ K : spFiniteConstructibleTorCategory Y A,
      (scalarExtensionFunctor φ X').map (eA K) ≫
          (cp.app ((mixedCtfPullback A g hVA).obj K)).hom =
        (directImageScalarPullbackIso φ g').inv.app (GA.obj K).obj ≫
          (proEtaleConstantRingDerivedPullback B g').map (c.app K).hom ≫
          eB ((reductionCtfScalar φ Y hSY).obj K) ≫
          (GBp.map (ObjectProperty.homMk
            ((directImageScalarPullbackIso φ g).hom.app K.obj))).hom) := by
  have hmix (M : spFiniteConstructibleTorCategory X A) :=
    mixedCompactSupportScalar sq cpt φ M.obj
  refine ⟨hmix, ?_⟩
  intro K
  have hN := (mixedBaseChange_input ℓ pchar hp hℓ k f cpt g' f' g sq A hA (GA.obj K).obj (GA.obj
    K).property).1
  let Q : spFiniteConstructibleTorCategory X' B :=
    ⟨(scalarExtensionFunctor φ X').obj ((proEtaleConstantRingDerivedPullback A g').obj (GA.obj
      K).obj), hSXp ⟨(proEtaleConstantRingDerivedPullback A g').obj (GA.obj K).obj, hN⟩⟩
  let L := (reductionCtfScalar φ Y' hSYp).obj ((mixedCtfPullback A g hVA).obj K)
  have hbN : IsIso ((reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj) := by
    have hbnd : Set.Finite {i : ℤ | ¬ IsZero
        ((DerivedCategory.homologyFunctor _ i).obj (GA.obj K).obj)} := by
      obtain ⟨a, z, haz, hz⟩ := (GA.obj K).property.1
      apply (Set.finite_Icc a z).subset
      intro i hi
      constructor <;> by_contra! hn
      · exact hi (hz i (.inl hn))
      · exact hi (hz i (.inr hn))
    exact (reductionDirectImage_isIso ℓ pchar hp hℓ k f cpt.i cpt.g cpt.comm.symm hA hB φ
      (GA.obj K).obj hbnd (GA.obj K).property.2.1 (GA.obj K).property.2.2).1
  have := hbN
  have : IsIso ((mixedCompactSupportExchange B sq cpt).app ((scalarExtensionFunctor φ X).obj (GA.obj
    K).obj)) :=
    (mixedBaseChange_input ℓ pchar hp hℓ k f cpt g' f' g sq B hB
      ((scalarExtensionFunctor φ X).obj (GA.obj K).obj) (hSX (GA.obj K))).2
  have hcommonIso : IsIso ((scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq
    cpt).app
    (GA.obj K).obj) ≫ (reductionDirectImageComparison φ (mixedPullbackCompactification sq cpt).i
    (mixedPullbackCompactification sq cpt).g).app ((proEtaleConstantRingDerivedPullback A g').obj
    (GA.obj K).obj)) := mixedIsoOfComposites
    ((directImageScalarPullbackIso φ g).inv.app ((reductionCompactSupport A cpt.i cpt.g).obj (GA.obj
      K).obj)) ((proEtaleConstantRingDerivedPullback B g).map ((reductionDirectImageComparison φ
      cpt.i cpt.g).app (GA.obj K).obj)) ((mixedCompactSupportExchange B sq cpt).app
      ((scalarExtensionFunctor φ X).obj (GA.obj K).obj))
    ((scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq cpt).app (GA.obj K).obj))
      ((reductionDirectImageComparison φ (mixedPullbackCompactification sq cpt).i
      (mixedPullbackCompactification sq cpt).g).app ((proEtaleConstantRingDerivedPullback A g').obj
      (GA.obj K).obj)) ((reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
      (mixedPullbackCompactification sq cpt).g).map ((directImageScalarPullbackIso φ g').inv.app
      (GA.obj K).obj))
    (hmix (GA.obj K))
  let m : Q ⟶ GBp.obj L := ObjectProperty.homMk
    ((scalarExtensionFunctor φ X').map (eA K) ≫ (cp.app ((mixedCtfPullback A g hVA).obj K)).hom)
  let n : Q ⟶ GBp.obj L := ObjectProperty.homMk
    ((directImageScalarPullbackIso φ g').inv.app (GA.obj K).obj ≫
      (proEtaleConstantRingDerivedPullback B g').map (c.app K).hom ≫
      eB ((reductionCtfScalar φ Y hSY).obj K) ≫
      (GBp.map (ObjectProperty.homMk ((directImageScalarPullbackIso φ g).hom.app K.obj))).hom)
  suffices hm : m = n by exact congrArg (fun z ↦ z.hom) hm
  apply (adjBp.homEquiv Q L).symm.injective
  apply (spFiniteConstructibleTor Y' B).ι.map_injective
  change (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
    (mixedPullbackCompactification sq cpt).g).map m.hom ≫ (adjBp.counit.app L).hom =
    (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
      (mixedPullbackCompactification sq cpt).g).map n.hom ≫ (adjBp.counit.app L).hom
  apply mixedCancelIso ((scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq
    cpt).app
    (GA.obj K).obj) ≫ (reductionDirectImageComparison φ (mixedPullbackCompactification sq cpt).i
    (mixedPullbackCompactification sq cpt).g).app ((proEtaleConstantRingDerivedPullback A g').obj
    (GA.obj K).obj)) hcommonIso
  have hε' := mixedCounitNaturality
    (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
      (mixedPullbackCompactification sq cpt).g) hFBp GBp adjBp
    (ObjectProperty.homMk ((directImageScalarPullbackIso φ g).hom.app K.obj) :
      (mixedCtfPullback B g hVB).obj ((reductionCtfScalar φ Y hSY).obj K) ⟶ L)
  have hcalc := mixedExceptionalCalc (reductionCompactSupport A cpt.i cpt.g)
    (reductionCompactSupport B
    cpt.i cpt.g) (reductionCompactSupport A (mixedPullbackCompactification sq cpt).i
    (mixedPullbackCompactification sq cpt).g) (reductionCompactSupport B
    (mixedPullbackCompactification sq cpt).i (mixedPullbackCompactification sq cpt).g)
    (scalarExtensionFunctor φ X) (scalarExtensionFunctor φ Y) (scalarExtensionFunctor φ X')
    (scalarExtensionFunctor φ Y') (proEtaleConstantRingDerivedPullback A g')
    (proEtaleConstantRingDerivedPullback B g') (proEtaleConstantRingDerivedPullback A g)
    (proEtaleConstantRingDerivedPullback B g)
    (reductionDirectImageComparison φ cpt.i cpt.g) (reductionDirectImageComparison φ
      (mixedPullbackCompactification sq cpt).i (mixedPullbackCompactification sq cpt).g)
      (mixedCompactSupportExchange A sq cpt) (mixedCompactSupportExchange B sq cpt)
      (directImageScalarPullbackIso φ g') (directImageScalarPullbackIso φ g) K.obj (GA.obj K).obj
    (GAp.obj ((mixedCtfPullback A g hVA).obj K)).obj
    (GB.obj ((reductionCtfScalar φ Y hSY).obj K)).obj
    (GBp.obj ((mixedCtfPullback B g hVB).obj
      ((reductionCtfScalar φ Y hSY).obj K))).obj
    (GBp.obj L).obj
    (c.app K).hom (cp.app ((mixedCtfPullback A g hVA).obj K)).hom
    (eA K) (eB ((reductionCtfScalar φ Y hSY).obj K))
    (GBp.map (ObjectProperty.homMk ((directImageScalarPullbackIso φ g).hom.app K.obj))).hom
    (adjA.counit.app K).hom
    (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom
    (adjAp.counit.app ((mixedCtfPullback A g hVA).obj K)).hom
    (adjBp.counit.app ((mixedCtfPullback B g hVB).obj
      ((reductionCtfScalar φ Y hSY).obj K))).hom
    (adjBp.counit.app L).hom
    (hc K) (hcp ((mixedCtfPullback A g hVA).obj K)) (heA K)
    (heB ((reductionCtfScalar φ Y hSY).obj K)) hε' (hmix (GA.obj K))
  exact hcalc

end AlgebraicGeometry.ProEtale
