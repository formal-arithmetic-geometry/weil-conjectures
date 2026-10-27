/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Mathlib.CategoryTheory.Adjunction.Basic
import all Sheaf.SecSmoothPurity.OpenScalarExchange

/-! # Open counit expansion of a restricted scalar transpose

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: lem-sp-open-scalar-restricted-transpose-expansion).

All equalities use the adjunction-preserving composition coordinates stipulated in the
node: F_g = J followed by F_f, and G_g = G_f followed by open restriction. The open
extension is the normalized ringed open extension. Its identification with the recorded
sectionwise extension is reductionOpenModel; in these coordinates the identity-proper
normalization of b_j is openScalarIso. Its counit is the actual localized open counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem counitOfUnit
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {LA : C ⥤ D} {RA : D ⥤ C} {LB : E ⥤ H} {RB : H ⥤ E}
    {SX : D ⥤ H} {SU : C ⥤ E}
    (a : LA ⊣ RA) (b : LB ⊣ RB)
    (q : RA ⋙ SU ⟶ SX ⋙ RB) (β : SU ⋙ LB ⟶ LA ⋙ SX)
    (h : ∀ K, b.unit.app (SU.obj K) ≫ RB.map (β.app K) =
      SU.map (a.unit.app K) ≫ q.app (LA.obj K)) (M : D) :
    LB.map (q.app M) ≫ b.counit.app (SX.obj M) =
      β.app (RA.obj M) ≫ SX.map (a.counit.app M) := by
  apply (b.homEquiv _ _).injective
  simp only [b.homEquiv_naturality_left, Adjunction.homEquiv_unit,
    Functor.map_comp, b.right_triangle_components, Category.comp_id,
    Functor.comp_obj, Functor.id_obj]
  simp only [← Category.assoc]
  rw [h, Category.assoc]
  have hn := q.naturality (a.counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← hn]
  simp only [← Category.assoc, ← SU.map_comp, a.right_triangle_components]
  erw [SU.map_id]
  exact (Category.id_comp _).symm

private theorem inverseTransposeExpansion
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (F : D ⥤ E)
    {M : C} {N P : D} {K : E} (q : M ⟶ R.obj N) (r : N ⟶ P)
    (ε : F.obj P ⟶ K) :
    F.map ((a.homEquiv _ _).symm (q ≫ R.map r)) ≫ ε =
      F.map (L.map q ≫ a.counit.app N) ≫ F.map r ≫ ε := by
  rw [a.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]

private theorem mapCompSubstitute
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {K : D} {l : W ⟶ Y} {β : W ⟶ X} {s : X ⟶ Y}
    {r : Y ⟶ Z} {ε : F.obj Z ⟶ K} {t : F.obj Y ⟶ K}
    (ho : l = β ≫ s) (hr : F.map r ≫ ε = t) :
    F.map l ≫ F.map r ≫ ε = F.map β ≫ F.map s ≫ t := by
  rw [ho, Functor.map_comp, Category.assoc, hr]

private theorem directImageTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {U X : Scheme.{u}} (j : U ⟶ X) :
    directImageScalarPullbackIso φ j = tensorPullbackIso φ j := rfl

attribute [local irreducible] proEtaleRingDerivedOpenAdjunction
  proEtaleRingModulePullback proEtaleRingModuleAdjunction
  reductionDirectImageComparison openScalarIso directImageScalarPullbackIso tensorPullbackIso

/-- The restricted transpose in composition coordinates. First form
`d = a_j followed by U_B(r)`, then take its inverse adjunct for the actual open
adjunction, apply F_f, and compose with the f-counit. By the composite adjunction
Hom equivalence this is precisely the inverse adjunct for g, including its counit.
The parameter F is instantiated with the specified compactification functor below.
Source: blueprint Locality paragraph; Stacks Tag 0DV0
(blueprint: lem-sp-open-scalar-restricted-transpose-expansion). -/
def openScalarRestrictedTranspose
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory Y B)
    {M : proEtaleDerivedCategory X A} {N : proEtaleDerivedCategory X B}
    {K : proEtaleDerivedCategory Y B} (ε : F.obj N ⟶ K)
    (r : (scalarExtensionFunctor φ X).obj M ⟶ N) :
    F.obj ((openExtension (A := B) j).obj
      ((scalarExtensionFunctor φ U).obj
        ((proEtaleConstantRingDerivedPullback A j).obj M))) ⟶ K :=
  F.map (((proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X B)
    (proEtaleConstantRing U B) (proEtaleConstantRingComparison j B)).homEquiv _ _).symm
      ((directImageScalarPullbackIso φ j).inv.app M ≫
        (proEtaleConstantRingDerivedPullback B j).map r)) ≫ ε

set_option maxHeartbeats 600000 in
-- The explicit derived-category counit substitutions require extra elaboration heartbeats.
/-- Open scalar-counit compatibility and both expansions of the restricted transpose.
Source: blueprint Locality paragraph
(blueprint: lem-sp-open-scalar-restricted-transpose-expansion).

Proof plan:
1. Apply lem-sp-open-proetale-counit-scalar at M = G_A K with the specified
   openScalarIso, inverse directImageScalarPullbackIso and actual open counits.
   Precompose with the inverse b_j at L = U_A M to obtain the first equation.
2. By def-weil-pbc-composite-adjunction (Adjunction.comp), the g-counit is
   F_f of the open counit followed by the f-counit. Substitute d = a_j followed
   by U_B(r). Naturality of the actual open counit at r moves r past that
   counit. Functoriality gives the first expansion of tau.
3. Substitute the assumed f-counit equation for r, and the equation from step 1
   for the open factor. Preservation of composition gives the second expansion.
   Both arrows start at F_f J_B T_U L and end at T_Y K; only b_f and b_j
   are inverted. The membership witnesses merely restrict the actual functors
   to the stated full categories; their morphisms are the ambient morphisms.
-/
theorem openScalarRestrictedTransposeExpansion
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hℓ : ℓ ≠ p)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (_hN : 1 ≤ ℓ ^ n)
    (_hA : (ℓ ^ n : A) = 0) (_hB : (ℓ ^ n : B) = 0)
    {U X Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
    (c : Compactification f)
    [c.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A c.i c.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B c.i c.g).obj M.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : (spFiniteConstructibleTor Y A).lift
      ((spFiniteConstructibleTor X A).ι ⋙ reductionCompactSupport A c.i c.g) hFA ⊣ GA)
    (adjB : (spFiniteConstructibleTor Y B).lift
      ((spFiniteConstructibleTor X B).ι ⋙ reductionCompactSupport B c.i c.g) hFB ⊣ GB)
    (K : spFiniteConstructibleTorCategory Y A)
    (hKB : spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hb : IsIso ((reductionDirectImageComparison φ c.i c.g).app (GA.obj K).obj))
    (r : (scalarExtensionFunctor φ X).obj (GA.obj K).obj ⟶
      (GB.obj ⟨(scalarExtensionFunctor φ Y).obj K.obj, hKB⟩).obj)
    (hr : (reductionCompactSupport B c.i c.g).map r ≫
        (adjB.counit.app ⟨(scalarExtensionFunctor φ Y).obj K.obj, hKB⟩).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app (GA.obj K).obj) hb ≫
        (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) :
    ((openExtension (A := B) j).map
        ((directImageScalarPullbackIso φ j).inv.app (GA.obj K).obj) ≫
      (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X B)
        (proEtaleConstantRing U B) (proEtaleConstantRingComparison j B)).counit.app
          ((scalarExtensionFunctor φ X).obj (GA.obj K).obj) =
      (openScalarIso φ j).inv.app
          ((proEtaleConstantRingDerivedPullback A j).obj (GA.obj K).obj) ≫
        (scalarExtensionFunctor φ X).map
          ((proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X A)
            (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)).counit.app
              (GA.obj K).obj)) ∧
    (openScalarRestrictedTranspose φ j (reductionCompactSupport B c.i c.g)
        (adjB.counit.app ⟨(scalarExtensionFunctor φ Y).obj K.obj, hKB⟩).hom r =
      (reductionCompactSupport B c.i c.g).map
        ((openExtension (A := B) j).map
            ((directImageScalarPullbackIso φ j).inv.app (GA.obj K).obj) ≫
          (proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X B)
            (proEtaleConstantRing U B) (proEtaleConstantRingComparison j B)).counit.app
              ((scalarExtensionFunctor φ X).obj (GA.obj K).obj)) ≫
        (reductionCompactSupport B c.i c.g).map r ≫
        (adjB.counit.app ⟨(scalarExtensionFunctor φ Y).obj K.obj, hKB⟩).hom) ∧
    (openScalarRestrictedTranspose φ j (reductionCompactSupport B c.i c.g)
        (adjB.counit.app ⟨(scalarExtensionFunctor φ Y).obj K.obj, hKB⟩).hom r =
      (reductionCompactSupport B c.i c.g).map
        ((openScalarIso φ j).inv.app
          ((proEtaleConstantRingDerivedPullback A j).obj (GA.obj K).obj)) ≫
        (reductionCompactSupport B c.i c.g).map
          ((scalarExtensionFunctor φ X).map
            ((proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X A)
              (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)).counit.app
                (GA.obj K).obj)) ≫
        @inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app (GA.obj K).obj) hb ≫
        (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) := by
  let a := proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X A)
    (proEtaleConstantRing U A) (proEtaleConstantRingComparison j A)
  let b := proEtaleRingDerivedOpenAdjunction j (proEtaleConstantRing X B)
    (proEtaleConstantRing U B) (proEtaleConstantRingComparison j B)
  have ho := counitOfUnit a b (tensorPullbackIso φ j).inv (openScalarIso φ j).inv
    (openScalarIso_unit φ j) (GA.obj K).obj
  rw [← directImageTensorIso] at ho
  change (openExtension (A := B) j).map
      ((directImageScalarPullbackIso φ j).inv.app (GA.obj K).obj) ≫
    b.counit.app ((scalarExtensionFunctor φ X).obj (GA.obj K).obj) =
    (openScalarIso φ j).inv.app
      ((proEtaleConstantRingDerivedPullback A j).obj (GA.obj K).obj) ≫
    (scalarExtensionFunctor φ X).map (a.counit.app (GA.obj K).obj) at ho
  have ht := inverseTransposeExpansion b (reductionCompactSupport B c.i c.g)
    ((directImageScalarPullbackIso φ j).inv.app (GA.obj K).obj) r
    (adjB.counit.app ⟨(scalarExtensionFunctor φ Y).obj K.obj, hKB⟩).hom
  refine ⟨ho, ht, ?_⟩
  have hs := mapCompSubstitute (reductionCompactSupport B c.i c.g)
    (l := (openExtension (A := B) j).map
      ((directImageScalarPullbackIso φ j).inv.app (GA.obj K).obj) ≫
        b.counit.app ((scalarExtensionFunctor φ X).obj (GA.obj K).obj))
    (β := (openScalarIso φ j).inv.app
      ((proEtaleConstantRingDerivedPullback A j).obj (GA.obj K).obj))
    (s := (scalarExtensionFunctor φ X).map (a.counit.app (GA.obj K).obj))
    (r := r) (ε := (adjB.counit.app
      ⟨(scalarExtensionFunctor φ Y).obj K.obj, hKB⟩).hom)
    (t := @inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app
      (GA.obj K).obj) hb ≫ (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom)
    ho hr
  exact ht.trans hs

end AlgebraicGeometry.ProEtale
