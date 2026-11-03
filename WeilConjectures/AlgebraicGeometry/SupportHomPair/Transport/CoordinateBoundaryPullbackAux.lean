/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryModel.CoordinateBoundaryGeometricPullbackDefs
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import all WeilConjectures.AlgebraicGeometry.Module.ModuleSupportedHomTransport
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Naturality of the normalized support boundary on injective models -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry

/-- On termwise injective representatives a restriction square induces a unique map
of the support kernels, and the snake-normalized connecting morphisms commute with it.
Source: Milne, Theorem 9.4, functoriality of the long exact sequence; Stacks 0117.
Proof: obtain the two short exact rows from the two normalization hypotheses.
The adjoint coefficient chain map gives maps of global and open section complexes.
Their restriction square commutes by naturality of the coefficient map and the
square of site arrows. The universal property of the target support kernel gives
its map uniquely. These three maps form a morphism of short exact complexes.
Apply `HomologicalComplex.HomologySequence.δ_naturality` and replace both snake
boundaries by the specified normalized boundaries. No inverse image of an
injective is asserted to be injective.
(blueprint: aux-lem-pur-coordinate-boundary-pullback) -/
theorem normalized_support_boundary_pair
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    (A : Type (u + 1)) [CommRing A]
    [HasSheafify J (ModuleCat.{u + 1} A)] [HasSheafify J' (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J' (ModuleCat.{u + 1} A))]
    (B : C ⥤ D) [B.IsContinuous J J']
    {V W : C} {V' W' : D} (j : W ⟶ V) (j' : W' ⟶ V')
    (δ : Sheaf.SupportSequenceBoundary J (ModuleCat.{u + 1} A) j ⊤)
    (δ' : Sheaf.SupportSequenceBoundary J' (ModuleCat.{u + 1} A) j' ⊤)
    (N : supportBoundaryNormalization J A j δ)
    (N' : supportBoundaryNormalization J' A j' δ')
    (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    (L : CochainComplex.Plus (Sheaf J' (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (L.obj.X n)]
    (b : I.obj ⟶ ((B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj)
    (t : V' ⟶ B.obj V) (s : W' ⟶ B.obj W)
    (square : s ≫ B.map j = j' ≫ t) :
    ∃! z : (((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj) ⟶
      (((Sheaf.supportedSectionsFunctor J' (ModuleCat.{u + 1} A) j').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L.obj),
      z ≫ (NatTrans.mapHomologicalComplex (Sheaf.supportedSectionsInclusion
          J' (ModuleCat.{u + 1} A) j') (ComplexShape.up ℤ)).app L.obj =
        (NatTrans.mapHomologicalComplex (Sheaf.supportedSectionsInclusion
          J (ModuleCat.{u + 1} A) j) (ComplexShape.up ℤ)).app I.obj ≫
          Sheaf.supportPairComplexSectionMap J J' (ModuleCat.{u + 1} A) B I L b t ∧
      ∀ q : ℤ,
        Sheaf.supportSequenceModelBoundary J (ModuleCat.{u + 1} A) j ⊤ δ I
            ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ (Iso.refl _) q ≫
          (HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A)
            (ComplexShape.up ℤ) (q + 1)).map z =
        (HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A)
            (ComplexShape.up ℤ) q).map
          (Sheaf.supportPairComplexSectionMap J J' (ModuleCat.{u + 1} A) B I L b s) ≫
            Sheaf.supportSequenceModelBoundary J' (ModuleCat.{u + 1} A) j' ⊤ δ' L
              ⟨DerivedCategory.Plus.Q.obj L, trivial⟩ (Iso.refl _) q := by
  obtain ⟨w, R, hδ⟩ := N I
  obtain ⟨w', R', hδ'⟩ := N' L
  let row := ShortComplex.mk _ _ w
  let row' := ShortComplex.mk _ _ w'
  have : Mono row'.f := R'.mono_f
  let f := Sheaf.supportPairComplexSectionMap J J' (ModuleCat.{u + 1} A) B I L b t
  let g := Sheaf.supportPairComplexSectionMap J J' (ModuleCat.{u + 1} A) B I L b s
  have hg : row.g ≫ g = f ≫ row'.g := by
    ext n : 1
    dsimp [row, row', f, g, Sheaf.supportPairComplexSectionMap]
    have hn := (b.f n).hom.naturality j.op
    change (I.obj.X n).obj.map j.op ≫ (b.f n).hom.app (op W) =
      (b.f n).hom.app (op V) ≫ (L.obj.X n).obj.map (B.map j).op at hn
    change (I.obj.X n).obj.map j.op ≫
        ((b.f n).hom.app (op W) ≫ (L.obj.X n).obj.map s.op) =
      ((b.f n).hom.app (op V) ≫ (L.obj.X n).obj.map t.op) ≫
        (L.obj.X n).obj.map j'.op
    rw [← Category.assoc, hn, Category.assoc, Category.assoc]
    rw [← (L.obj.X n).obj.map_comp, ← (L.obj.X n).obj.map_comp]
    rw [← op_comp, ← op_comp, square]
  have hz : row.f ≫ f ≫ row'.g = 0 := by
    rw [← hg, ← Category.assoc, row.zero, zero_comp]
  let z := R'.exact.fIsKernel.lift
    (KernelFork.ofι (row.f ≫ f) (by simpa only [Category.assoc] using hz))
  have hzι : z ≫ row'.f = row.f ≫ f := R'.exact.fIsKernel.fac _ WalkingParallelPair.zero
  refine ⟨z, ⟨hzι, ?_⟩, ?_⟩
  · intro q
    rw [hδ q, hδ' q]
    let φ : row ⟶ row' :=
      { τ₁ := z, τ₂ := f, τ₃ := g, comm₁₂ := hzι, comm₂₃ := hg.symm }
    exact HomologicalComplex.HomologySequence.δ_naturality φ R R' q (q + 1) rfl
  · intro z' hz'
    apply (cancel_mono row'.f).1
    exact hz'.1.trans hzι.symm

namespace SupportHomPair

attribute [local implicit_reducible] Functor.mapCochainComplexPlus
  Functor.sheafPushforwardContinuous Sheaf.supportedSectionsFunctor
  DerivedCategory.Plus.homologyFunctor Functor.mapDerivedCategoryPlus

variable {A : Type (u + 1)} [CommRing A] {S T : SupportHomPair A}
  {B : S.Site ⥤ T.Site} [B.IsContinuous S.topology T.topology]
  {L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
    Sheaf T.topology (ModuleCat.{u + 1} A)}
  {adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology}
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The adjunction-unit map on sections over the open object, followed by the
recorded open restriction. Source: Milne, Section 9, pullback of restriction rows
(blueprint: aux-lem-pur-coordinate-boundary-pullback). -/
def Transport.openUnit (e : Transport S T B L adj) :
    (sheafToPresheaf S.topology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op S.complement)) ⟶
    L ⋙ (sheafToPresheaf T.topology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op T.complement)) where
  app F := (adj.unit.app F).hom.app (op S.complement) ≫
    (L.obj F).obj.map e.complementMap.op
  naturality {F G} f := by
    have hu := congrArg (fun t ↦ t.hom.app (op S.complement)) (adj.unit.naturality f)
    change f.hom.app (op S.complement) ≫ (adj.unit.app G).hom.app (op S.complement) =
      (adj.unit.app F).hom.app (op S.complement) ≫
        (L.map f).hom.app (op (B.obj S.complement)) at hu
    change f.hom.app (op S.complement) ≫
      ((adj.unit.app G).hom.app (op S.complement) ≫ (L.obj G).obj.map e.complementMap.op) =
      ((adj.unit.app F).hom.app (op S.complement) ≫
        (L.obj F).obj.map e.complementMap.op) ≫ (L.map f).hom.app (op T.complement)
    rw [← Category.assoc, hu, Category.assoc, Category.assoc]
    rw [(L.map f).hom.naturality e.complementMap.op]

/-- The canonical derived open section map of a support transport. Source: Milne,
Section 9, functorial localization row, derived through the adjunction unit
(blueprint: aux-lem-pur-coordinate-boundary-pullback). -/
def Transport.openDerivedMap (e : Transport S T B L adj) :
    (sheafToPresheaf S.topology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op S.complement)).rightDerivedFunctorPlus ⟶
    L.mapDerivedCategoryPlus ⋙
      (sheafToPresheaf T.topology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op T.complement)).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := sheafToPresheaf S.topology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op S.complement))
      (G' := sheafToPresheaf T.topology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op T.complement))
      (β := L) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ e.openUnit)

omit [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
private theorem open_chain_eq (e : Transport S T B L adj)
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
    (R : CochainComplex.Plus (Sheaf T.topology (ModuleCat.{u + 1} A)))
    (t : L.mapCochainComplexPlus.obj I ⟶ R) :
    (Functor.normalizedSupportChainMap L
      (sheafToPresheaf S.topology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op S.complement))
      (sheafToPresheaf T.topology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op T.complement)) e.openUnit I R t.hom).hom =
      Sheaf.supportPairComplexSectionMap S.topology T.topology (ModuleCat.{u + 1} A)
        B I R ((adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _ t.hom) e.complementMap := by
  ext n : 1
  rw [Functor.normalizedSupportChainMap_f]
  dsimp only [Transport.openUnit, Sheaf.supportPairComplexSectionMap]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.homEquiv_unit,
    Adjunction.mapHomologicalComplex_unit_app_f]
  change ((adj.unit.app (I.obj.X n)).hom.app (op S.complement) ≫
      (L.obj (I.obj.X n)).obj.map e.complementMap.op) ≫
        (t.hom.f n).hom.app (op T.complement) =
    ((adj.unit.app (I.obj.X n)).hom.app (op S.complement) ≫
      (t.hom.f n).hom.app (op (B.obj S.complement))) ≫
        (R.obj.X n).obj.map e.complementMap.op
  have hn := (t.hom.f n).hom.naturality e.complementMap.op
  change (L.obj (I.obj.X n)).obj.map e.complementMap.op ≫
    (t.hom.f n).hom.app (op T.complement) =
      (t.hom.f n).hom.app (op (B.obj S.complement)) ≫
        (R.obj.X n).obj.map e.complementMap.op at hn
  rw [Category.assoc, Category.assoc, hn]

omit [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
private theorem support_chain_inclusion (e : Transport S T B L adj)
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
    (R : CochainComplex.Plus (Sheaf T.topology (ModuleCat.{u + 1} A)))
    (t : L.mapCochainComplexPlus.obj I ⟶ R) :
    (Functor.normalizedSupportChainMap L S.sections T.sections e.supportUnit I R t.hom).hom ≫
      (NatTrans.mapHomologicalComplex (Sheaf.supportedSectionsInclusion
        T.topology (ModuleCat.{u + 1} A) T.restriction) (.up ℤ)).app R.obj =
    (NatTrans.mapHomologicalComplex (Sheaf.supportedSectionsInclusion
      S.topology (ModuleCat.{u + 1} A) S.restriction) (.up ℤ)).app I.obj ≫
      Sheaf.supportPairComplexSectionMap S.topology T.topology (ModuleCat.{u + 1} A)
        B I R ((adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _ t.hom) e.terminalMap := by
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.normalizedSupportChainMap_f,
    NatTrans.mapHomologicalComplex_app_f]
  have hn := (Sheaf.supportedSectionsInclusion T.topology
    (ModuleCat.{u + 1} A) T.restriction).naturality (t.hom.f n)
  rw [Category.assoc, hn, ← Category.assoc]
  erw [e.supportUnit_spec]
  simp only [Sheaf.supportPairComplexSectionMap, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Adjunction.homEquiv_unit, Adjunction.mapHomologicalComplex_unit_app_f]
  change (kernel.ι ((I.obj.X n).obj.map S.restriction.op) ≫
    (adj.unit.app (I.obj.X n)).hom.app (op S.terminal) ≫
      (L.obj (I.obj.X n)).obj.map e.terminalMap.op) ≫
        (t.hom.f n).hom.app (op T.terminal) =
    kernel.ι ((I.obj.X n).obj.map S.restriction.op) ≫
      (((adj.unit.app (I.obj.X n)).hom.app (op S.terminal) ≫
        (t.hom.f n).hom.app (op (B.obj S.terminal))) ≫
          (R.obj.X n).obj.map e.terminalMap.op)
  simp only [Category.assoc]
  have ht := (t.hom.f n).hom.naturality e.terminalMap.op
  change (L.obj (I.obj.X n)).obj.map e.terminalMap.op ≫
      (t.hom.f n).hom.app (op T.terminal) =
    (t.hom.f n).hom.app (op (B.obj S.terminal)) ≫
      (R.obj.X n).obj.map e.terminalMap.op at ht
  rw [ht]


private theorem modelIso_refl
    (G : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A) [G.Additive]
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (q : ℤ) :
    (Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} A) G I
      (DerivedCategory.Plus.Q.obj I) (Iso.refl _) q).hom =
    (DerivedCategory.Plus.homologyFunctorObjQIso (G.mapCochainComplexPlus.obj I) q).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
        (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient _).obj I)) := by
  simp only [Sheaf.supportSequenceModelIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, asIso_hom]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem transport_model
    (G : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A) [G.Additive]
    (G' : Sheaf T.topology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A) [G'.Additive]
    (τ : G ⟶ L ⋙ G')
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
    (R : CochainComplex.Plus (Sheaf T.topology (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (R.obj.X n)]
    (t : L.mapCochainComplexPlus.obj I ⟶ R) (q : ℤ) :
    (Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} A) G I
      (DerivedCategory.Plus.Q.obj I) (Iso.refl _) q).hom ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
        ((Functor.normalizedSupportTransport L G G' τ).app (DerivedCategory.Plus.Q.obj I)) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
        (G'.rightDerivedFunctorPlus.map
          (L.mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.quotient _).obj I) ≫ DerivedCategory.Plus.Q.map t)) =
    HomologicalComplex.homologyMap
      (Functor.normalizedSupportChainMap L G G' τ I R t.hom).hom q ≫
      (Sheaf.supportSequenceModelIso T.topology (ModuleCat.{u + 1} A) G' R
        (DerivedCategory.Plus.Q.obj R) (Iso.refl _) q).hom := by
  rw [modelIso_refl, modelIso_refl]
  exact Functor.normalizedSupportTransport_homology_comp L G G' τ I R t q


private theorem boundary_naturality_injective (e : Transport S T B L adj)
    (δ : Sheaf.SupportSequenceBoundary S.topology (ModuleCat.{u + 1} A) S.restriction ⊤)
    (δ' : Sheaf.SupportSequenceBoundary T.topology (ModuleCat.{u + 1} A) T.restriction ⊤)
    (N : supportBoundaryNormalization S.topology A S.restriction δ)
    (N' : supportBoundaryNormalization T.topology A T.restriction δ')
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (q : ℤ) :
    (δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) (q + 1)).map
        (e.derivedMap.app (DerivedCategory.Plus.Q.obj I)) =
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
      (e.openDerivedMap.app (DerivedCategory.Plus.Q.obj I)) ≫
        (δ' q).app ⟨L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I), trivial⟩ := by
  let O := sheafToPresheaf S.topology (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op S.complement)
  let O' := sheafToPresheaf T.topology (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op T.complement)
  let M := L.mapCochainComplexPlus.obj I
  obtain ⟨m, hm⟩ := M.2
  have : M.obj.IsStrictlyGE m := hm
  obtain ⟨R₀, _, t, ht⟩ := CochainComplex.Plus.exists_quasiIso_injective M m
  let R := (InjectiveObject.ι (Sheaf T.topology (ModuleCat.{u + 1} A))).mapCochainComplexPlus.obj R₀
  have hi (n : ℤ) : Injective (R.obj.X n) := (R₀.obj.X n).2
  have : QuasiIso t.hom := ht
  have : IsIso (DerivedCategory.Plus.Q.map t) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  let eD : L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I) ≅
      DerivedCategory.Plus.Q.obj R :=
    L.mapDerivedCategoryPlusFactorsh.app ((HomotopyCategory.Plus.quotient _).obj I) ≪≫
      asIso (DerivedCategory.Plus.Q.map t)
  let b := (adj.mapHomologicalComplex (.up ℤ)).homEquiv I.obj R.obj t.hom
  obtain ⟨z₀, hz₀, _⟩ := normalized_support_boundary_pair S.topology T.topology A B
    S.restriction T.restriction δ δ' N N' I R b e.terminalMap e.complementMap
      e.restriction_square
  let z := (Functor.normalizedSupportChainMap L S.sections T.sections e.supportUnit
    I R t.hom).hom
  let g := (Functor.normalizedSupportChainMap L O O' e.openUnit I R t.hom).hom
  have hmono : Mono ((NatTrans.mapHomologicalComplex (Sheaf.supportedSectionsInclusion
      T.topology (ModuleCat.{u + 1} A) T.restriction) (.up ℤ)).app R.obj) := by
    obtain ⟨w, hR, _⟩ := N' R
    exact hR.mono_f
  have hz : z₀ = z := (cancel_mono _).1
    (hz₀.1.trans (support_chain_inclusion e I R t).symm)
  have hd := hz₀.2 q
  rw [hz, ← open_chain_eq e I R t] at hd
  let EI := Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} A) O I
    (DerivedCategory.Plus.Q.obj I) (Iso.refl _) q
  let SI := Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} A) S.sections I
    (DerivedCategory.Plus.Q.obj I) (Iso.refl _) (q + 1)
  let ER := Sheaf.supportSequenceModelIso T.topology (ModuleCat.{u + 1} A) O' R
    (DerivedCategory.Plus.Q.obj R) (Iso.refl _) q
  let SR := Sheaf.supportSequenceModelIso T.topology (ModuleCat.{u + 1} A) T.sections R
    (DerivedCategory.Plus.Q.obj R) (Iso.refl _) (q + 1)
  let dI := (δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩
  let dK := (δ' q).app ⟨L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I), trivial⟩
  let dR := (δ' q).app ⟨DerivedCategory.Plus.Q.obj R, trivial⟩
  let di := Sheaf.supportSequenceModelBoundary S.topology (ModuleCat.{u + 1} A)
    S.restriction ⊤ δ I ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ (Iso.refl _) q
  let dr := Sheaf.supportSequenceModelBoundary T.topology (ModuleCat.{u + 1} A)
    T.restriction ⊤ δ' R ⟨DerivedCategory.Plus.Q.obj R, trivial⟩ (Iso.refl _) q
  let ds := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) (q + 1)).map
    (e.derivedMap.app (DerivedCategory.Plus.Q.obj I))
  let do' := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
    (e.openDerivedMap.app (DerivedCategory.Plus.Q.obj I))
  let ss := (Sheaf.supportHypercohomologyFunctor T.topology (ModuleCat.{u + 1} A)
    T.restriction (q + 1)).map eD.hom
  let oo := (Sheaf.sectionHypercohomologyFunctor T.topology (ModuleCat.{u + 1} A)
    T.complement q).map eD.hom
  let hzmap := HomologicalComplex.homologyMap z (q + 1)
  let hgmap := HomologicalComplex.homologyMap g q
  have hSI : SI.hom ≫ ds ≫ ss = hzmap ≫ SR.hom := by
    simpa only [SI, ds, ss, hzmap, z, SR, eD, Iso.trans_hom, asIso_hom,
      Functor.normalizedSupportTransport_eq, Transport.derivedMap,
      Sheaf.supportHypercohomologyFunctor, CategoryTheory.Functor.comp_map, Iso.app_hom] using
      transport_model S.sections T.sections e.supportUnit I R t (q + 1)
  have hOI : EI.hom ≫ do' ≫ oo = hgmap ≫ ER.hom := by
    simpa only [EI, do', oo, hgmap, g, ER, eD, Iso.trans_hom, asIso_hom,
      Functor.normalizedSupportTransport_eq, Transport.openDerivedMap,
      Sheaf.sectionHypercohomologyFunctor, CategoryTheory.Functor.comp_map, Iso.app_hom] using
      transport_model O O' e.openUnit I R t q
  have hbi : EI.hom ≫ dI = di ≫ SI.hom := by
    change EI.hom ≫ dI = (EI.hom ≫ dI ≫ SI.inv) ≫ SI.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hbr : ER.hom ≫ dR = dr ≫ SR.hom := by
    change ER.hom ≫ dR = (ER.hom ≫ dR ≫ SR.inv) ≫ SR.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn : oo ≫ dR = dK ≫ ss := by
    exact (δ' q).naturality (ObjectProperty.homMk
      (X := ⟨L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I), trivial⟩)
      (Y := ⟨DerivedCategory.Plus.Q.obj R, trivial⟩) eD.hom)
  change di ≫ hzmap = hgmap ≫ dr at hd
  have hfull : EI.hom ≫ dI ≫ ds ≫ ss = EI.hom ≫ do' ≫ dK ≫ ss := by
    calc
      _ = di ≫ (SI.hom ≫ ds ≫ ss) := by
        simp only [← Category.assoc]
        rw [hbi]
      _ = (di ≫ hzmap) ≫ SR.hom := by rw [hSI]; simp only [Category.assoc]
      _ = hgmap ≫ (dr ≫ SR.hom) := by rw [hd]; simp only [Category.assoc]
      _ = (hgmap ≫ ER.hom) ≫ dR := by rw [← hbr]; simp only [Category.assoc]
      _ = EI.hom ≫ do' ≫ (oo ≫ dR) := by rw [← hOI]; simp only [Category.assoc]
      _ = _ := by rw [hn]
  apply (cancel_epi EI.hom).1
  apply (cancel_mono ss).1
  simpa only [Category.assoc] using hfull


/-- A support transport commutes with every snake-normalized boundary.
Source: Milne, Theorem 9.4, and Stacks Tags 0117 and 05TI.
Proof: choose a bounded-below injective representative I of K. Resolve LI by R;
the adjoint of LI → R gives the section-row morphism. The kernel inclusion fixes
its support component. The normalized model boundary equation is delta naturality
for this morphism of short exact complexes. The right-derived base-change unit
computes the two derived maps by these chain maps. Cancel the injective-model
comparison isomorphisms. Finally transport from QI to K by naturality.
(blueprint: aux-lem-pur-coordinate-boundary-pullback). -/
theorem Transport.boundary_naturality (e : Transport S T B L adj)
    (δ : Sheaf.SupportSequenceBoundary S.topology (ModuleCat.{u + 1} A) S.restriction ⊤)
    (δ' : Sheaf.SupportSequenceBoundary T.topology (ModuleCat.{u + 1} A) T.restriction ⊤)
    (N : supportBoundaryNormalization S.topology A S.restriction δ)
    (N' : supportBoundaryNormalization T.topology A T.restriction δ')
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (q : ℤ) :
    (δ q).app ⟨K, trivial⟩ ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) (q + 1)).map
        (e.derivedMap.app K) =
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
      (e.openDerivedMap.app K) ≫
        (δ' q).app ⟨L.mapDerivedCategoryPlus.obj K, trivial⟩ := by
  obtain ⟨m, hm⟩ := K.2
  have : K.IsGE m := (K.isGE_ι_obj_iff m).mp hm
  obtain ⟨I₀, _, ⟨f⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K m
  let I := (InjectiveObject.ι (Sheaf S.topology (ModuleCat.{u + 1} A))).mapCochainComplexPlus.obj I₀
  have hi (n : ℤ) : Injective (I.obj.X n) := (I₀.obj.X n).2
  let X := Sheaf.sectionHypercohomologyFunctor S.topology (ModuleCat.{u + 1} A)
    S.complement q
  let Sg := Sheaf.supportHypercohomologyFunctor S.topology (ModuleCat.{u + 1} A)
    S.restriction (q + 1)
  let X' := Sheaf.sectionHypercohomologyFunctor T.topology (ModuleCat.{u + 1} A)
    T.complement q
  let Tg := Sheaf.supportHypercohomologyFunctor T.topology (ModuleCat.{u + 1} A)
    T.restriction (q + 1)
  let hs := fun K ↦ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) (q + 1)).map
    (e.derivedMap.app K)
  let ho := fun K ↦ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
    (e.openDerivedMap.app K)
  have hδ : X.map f.hom ≫ (δ q).app ⟨K, trivial⟩ =
      (δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ ≫ Sg.map f.hom :=
    (δ q).naturality (ObjectProperty.homMk
      (X := ⟨DerivedCategory.Plus.Q.obj I, trivial⟩) (Y := ⟨K, trivial⟩) f.hom)
  have hδ' : X'.map (L.mapDerivedCategoryPlus.map f.hom) ≫
      (δ' q).app ⟨L.mapDerivedCategoryPlus.obj K, trivial⟩ =
    (δ' q).app ⟨L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I), trivial⟩ ≫
      Tg.map (L.mapDerivedCategoryPlus.map f.hom) :=
    (δ' q).naturality (ObjectProperty.homMk
      (X := ⟨L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I), trivial⟩)
      (Y := ⟨L.mapDerivedCategoryPlus.obj K, trivial⟩)
      (L.mapDerivedCategoryPlus.map f.hom))
  have hS : Sg.map f.hom ≫ hs K = hs (DerivedCategory.Plus.Q.obj I) ≫
      Tg.map (L.mapDerivedCategoryPlus.map f.hom) := by
    have hh := congrArg (DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{u + 1} A) (q + 1)).map (e.derivedMap.naturality f.hom)
    simpa only [Sg, Tg, hs, I, Sheaf.supportHypercohomologyFunctor,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map] using hh
  have hO : X.map f.hom ≫ ho K = ho (DerivedCategory.Plus.Q.obj I) ≫
      X'.map (L.mapDerivedCategoryPlus.map f.hom) := by
    have hh := congrArg (DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{u + 1} A) q).map (e.openDerivedMap.naturality f.hom)
    simpa only [X, X', ho, I, Sheaf.sectionHypercohomologyFunctor,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map] using hh
  have hc := boundary_naturality_injective e δ δ' N N' I q
  apply (cancel_epi (X.map f.hom)).1
  calc
    _ = (δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ ≫ (Sg.map f.hom ≫ hs K) := by
      simp only [← Category.assoc]
      rw [hδ]
    _ = ((δ q).app ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ ≫
        hs (DerivedCategory.Plus.Q.obj I)) ≫ Tg.map (L.mapDerivedCategoryPlus.map f.hom) := by
      rw [hS]; simp only [Category.assoc]
    _ = ho (DerivedCategory.Plus.Q.obj I) ≫
        ((δ' q).app ⟨L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I), trivial⟩ ≫
          Tg.map (L.mapDerivedCategoryPlus.map f.hom)) := by
      rw [hc]; simp only [ho, Category.assoc]
    _ = (ho (DerivedCategory.Plus.Q.obj I) ≫ X'.map (L.mapDerivedCategoryPlus.map f.hom)) ≫
        (δ' q).app ⟨L.mapDerivedCategoryPlus.obj K, trivial⟩ := by
      rw [← hδ']; simp only [Category.assoc]
    _ = _ := by rw [← hO]; simp only [ho, Category.assoc]


/-- Naturality of a normalized boundary after a coefficient map, evaluated on a class.
Source: Milne, Theorem 9.4, pair and coefficient functoriality.
Proof: compose boundary naturality with the target support coefficient map, and use
naturality of the target boundary to move that coefficient map before the boundary.
Evaluate the resulting morphism equality on the input class.
(blueprint: aux-lem-pur-coordinate-boundary-pullback). -/
theorem Transport.boundary_coefficient_apply (e : Transport S T B L adj)
    (δ : Sheaf.SupportSequenceBoundary S.topology (ModuleCat.{u + 1} A) S.restriction ⊤)
    (δ' : Sheaf.SupportSequenceBoundary T.topology (ModuleCat.{u + 1} A) T.restriction ⊤)
    (N : supportBoundaryNormalization S.topology A S.restriction δ)
    (N' : supportBoundaryNormalization T.topology A T.restriction δ')
    {K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))}
    {K' : DerivedCategory.Plus (Sheaf T.topology (ModuleCat.{u + 1} A))}
    (b : L.mapDerivedCategoryPlus.obj K ⟶ K') (q : ℤ)
    (x : (Sheaf.sectionHypercohomologyFunctor S.topology
      (ModuleCat.{u + 1} A) S.complement q).obj K)
    (y : (Sheaf.sectionHypercohomologyFunctor T.topology
      (ModuleCat.{u + 1} A) T.complement q).obj K')
    (hxy : ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
      (e.openDerivedMap.app K) ≫
      (Sheaf.sectionHypercohomologyFunctor T.topology
        (ModuleCat.{u + 1} A) T.complement q).map b) x = y) :
    e.coefficientGroupMap b (q + 1) ((δ q).app ⟨K, trivial⟩ x) =
      (δ' q).app ⟨K', trivial⟩ y := by
  have hn := (δ' q).naturality (ObjectProperty.homMk
    (X := ⟨L.mapDerivedCategoryPlus.obj K, trivial⟩) (Y := ⟨K', trivial⟩) b)
  change (Sheaf.sectionHypercohomologyFunctor T.topology
      (ModuleCat.{u + 1} A) T.complement q).map b ≫ (δ' q).app ⟨K', trivial⟩ =
    (δ' q).app ⟨L.mapDerivedCategoryPlus.obj K, trivial⟩ ≫
      (Sheaf.supportHypercohomologyFunctor T.topology
        (ModuleCat.{u + 1} A) T.restriction (q + 1)).map b at hn
  have hh : (δ q).app ⟨K, trivial⟩ ≫ e.coefficientGroupMap b (q + 1) =
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
        (e.openDerivedMap.app K) ≫
        (Sheaf.sectionHypercohomologyFunctor T.topology
          (ModuleCat.{u + 1} A) T.complement q).map b) ≫
        (δ' q).app ⟨K', trivial⟩ := by
    unfold Transport.coefficientGroupMap
    rw [← Category.assoc, e.boundary_naturality δ δ' N N' K q]
    rw [Category.assoc, ← hn, ← Category.assoc]
  have he := ConcreteCategory.congr_hom hh x
  rw [← hxy]
  exact he

end SupportHomPair

end AlgebraicGeometry
