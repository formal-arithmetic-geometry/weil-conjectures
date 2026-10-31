/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerOrdinaryLocalization
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Localization triangle for normalized strict coefficient towers

Source: Stacks 09AH and 09BM; blueprint operations proof (2c)
(blueprint: lem-sp-tower-localization-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem derived_sequence
    {T : Scheme.{u}} (F G H : S l E T ⥤ S l E T)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (f : F ⟶ G) (g : G ⟶ H)
    (hs : ∀ M, Mono (f.app M) ∧ Epi (g.app M) ∧
      (ComposableArrows.mk₂ (f.app M) (g.app M)).Exact)
    (C : D l E T) :
    ∃ δ : H.mapDerivedCategory.obj C ⟶ (F.mapDerivedCategory.obj C)⟦(1 : ℤ)⟧,
      Triangle.mk ((deriveMap l E f).app C) ((deriveMap l E g).app C) δ ∈
        distTriang (D l E T) := by
  let K := DerivedCategory.Q.objPreimage C
  let e : DerivedCategory.Q.obj K ≅ C := DerivedCategory.Q.objObjPreimageIso C
  let fK := (NatTrans.mapHomologicalComplex f (.up ℤ)).app K
  let gK := (NatTrans.mapHomologicalComplex g (.up ℤ)).app K
  have w : fK ≫ gK = 0 := by
    apply HomologicalComplex.hom_ext
    intro q
    exact (hs (K.X q)).2.2.toIsComplex.zero 0 (by decide)
  let S := ShortComplex.mk fK gK w
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S (by
    intro q
    exact { mono_f := (hs (K.X q)).1
            epi_g := (hs (K.X q)).2.1
            exact := (hs (K.X q)).2.2.exact 0 })
  let eF : F.mapDerivedCategory.obj C ≅ DerivedCategory.Q.obj S.X₁ :=
    F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app K
  let eG : G.mapDerivedCategory.obj C ≅ DerivedCategory.Q.obj S.X₂ :=
    G.mapDerivedCategory.mapIso e.symm ≪≫ G.mapDerivedCategoryFactors.app K
  let eH : H.mapDerivedCategory.obj C ≅ DerivedCategory.Q.obj S.X₃ :=
    H.mapDerivedCategory.mapIso e.symm ≪≫ H.mapDerivedCategoryFactors.app K
  refine ⟨eH.hom ≫ DerivedCategory.triangleOfSESδ hS ≫ eF.inv⟦(1 : ℤ)⟧', ?_⟩
  apply CategoryTheory.Pretriangulated.isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished hS) _
  refine Triangle.isoMk _ _ eF eG eH ?_ ?_ ?_
  · change (deriveMap l E f).app C ≫ eG.hom = eF.hom ≫ DerivedCategory.Q.map fK
    dsimp only [eF, eG, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← (deriveMap l E f).naturality e.inv]
    simp [deriveMap, Localization.liftNatTrans_app, Localization.Lifting.iso, fK,
      Category.assoc]
  · change (deriveMap l E g).app C ≫ eH.hom = eG.hom ≫ DerivedCategory.Q.map gK
    dsimp only [eG, eH, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← (deriveMap l E g).naturality e.inv]
    simp [deriveMap, Localization.liftNatTrans_app, Localization.Lifting.iso, gK,
      Category.assoc]
  · simp

/-- Termwise open counit and closed unit give the specified derived localization
triangle, with its evaluated connecting morphism. Source: Stacks 09AH and 09BM;
blueprint operations proof (2c), final sentence
(blueprint: lem-sp-tower-localization-realization).

Proof: present the open immersion by its object of the small pro-etale site.
Apply lem-sp-semilinear-open-closed-complex-sequence to B and tau. Transport its
closed coefficient inverse images to the fixed constant-section coordinates of
o.geometry. The section-normalized comparisons and the ordinary adjunction
identities identify its unit with o.geometry i's unit. The two open ordinary
adjunction evaluation equations identify its counit with o.openOp a's counit.
Exact evaluation detects exactness on systems, so the degreewise counit-unit
sequence is one short exact sequence of strict tower complexes. Closed direct
image preserves finite limits and colimits by the same sequence-site theorem.
Choose a bounded-below strict representative of C and apply
DerivedCategory.triangleOfSES_distinguished to that short exact sequence. The
localization comparison for exact functors identifies its first two arrows with
the deriveMap expressions in LocalizationData, using Open.counit_termwise and
the ordinary closed adjunction unit. Transport the entire triangle along the
representative isomorphism, including its connecting map. Finally exact derived
evaluation is triangulated by b.calculus T and carries this very triangle,
including its boundary, to a distinguished finite triangle. Empty open or closed
parts and the zero complex require no exception. -/
theorem tower_localization_realization (b : Base l E) (o : Operations l E b)
    {Z U T : Scheme.{u}} (i : Z ⟶ T) (a : U ⟶ T)
    [IsClosedImmersion i] [IsOpenImmersion a] [QuasiCompact a]
    (complement : Set.range a = (Set.range i)ᶜ) :
    Nonempty (LocalizationData l E b o i a complement) := by
  obtain ⟨hc, hs⟩ := tower_ordinary_localization l E b o i a complement
  have : PreservesLimitsOfSize.{0, 0} (o.geometry i).push :=
    (o.geometry i).ordinaryAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits (o.geometry i).push := hc
  refine ⟨{ closedLimits := inferInstance, closedColimits := hc, triangle := ?_ }⟩
  intro C
  obtain ⟨δ, hδ⟩ := derived_sequence l E
    ((o.geometry a).pull ⋙ (o.openOp a).extension) (𝟭 (S l E T))
    ((o.geometry i).pull ⋙ (o.geometry i).push)
    (o.openOp a).ordinaryAdjunction.counit (o.geometry i).ordinaryAdjunction.unit hs C.obj
  let e₁ := (Functor.mapDerivedCategoryCompIso
    (o.geometry a).pull (o.openOp a).extension).app C.obj
  let e₂ := (Functor.mapDerivedCategoryIdIso (S l E T)).app C.obj
  let e₃ := (Functor.mapDerivedCategoryCompIso
    (o.geometry i).pull (o.geometry i).push).app C.obj
  let δ' := e₃.inv ≫ δ ≫ e₁.hom⟦(1 : ℤ)⟧'
  have ht : Triangle.mk ((o.openOp a).derivedAdjunction.counit.app C.obj)
      (((Functor.mapDerivedCategoryIdIso _).inv ≫
        deriveMap l E (o.geometry i).ordinaryAdjunction.unit ≫
        (Functor.mapDerivedCategoryCompIso (o.geometry i).pull
          (o.geometry i).push).hom).app C.obj) δ' ∈ distTriang (D l E T) := by
    apply CategoryTheory.Pretriangulated.isomorphic_distinguished _ hδ _
    refine Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm ?_ ?_ ?_
    · rw [(o.openOp a).counit_termwise]
      simp [e₁, e₂, Category.assoc]
    · simp [e₂, e₃, Category.assoc]
    · simp [δ', Category.assoc]
  refine ⟨δ', ht, ?_⟩
  intro n
  exact (Ev l E T n).map_distinguished _ ht

end AlgebraicGeometry.ProEtale.SpTowerShriek
