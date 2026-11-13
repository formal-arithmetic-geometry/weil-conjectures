/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism

/-!
# A uniform cardinality bound for constructible abelian sheaves

Source: Stacks Project, Tags 03RW and 095E, and the finite-cover argument in step 1 of
`lem-weil-pbc-curve-constructible-annihilator`.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The pullback of a constant chart is constant with the same value. -/
private noncomputable def constantChartPullbackIso {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (M : Type (u + 1))
    (e : G.over U ≅ (constantSheaf (X.smallEtaleTopology.over U)
      (Type (u + 1))).obj M) :
    (etaleSetPullback U.hom).obj G ≅
      (constantSheaf U.left.smallEtaleTopology (Type (u + 1))).obj M := by
  have : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom).IsContinuous
      (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
      (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale) :=
    Scheme.isContinuous_overPullback @AlgebraicGeometry.Etale
      @AlgebraicGeometry.Etale le_rfl U.hom
  have : (MorphismProperty.Over.map ⊤ U.prop).IsContinuous
      (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale)
      (X.smallGrothendieckTopology @AlgebraicGeometry.Etale) :=
    Scheme.isContinuous_overMap U.prop le_rfl
  let a₁ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ U.hom) (Type (u + 1))
    (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let siteAdj := MorphismProperty.Over.mapPullbackAdj
    @AlgebraicGeometry.Etale ⊤ U.hom U.prop trivial
  let a₂ := siteAdj.sheafPushforwardContinuous (E := Type (u + 1))
    (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale)
    (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
  let ρ := a₁.leftAdjointUniq a₂
  let σ : (Etale.overSheafEquiv U (Type (u + 1))).functor.obj (G.over U) ≅
      ((MorphismProperty.Over.map ⊤ U.prop).sheafPushforwardContinuous
        (Type (u + 1)) (U.left.smallGrothendieckTopology @AlgebraicGeometry.Etale)
          (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)).obj G :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerRight (NatIso.op (Etale.etaleToOverCompForgetIso U).symm) G.obj)
  exact ρ.app G ≪≫ σ.symm ≪≫
    (Etale.overSheafEquiv U (Type (u + 1))).functor.mapIso e ≪≫
    ((Etale.overEquiv U).constantSheafSheafCongrIso
      (X.smallEtaleTopology.over U) U.left.smallEtaleTopology
      (Type (u + 1)) Over.mkIdTerminal).app M

/-- A geometric stalk through a constant chart is in bijection with its constant value. -/
private theorem nonempty_equiv_stalk_constantChart {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (M : Type (u + 1))
    (e : G.over U ≅ (constantSheaf (X.smallEtaleTopology.over U)
      (Type (u + 1))).obj M)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ U.left) :
    Nonempty ((((pointSmallEtale (t ≫ U.hom)).sheafFiber).obj G) ≃ M) := by
  obtain ⟨c, hc, -⟩ := etaleSetInverseImageStalkGerm X U.left U.hom G Ω t
  let d := (pointSmallEtale t).sheafFiber.mapIso (constantChartPullbackIso G U M e) ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso M
  exact ⟨(Equiv.ofBijective c hc).symm.trans d.toEquiv⟩

/-- A geometric stalk through a constant chart has the cardinality of its constant value. -/
private theorem card_stalk_constantChart {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale)
    (M : Type (u + 1))
    (e : G.over U ≅ (constantSheaf (X.smallEtaleTopology.over U)
      (Type (u + 1))).obj M)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ U.left) :
    Nat.card (((pointSmallEtale (t ≫ U.hom)).sheafFiber).obj G) = Nat.card M :=
  Nat.card_congr (nonempty_equiv_stalk_constantChart G U M e Ω t).some

/-- A locally constant sheaf of sets whose stalks at algebraically closed geometric points
are finite is finite locally constant: its stalks at separably closed geometric points
are then finite as well. Each such stalk is the constant value of a trivializing chart,
which is also the stalk at an algebraic closure of the residue field of a point of the
chart. -/
theorem isFiniteLocallyConstantSheafOfTypes_of_finite_sheafFiber_of_isAlgClosed
    {X : Scheme.{u}} {G : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (hG : IsLocallyConstantEtaleSheafOfSets G)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      Finite (((pointSmallEtale t).sheafFiber (A := Type (u + 1))).obj G)) :
    IsFiniteLocallyConstantSheafOfTypes G := by
  refine isFiniteLocallyConstantSheafOfTypes_of_finite_sheafFiber hG fun Ω _ _ t ↦ ?_
  have : JointlySurjective etalePrecoverage :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (t default)
  have : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) t y hy
  let U := 𝒰.etalePrecoverageToEtale i
  have := h𝒰 i
  obtain ⟨M, ⟨e⟩⟩ := (G.over U).mem_essImage_of_isConstant
  let s₀ := U.left.algClosurePoint y
  have : Finite M := Finite.of_equiv _
    (nonempty_equiv_stalk_constantChart G U M e.symm _ s₀).some
  have hfinite : Finite (((pointSmallEtale (l ≫ U.hom)).sheafFiber).obj G) :=
    Finite.of_equiv _ (nonempty_equiv_stalk_constantChart G U M e.symm Ω l).some.symm
  change Finite (((pointSmallEtale (l ≫ 𝒰.f i)).sheafFiber).obj G) at hfinite
  simpa only [hl] using hfinite

/-- Compactness bounds cardinalities of stalks of a locally constant set sheaf. -/
private theorem exists_card_bound_of_locallyConstant (X : Scheme.{u}) [CompactSpace X]
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hG : IsLocallyConstantEtaleSheafOfSets G) :
    ∃ N : ℕ, ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X),
      Nat.card (((pointSmallEtale t).sheafFiber).obj G) ≤ N := by
  classical
  have : JointlySurjective etalePrecoverage :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  obtain ⟨𝒰, h𝒰⟩ := hG
  have hvalues (i : 𝒰.I₀) : ∃ M : Type (u + 1),
      Nonempty ((constantSheaf (X.smallEtaleTopology.over
        (𝒰.etalePrecoverageToEtale i)) (Type (u + 1))).obj M ≅
          G.over (𝒰.etalePrecoverageToEtale i)) := by
    have := h𝒰 i
    exact (G.over (𝒰.etalePrecoverageToEtale i)).mem_essImage_of_isConstant
  choose M e using hvalues
  have hopen (i : 𝒰.I₀) : IsOpen (Set.range (𝒰.f i)) := by
    have : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
    exact (𝒰.f i).isOpenMap.isOpen_range
  have hcover : Set.univ ⊆ ⋃ i, Set.range (𝒰.f i) := by
    intro x _
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ Set.range (𝒰.f i)) hopen hcover
  refine ⟨I.sup (fun i ↦ Nat.card (M i)), ?_⟩
  intro Ω _ _ t
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (Set.mem_univ (t default)))
  obtain ⟨hi, y, hy⟩ := Set.mem_iUnion.mp hi
  have : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) t y hy
  have hcard := card_stalk_constantChart G (𝒰.etalePrecoverageToEtale i)
    (M i) (e i).some.symm Ω l
  change Nat.card (((pointSmallEtale (l ≫ 𝒰.f i)).sheafFiber).obj G) = _ at hcard
  rw [hl] at hcard
  rw [hcard]
  exact Finset.le_sup (f := fun i ↦ Nat.card (M i)) hi

/-- The geometric stalks of a constructible underlying set sheaf on a Noetherian scheme
are finite and have uniformly bounded cardinality. No torsion hypothesis is needed.

Source: Stacks Project, Definition 03RW and Lemma 095E; the finite-cover part of step 1
of `lem-weil-pbc-curve-constructible-annihilator`. -/
theorem exists_stalk_cardinality_bound_of_constructible
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F)) :
    ∃ N : ℕ, ∀ x : X,
      Finite (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) ∧
      Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) ≤ N := by
  classical
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let G := (sheafCompose X.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F
  obtain ⟨S, hS⟩ := hF
  have hcompact (i : Fin S.n) : CompactSpace (S.domain i) := by
    have : TopologicalSpace.NoetherianSpace (S.domain i) :=
      (S.immersion i).isEmbedding.isInducing.noetherianSpace
    infer_instance
  have hbounds (i : Fin S.n) : ∃ N : ℕ,
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ S.domain i),
        Nat.card (((pointSmallEtale t).sheafFiber).obj
          ((etaleSetPullback (S.immersion i)).obj G)) ≤ N := by
    have := hcompact i
    exact exists_card_bound_of_locallyConstant (S.domain i) _ (hS i).1
  choose N hN using hbounds
  refine ⟨Finset.univ.sup N, fun x ↦ ?_⟩
  have hx : x ∈ ⋃ i, S.stratum i := by rw [S.iUnion_stratum_eq_univ]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [← S.range_immersion i] at hi
  obtain ⟨t, ht⟩ := exists_comp_eq_of_mem_range (S.immersion i) (X.algClosurePoint x)
    (by simpa using hi)
  obtain ⟨c, hc, -⟩ := etaleSetInverseImageStalkGerm X (S.domain i)
    (S.immersion i) G _ t
  have hfin := (hS i).finite_sheafFiber _ t
  have hfinG : Finite (((pointSmallEtale (t ≫ S.immersion i)).sheafFiber).obj G) :=
    @Finite.of_equiv _ _ hfin (Equiv.ofBijective c hc)
  have hcardG : Nat.card (((pointSmallEtale (t ≫ S.immersion i)).sheafFiber).obj G) ≤
      N i := by
    rw [← Nat.card_congr (Equiv.ofBijective c hc)]
    exact hN i _ t
  rw [ht] at hfinG hcardG
  let e := ((pointSmallEtale (X.algClosurePoint x)).sheafFiberCompIso
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).app F
  refine ⟨@Finite.of_equiv _ _ hfinG e.toEquiv, ?_⟩
  exact (Nat.card_congr e.toEquiv).symm.le.trans
    (hcardG.trans (Finset.le_sup (Finset.mem_univ i)))

end AlgebraicGeometry.Scheme
