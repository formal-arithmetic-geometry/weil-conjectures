/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.Constructible
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.GeometricStalkComparisonConstant
import WeilConjectures.AlgebraicGeometry.EtaleGenericIrreducibleNeighbourhood

/-!
# Constructibility from finite geometric stalk cardinalities

Source: SGA 4, Exposé IX, Proposition 2.13(iii), and the blueprint lemma
`fin4-lem-stalk-constructibility-criterion`
(blueprint: fin4-lem-stalk-constructibility-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A constant chart computes every geometric stalk in its image. -/
private theorem abelian_stalk_iso_of_chart {X V : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : V ⟶ X) [Etale f] (A : AddCommGrpCat.{u + 1})
    (e : (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj F ≅
      (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range f) :
    Nonempty (((pointSmallEtale s).sheafFiber.obj F) ≅ A) := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨v, hv⟩ := hs
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed f s v
    (hv.trans (congrArg s (Subsingleton.elim _ _)))
  rw [← ht]
  exact ⟨((AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
    AddCommGrpCat.{u + 1} f t).app F).symm ≪≫
    (pointSmallEtale t).sheafFiber.mapIso e ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso A⟩

/-- Trivializations make stalk isomorphism classes locally constant on the base. -/
private theorem abelian_stalk_iso_near {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Cover.{u} etalePrecoverage X)
    (hV : ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1},
      Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj F ≅
        (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) (x : X) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ A : AddCommGrpCat.{u + 1},
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        s (IsLocalRing.closedPoint Ω) ∈ O →
          Nonempty (((pointSmallEtale s).sheafFiber.obj F) ≅ A) := by
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨i, v, rfl⟩ := V.exists_eq x
  have : Etale (V.f i) := V.map_prop i
  obtain ⟨A, ⟨e⟩⟩ := hV i
  exact ⟨Set.range (V.f i), (V.f i).isOpenMap.isOpen_range, ⟨v, rfl⟩, A,
    fun Ω _ _ s hs ↦ abelian_stalk_iso_of_chart F (V.f i) A e s hs⟩

/-- The cardinality loci of a sheaf with constant charts are open. -/
private theorem abelian_cardinality_locus_isOpen {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Cover.{u} etalePrecoverage X)
    (hV : ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1},
      Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj F ≅
        (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) (n : ℕ) :
    IsOpen {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F) = n} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨O, hO, hxO, A, hA⟩ := abelian_stalk_iso_near F V hV x
  refine ⟨O, fun y hy ↦ ?_, hO, hxO⟩
  obtain ⟨e⟩ := hA _ (X.algClosurePoint x) (by simpa using hxO)
  obtain ⟨e'⟩ := hA _ (X.algClosurePoint y) (by simpa using hy)
  exact (Nat.card_congr (e' ≪≫ e.symm).addCommGroupIsoToAddEquiv.toEquiv).trans hx

/-- A constant-chart restriction identifies cardinalities along an immersion. -/
private theorem abelian_cardinality_immersion {X T : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ι : T ⟶ X) [IsImmersion ι]
    (V : Cover.{u} etalePrecoverage T)
    (hV : ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1},
      Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj
        ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} ι).obj F) ≅
          (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) (t : T) :
    Nat.card (((pointSmallEtale (X.algClosurePoint (ι t))).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F) =
    Nat.card (((pointSmallEtale (T.algClosurePoint t)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} ι).obj F)) := by
  obtain ⟨s, hs⟩ := IsImmersion.exists_comp_eq_of_field ι (X.algClosurePoint (ι t))
    ⟨t, by simp⟩
  have hst : s (IsLocalRing.closedPoint _) = t := ι.isEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hs, algClosurePoint_base])
  let G := (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} ι).obj F
  obtain ⟨O, -, htO, A, hA⟩ := abelian_stalk_iso_near G V hV t
  obtain ⟨e⟩ := hA _ s (by simpa [hst] using htO)
  obtain ⟨e'⟩ := hA _ (T.algClosurePoint t) (by simpa using htO)
  rw [← hs]
  let eTotal := ((AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
    AddCommGrpCat.{u + 1} ι s).app F).symm ≪≫ e ≪≫ e'.symm
  exact Nat.card_congr eTotal.addCommGroupIsoToAddEquiv.toEquiv

/-- Finite stratifications with constant charts have constructible cardinality loci. -/
private theorem abelian_constructible_cardinality {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf F) (n : ℕ) :
    Topology.IsConstructible {x : X | Nat.card
      (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) = n} := by
  classical
  obtain ⟨S, hS, hloc⟩ := hF
  let C := {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
    (A := AddCommGrpCat.{u + 1})).obj F) = n}
  have heq : C = ⋃ i, (S.stratum i ∩ C) := by
    rw [← Set.iUnion_inter, S.iUnion_stratum_eq_univ, Set.univ_inter]
  change Topology.IsConstructible C
  rw [heq]
  refine Topology.IsConstructible.iUnion fun i ↦ ?_
  obtain ⟨V, hV⟩ := hloc i
  have hV' : ∀ j : V.I₀, ∃ A : AddCommGrpCat.{u + 1},
      Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f j)).obj
        ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).obj F) ≅
          (constantSheaf (V.X j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) := by
    intro j
    obtain ⟨A, -, e⟩ := hV j
    exact ⟨A, e⟩
  obtain ⟨O, hO, hOe⟩ := (S.immersion i).isEmbedding.isInducing.isOpen_iff.mp
    (abelian_cardinality_locus_isOpen _ V hV' n)
  have hinter : S.stratum i ∩ C = S.stratum i ∩ O := by
    rw [← S.range_immersion]
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion i) ⁻¹' O
      rw [hOe]
      exact (abelian_cardinality_immersion F (S.immersion i) V hV' t).symm.trans hx
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion i) ⁻¹' O at hx
      rw [hOe] at hx
      exact (abelian_cardinality_immersion F (S.immersion i) V hV' t).trans hx
  rw [hinter]
  exact (hS i).inter hO.isConstructible_of_noetherianSpace

/-- Stalk cardinality is independent of the chosen geometric point. -/
private theorem abelian_cardinality_eq_of_same_point {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω') ⟶ X)
    (hst : s (IsLocalRing.closedPoint Ω) = t (IsLocalRing.closedPoint Ω')) :
    Nat.card (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) =
      Nat.card (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) := by
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let U := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  let M := (sheafCompose X.smallEtaleTopology E).obj F
  let eAb : (sheafCompose X.smallEtaleTopology U).obj M ≅ F :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerLeft F.obj
        (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.counitIso ≪≫
          Functor.rightUnitor F.obj)
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u} U :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨β, -⟩ := exists_geometricStalkComparison_constant
    (Λ := ULift.{u + 1} ℤ) s t hst
  let e := ((pointSmallEtale s).sheafFiber.mapIso eAb).symm ≪≫
    ((pointSmallEtale s).sheafFiberCompIso U).app M ≪≫ U.mapIso (β.app M) ≪≫
      (((pointSmallEtale t).sheafFiberCompIso U).app M).symm ≪≫
        (pointSmallEtale t).sheafFiber.mapIso eAb
  exact Nat.card_congr e.addCommGroupIsoToAddEquiv.toEquiv

/-- Pullback reads a cardinality locus as the preimage of the original locus. -/
private theorem abelian_cardinality_pullback {X Y : Scheme.{u}}
    (f : Y ⟶ X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (y : Y) :
    Nat.card (((pointSmallEtale (Y.algClosurePoint y)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)) =
      Nat.card (((pointSmallEtale (X.algClosurePoint (f y))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) := by
  let e := (AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
    AddCommGrpCat.{u + 1} f (Y.algClosurePoint y)).app F
  exact (Nat.card_congr e.addCommGroupIsoToAddEquiv.toEquiv).trans
    (abelian_cardinality_eq_of_same_point F (Y.algClosurePoint y ≫ f)
      (X.algClosurePoint (f y)) (by simp))

/-- Constructibility of all cardinality loci is preserved by every pullback. -/
private theorem abelian_cardinality_loci_pullback {X Y : Scheme.{u}}
    (f : Y ⟶ X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
      {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) = n}) :
    ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
      {y : Y | Nat.card (((pointSmallEtale (Y.algClosurePoint y)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
          ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)) = n} := by
  intro n hn
  have h := f.isConstructible_preimage (hF n hn)
  convert h using 1
  ext y
  exact iff_of_eq (congrArg (· = n) (abelian_cardinality_pullback f F y))

/-- Transport finite constant charts across an isomorphism. -/
private theorem abelian_constructible_of_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (hF : IsConstructibleAbelianSheaf F) : IsConstructibleAbelianSheaf G := by
  obtain ⟨S, hS, hF⟩ := hF
  refine ⟨S, hS, fun k ↦ ?_⟩
  obtain ⟨V, hV⟩ := hF k
  refine ⟨V, fun i ↦ ?_⟩
  obtain ⟨A, hA, ⟨eA⟩⟩ := hV i
  exact ⟨A, hA, ⟨(AlgebraicGeometry.Etale.upperStar _ (V.f i)).mapIso
    ((AlgebraicGeometry.Etale.upperStar _ (S.immersion k)).mapIso e.symm) ≪≫ eA⟩⟩

/-- A single finite constant-chart cover gives a constructible sheaf. -/
private theorem abelian_constructible_of_charts {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Cover.{u} etalePrecoverage X)
    (hV : ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1}, Finite A ∧
      Nonempty ((AlgebraicGeometry.Etale.upperStar _ (V.f i)).obj F ≅
        (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) :
    IsConstructibleAbelianSheaf F := by
  refine ⟨Stratification.trivial X, fun _ ↦ Topology.IsConstructible.univ, fun _ ↦ ?_⟩
  refine ⟨V, fun i ↦ ?_⟩
  obtain ⟨A, hA, ⟨eA⟩⟩ := hV i
  exact ⟨A, hA, ⟨(AlgebraicGeometry.Etale.upperStar _ (V.f i)).mapIso
    ((AlgebraicGeometry.Etale.upperStarId AddCommGrpCat.{u + 1} X).app F) ≪≫ eA⟩⟩

/-- The empty scheme has the empty trivializing cover. -/
private theorem abelian_constructible_empty {X : Scheme.{u}} [IsEmpty X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsConstructibleAbelianSheaf F := by
  apply abelian_constructible_of_charts F
    (Cover.mkOfCovers PEmpty (fun _ ↦ X) (fun _ ↦ 𝟙 X)
      (fun x ↦ isEmptyElim x) (fun _ ↦ inferInstance))
  exact fun i ↦ i.elim

/-- Concatenate the stratifications on an open and its closed complement. -/
private theorem abelian_constructible_openClosed {X U Z : Scheme.{u}}
    [IsNoetherian X] (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (hij : Set.range i = (Set.range j)ᶜ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hU : IsConstructibleAbelianSheaf
      ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} j).obj F))
    (hZ : IsConstructibleAbelianSheaf
      ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} i).obj F)) :
    IsConstructibleAbelianSheaf F := by
  obtain ⟨SU, _, hSU⟩ := hU
  obtain ⟨SZ, _, hSZ⟩ := hZ
  refine ⟨Stratification.openClosed j i hij SU SZ,
    (Stratification.openClosed j i hij SU SZ).isConstructible_stratum, fun k ↦ ?_⟩
  change ∃ V : Cover.{u} etalePrecoverage
      (Sum.elim SU.domain SZ.domain (finSumFinEquiv.symm k)),
    ∀ a : V.I₀, ∃ A : AddCommGrpCat.{u + 1}, Finite A ∧ Nonempty
      ((AlgebraicGeometry.Etale.upperStar _ (V.f a)).obj
        ((AlgebraicGeometry.Etale.upperStar _
          (Sum.rec (motive := fun t ↦ Sum.elim SU.domain SZ.domain t ⟶ X)
            (fun l ↦ SU.immersion l ≫ j) (fun l ↦ SZ.immersion l ≫ i)
              (finSumFinEquiv.symm k))).obj F) ≅
        (constantSheaf (V.X a).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
  generalize finSumFinEquiv.symm k = t
  rcases t with l | l
  · obtain ⟨V, hV⟩ := hSU l
    refine ⟨V, fun a ↦ ?_⟩
    obtain ⟨A, hA, ⟨e⟩⟩ := hV a
    exact ⟨A, hA, ⟨(AlgebraicGeometry.Etale.upperStar _ (V.f a)).mapIso
      ((AlgebraicGeometry.Etale.upperStarComp _ (SU.immersion l) j).app F) ≪≫ e⟩⟩
  · obtain ⟨V, hV⟩ := hSZ l
    refine ⟨V, fun a ↦ ?_⟩
    obtain ⟨A, hA, ⟨e⟩⟩ := hV a
    exact ⟨A, hA, ⟨(AlgebraicGeometry.Etale.upperStar _ (V.f a)).mapIso
      ((AlgebraicGeometry.Etale.upperStarComp _ (SZ.immersion l) i).app F) ≪≫ e⟩⟩

/-- Noetherian induction reduces constructibility to one nonempty open on each closed part. -/
private theorem abelian_constructible_of_closed_generic {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian Z]
      [Nonempty Z], ∃ U : Z.Opens, (U : Set Z).Nonempty ∧
        IsConstructibleAbelianSheaf ((AlgebraicGeometry.Etale.upperStar _ U.ι).obj
          ((AlgebraicGeometry.Etale.upperStar _ i).obj F))) :
    IsConstructibleAbelianSheaf F := by
  classical
  have key : ∀ (C : TopologicalSpace.Closeds X) (Z : Scheme.{u})
      (i : Z ⟶ X) [IsClosedImmersion i], Set.range i ⊆ C →
      IsConstructibleAbelianSheaf ((AlgebraicGeometry.Etale.upperStar _ i).obj F) := by
    intro C
    induction C using WellFoundedLT.induction with
    | ind C ih =>
      intro Z i _ hiC
      have : IsNoetherian Z := by
        have := LocallyOfFiniteType.isLocallyNoetherian i
        have := QuasiCompact.compactSpace_of_compactSpace i
        exact {}
      cases isEmpty_or_nonempty Z
      · exact abelian_constructible_empty _
      obtain ⟨U, ⟨z, hz⟩, hU⟩ := h Z i
      let D : TopologicalSpace.Closeds Z := ⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩
      let i' := (IdealSheafData.vanishingIdeal D).subschemeι
      have hrange : Set.range i' = (U : Set Z)ᶜ := by
        simp [i', D, IdealSheafData.range_subschemeι,
          IdealSheafData.coe_support_vanishingIdeal]
      let C' : TopologicalSpace.Closeds X :=
        ⟨i '' (U : Set Z)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hlt : C' < C := by
        refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hiC ⟨t, ht⟩) fun heq ↦ ?_
        have : i z ∈ (C' : Set X) := heq ▸ hiC ⟨z, rfl⟩
        obtain ⟨t, ht, hti⟩ := this
        exact ht (i.isClosedEmbedding.injective hti ▸ hz)
      have hC' := ih C' hlt _ (i' ≫ i) (by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
        exact subset_rfl)
      have hclosed : IsConstructibleAbelianSheaf
          ((AlgebraicGeometry.Etale.upperStar _ i').obj
            ((AlgebraicGeometry.Etale.upperStar _ i).obj F)) :=
        abelian_constructible_of_iso
          ((AlgebraicGeometry.Etale.upperStarComp AddCommGrpCat.{u + 1} i' i).app F) hC'
      exact abelian_constructible_openClosed U.ι i'
        (by rw [Scheme.Opens.range_ι]; exact hrange) _ hU hclosed
  exact abelian_constructible_of_iso
    ((AlgebraicGeometry.Etale.upperStarId AddCommGrpCat.{u + 1} X).app F)
    (key ⊤ X (𝟙 X) (by simp))

/-- Finitely many equalities of germs hold on one common pointed neighbourhood. -/
private theorem abelian_refine_relations {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    {I : Type*} (q : Finset I) :
    ∀ (V : X.Etale) (v : (pointSmallEtale s).fiber.obj V)
      (a b : I → F.obj.obj (Opposite.op V)),
      (∀ i ∈ q, (pointSmallEtale s).toPresheafFiber V v F.obj (a i) =
        (pointSmallEtale s).toPresheafFiber V v F.obj (b i)) →
      ∃ (W : X.Etale) (f : W ⟶ V) (w : (pointSmallEtale s).fiber.obj W),
        (pointSmallEtale s).fiber.map f w = v ∧
          ∀ i ∈ q, F.obj.map f.op (a i) = F.obj.map f.op (b i) := by
  classical
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  induction q using Finset.induction with
  | empty => exact fun V v _ _ _ ↦ ⟨V, 𝟙 V, v, by simp, by simp⟩
  | @insert i q hi ih =>
    intro V v a b h
    obtain ⟨W, f, w, hw, heq⟩ :=
      ((pointSmallEtale s).toPresheafFiber_eq_iff' V v (a i) (b i)).mp
        (h i (Finset.mem_insert_self _ _))
    obtain ⟨W', g, w', hw', hg⟩ := ih W w
      (fun j ↦ F.obj.map f.op (a j)) (fun j ↦ F.obj.map f.op (b j)) (by
        intro j hj
        rw [(pointSmallEtale s).toPresheafFiber_w_apply, hw,
          (pointSmallEtale s).toPresheafFiber_w_apply, hw]
        exact h j (Finset.mem_insert_of_mem hj))
    refine ⟨W', g ≫ f, w', by
      rw [Functor.map_comp_apply, hw', hw], ?_⟩
    intro j hj
    rw [op_comp, Functor.map_comp]
    simp only [ConcreteCategory.comp_apply]
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact congrArg (fun a ↦ F.obj.map g.op a) heq
    · exact hg j hj

/-- Lift the finite generic group and its addition table to sections on one neighbourhood. -/
private theorem abelian_finite_stalk_lift {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    [Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)] :
    ∃ (V : X.Etale) (v : (pointSmallEtale s).fiber.obj V)
      (σ : (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) →+
        F.obj.obj (Opposite.op V)),
      ∀ a, (pointSmallEtale s).toPresheafFiber V v F.obj (σ a) = a := by
  classical
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale s
  let M := (Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).obj F
  have hrep (a : M) : ∃ (E : Φ.fiber.Elements)
      (σ : F.obj.obj (Opposite.op E.1)), Φ.toPresheafFiber E.1 E.2 F.obj σ = a := by
    obtain ⟨V, v, σ, hσ⟩ := Φ.toPresheafFiber_jointly_surjective a
    exact ⟨⟨V, v⟩, σ, hσ⟩
  choose E σ hσ using hrep
  let : Fintype M := Fintype.ofFinite M
  obtain ⟨E₀, hE₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image E)
  let f (a : M) : E₀ ⟶ E a :=
    (hE₀ (Finset.mem_image_of_mem E (Finset.mem_univ a))).some
  let τ (a : M) := F.obj.map (f a).1.op (σ a)
  have hτ (a : M) : Φ.toPresheafFiber E₀.1 E₀.2 F.obj (τ a) = a := by
    rw [Φ.toPresheafFiber_w_apply, (f a).2]
    exact hσ a
  obtain ⟨V, g, v, hv, hg⟩ := abelian_refine_relations F s
    (Finset.univ : Finset (M × M)) E₀.1 E₀.2
    (fun ab ↦ τ (ab.1 + ab.2)) (fun ab ↦ τ ab.1 + τ ab.2) (by
      intro ab _
      rw [map_add, hτ, hτ, hτ])
  let ρ (a : M) := F.obj.map g.op (τ a)
  have hadd (a b : M) : ρ (a + b) = ρ a + ρ b := by
    simpa only [map_add] using hg (a, b) (Finset.mem_univ _)
  let ψ : M →+ F.obj.obj (Opposite.op V) :=
    { toFun := ρ
      map_zero' := by
        have hh := hadd 0 0
        simpa using (add_left_cancel (show ρ 0 + ρ 0 = ρ 0 + 0 by simpa using hh.symm))
      map_add' := hadd }
  refine ⟨V, v, ψ, fun a ↦ ?_⟩
  change Φ.toPresheafFiber V v F.obj (F.obj.map g.op (τ a)) = a
  rw [Φ.toPresheafFiber_w_apply, hv, hτ]

/-- Independence of finite generic sections persists at every geometric germ. -/
private theorem abelian_injective_germs_of_generic {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (V : X.Etale) [IrreducibleSpace V.left] (v : (pointSmallEtale s).fiber.obj V)
    (hv : IsGenericPoint (v.left (IsLocalRing.closedPoint Ω)) Set.univ)
    (M : AddCommGrpCat.{u + 1}) (σ : M →+ F.obj.obj (Opposite.op V))
    (hσ : Function.Injective (fun a ↦ (pointSmallEtale s).toPresheafFiber V v F.obj (σ a)))
    {W : X.Etale} (g : W ⟶ V)
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ X)
    (w : (pointSmallEtale t).fiber.obj W) :
    Function.Injective (fun a ↦ (pointSmallEtale t).toPresheafFiber W w F.obj
      (F.obj.map g.op (σ a))) := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro a b hab
  obtain ⟨W', h, w', _, heq⟩ := ((pointSmallEtale t).toPresheafFiber_eq_iff'
    W w (F.obj.map g.op (σ a)) (F.obj.map g.op (σ b))).mp hab
  let H := h ≫ g
  have hH : Etale H.left := inferInstance
  have hη : v.left (IsLocalRing.closedPoint Ω) ∈ Set.range H.left :=
    (hv.mem_open_set_iff H.left.isOpenMap.isOpen_range).mpr
      ⟨H.left (w'.left (IsLocalRing.closedPoint Ω')), Set.mem_univ _, Set.mem_range_self _⟩
  obtain ⟨y, hy⟩ := hη
  have : Subsingleton (Spec (.of Ω)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨l, hl, _⟩ := exists_fac_of_etale_of_isSepClosed H.left v.left y
    (hy.trans (congrArg (fun p : Spec (.of Ω) ↦ v.left p)
      (Subsingleton.elim _ _)))
  let z : (pointSmallEtale s).fiber.obj W' := CategoryTheory.Over.homMk l (by
    change l ≫ W'.hom = s
    have hH' : H.left ≫ V.hom = W'.hom :=
      CategoryTheory.Over.w ((Scheme.Etale.forget X).map H)
    rw [← hH', ← Category.assoc, hl]
    exact CategoryTheory.Over.w v)
  have hz : (pointSmallEtale s).fiber.map H z = v :=
    CategoryTheory.Over.OverMorphism.ext hl
  apply hσ
  have hrel : F.obj.map H.op (σ a) = F.obj.map H.op (σ b) := by
    simpa only [H, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using heq
  have hgerm (c : M) : (pointSmallEtale s).toPresheafFiber W' z F.obj
      (F.obj.map H.op (σ c)) = (pointSmallEtale s).toPresheafFiber V v F.obj (σ c) := by
    rw [(pointSmallEtale s).toPresheafFiber_w_apply, hz]
  change (pointSmallEtale s).toPresheafFiber V v F.obj (σ a) =
    (pointSmallEtale s).toPresheafFiber V v F.obj (σ b)
  rw [← hgerm a, ← hgerm b, hrel]

set_option backward.isDefEq.respectTransparency false in
/-- Generic independent sections trivialize a finite constant-cardinality sheaf. -/
private theorem abelian_constant_chart_of_generic_sections {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (V : X.Etale) [IrreducibleSpace V.left] (v : (pointSmallEtale s).fiber.obj V)
    (hv : IsGenericPoint (v.left (IsLocalRing.closedPoint Ω)) Set.univ)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (σ : M →+ F.obj.obj (Opposite.op V))
    (hσ : Function.Injective (fun a ↦ (pointSmallEtale s).toPresheafFiber V v F.obj (σ a)))
    (hcard : ∀ x : V.left, Nat.card
      (((pointSmallEtale (X.algClosurePoint (V.hom x))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) = Nat.card M) :
    Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} V.hom).obj F ≅
      (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := by
  classical
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let L := MorphismProperty.Over.map ⊤ V.prop
  let K := (AlgebraicGeometry.Etale.localizationRestriction
    AddCommGrpCat.{u + 1} V.hom V.prop).obj F
  let g (T : V.left.Etale) : L.obj T ⟶ V := MorphismProperty.Over.homMk T.hom rfl
  let c : (Functor.const V.left.Etaleᵒᵖ).obj M ⟶ K.obj :=
    { app T := AddCommGrpCat.ofHom ((F.obj.map (g T.unop).op).hom.comp σ)
      naturality T T' f := by
        change _ ≫ F.obj.map (g T'.unop).op =
          _ ≫ F.obj.map (g T.unop).op ≫ F.obj.map (L.map f.unop).op
        rw [← Functor.map_comp, ← op_comp]
        have hcomp : L.map f.unop ≫ g T.unop = g T'.unop := by
          apply MorphismProperty.Over.Hom.ext
          exact CategoryTheory.Over.w ((Scheme.Etale.forget V.left).map f.unop)
        rw [hcomp] }
  have hinj (T : V.left.Etale) [Nonempty T.left] :
      Function.Injective (c.app (Opposite.op T)) := by
    obtain ⟨x⟩ := ‹Nonempty T.left›
    let t := T.left.algClosurePoint x ≫ (L.obj T).hom
    let w : (pointSmallEtale t).fiber.obj (L.obj T) :=
      CategoryTheory.Over.homMk (T.left.algClosurePoint x) rfl
    intro a b hab
    apply abelian_injective_germs_of_generic F s V v hv M σ hσ (g T) t w
    exact congrArg (fun a ↦ (pointSmallEtale t).toPresheafFiber (L.obj T) w F.obj a) hab
  have hW : V.left.smallEtaleTopology.W c := by
    rw [GrothendieckTopology.W_iff_isLocallyBijective]
    refine ⟨⟨fun {T} a b hab ↦ ?_⟩, ⟨fun {T} τ ↦ ?_⟩⟩
    · rw [mem_smallEtaleTopology_iff]
      intro x
      have : Nonempty T.unop.left := ⟨x⟩
      obtain rfl := hinj T.unop hab
      exact ⟨T.unop, 𝟙 _, rfl, ⟨x, rfl⟩⟩
    · rw [mem_smallEtaleTopology_iff]
      intro x
      let W := L.obj T
      let t := T.left.algClosurePoint x ≫ W.hom
      let w : (pointSmallEtale t).fiber.obj W :=
        CategoryTheory.Over.homMk (T.left.algClosurePoint x) rfl
      let δ (a : M) : ((pointSmallEtale t).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj F := (pointSmallEtale t).toPresheafFiber W w F.obj
        (F.obj.map (g T).op (σ a))
      have hδ : Function.Injective δ :=
        abelian_injective_germs_of_generic F s V v hv M σ hσ (g T) t w
      have hsize : Nat.card (((pointSmallEtale t).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj F) = Nat.card M := by
        refine (abelian_cardinality_eq_of_same_point F t
          (X.algClosurePoint (V.hom (T.hom x))) ?_).trans (hcard _)
        simp [t, W, L]
      have : Finite (((pointSmallEtale t).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj F) :=
        Nat.finite_of_card_ne_zero (hsize ▸ (Nat.card_pos (α := M)).ne')
      have hsurj : Function.Surjective δ :=
        ((Nat.bijective_iff_injective_and_card δ).mpr ⟨hδ, hsize.symm⟩).surjective
      obtain ⟨a, ha⟩ := hsurj ((pointSmallEtale t).toPresheafFiber W w F.obj τ)
      obtain ⟨E, f, e, hef, heq⟩ := ((pointSmallEtale t).toPresheafFiber_eq_iff'
        W w (F.obj.map (g T).op (σ a)) τ).mp ha
      have : Etale f.left := inferInstance
      let R : V.left.Etale := Scheme.Etale.mk (f.left ≫ T.hom)
      let fR : R ⟶ T := MorphismProperty.Over.homMk f.left rfl
      let k : L.obj R ⟶ E := MorphismProperty.Over.homMk (𝟙 E.left) (by
        change 𝟙 E.left ≫ E.hom = (f.left ≫ T.hom) ≫ V.hom
        rw [Category.id_comp, Category.assoc]
        exact (CategoryTheory.Over.w ((Scheme.Etale.forget X).map f)).symm)
      have hk : k ≫ f = L.map fR := by
        apply MorphismProperty.Over.Hom.ext
        exact Category.id_comp _
      have hg : L.map fR ≫ g T = g R := by
        apply MorphismProperty.Over.Hom.ext
        rfl
      refine ⟨R, fR, ⟨a, ?_⟩, ?_⟩
      · change F.obj.map (g R).op (σ a) = F.obj.map (L.map fR).op τ
        rw [← hg, ← hk, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        exact congrArg (fun b ↦ F.obj.map k.op b) heq
      · exact ⟨e.left (IsLocalRing.closedPoint _), by
          change f.left (e.left (IsLocalRing.closedPoint _)) = x
          have he : e.left ≫ f.left = T.left.algClosurePoint x :=
            congrArg CategoryTheory.Over.Hom.left hef
          exact (congrArg (fun q ↦ q (IsLocalRing.closedPoint _)) he).trans
            (algClosurePoint_base _ _ _)⟩
  have : IsIso ((presheafToSheaf V.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map c) :=
    (V.left.smallEtaleTopology.W_iff c).mp hW
  exact ⟨(AlgebraicGeometry.Etale.upperStarIsoLocalizationRestriction
    AddCommGrpCat.{u + 1} V.hom V.prop).app F ≪≫ sheafificationIso K ≪≫
      (asIso ((presheafToSheaf V.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map c)).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Constructible cardinality loci give a nonempty open with a single finite chart. -/
private theorem abelian_exists_nonempty_open {X : Scheme.{u}} [IsNoetherian X] [Nonempty X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      Finite (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F))
    (hloci : ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
      {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) = n}) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsConstructibleAbelianSheaf
      ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) := by
  classical
  let η : genericPoints X := genericPoints.ofComponent
    ⟨irreducibleComponent (Classical.arbitrary X),
      irreducibleComponent_mem_irreducibleComponents _⟩
  let s : Spec (.of (AlgebraicClosure (X.residueField η.val))) ⟶ X :=
    X.algClosurePoint η.val
  let M := ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F
  have : Finite M := hfinite _ s
  obtain ⟨O, hO, hηO, hsub⟩ := (hloci (Nat.card M) (Nat.card_pos (α := M))).exists_isOpen_mem_subset
    η.property (show η.val ∈ {x : X | Nat.card (((pointSmallEtale
      (X.algClosurePoint x)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) = Nat.card M}
      from rfl)
  let O' : X.Opens := ⟨O, hO⟩
  obtain ⟨V₀, v₀, σ, hσ⟩ := abelian_finite_stalk_lift F s
  have : Etale V₀.hom := V₀.prop
  let z : V₀.left := v₀.left (IsLocalRing.closedPoint _)
  have hz : V₀.hom z = η.val := by
    change (v₀.left ≫ V₀.hom) (IsLocalRing.closedPoint _) = η.val
    have hcomp : v₀.left ≫ V₀.hom = s := CategoryTheory.Over.w v₀
    exact (congrArg (fun q ↦ q (IsLocalRing.closedPoint _)) hcomp).trans
      (algClosurePoint_base _ _ _)
  obtain ⟨W, hzW, _, hgen⟩ :=
    exists_irreducible_open_of_etale_generic (X := X) V₀.hom η.val η.property z hz
  let Q : V₀.left.Opens := W ⊓ V₀.hom ⁻¹ᵁ O'
  have hzQ : z ∈ Q := ⟨hzW, by change V₀.hom z ∈ O; rwa [hz]⟩
  let V : X.Etale := Scheme.Etale.ofOpens V₀ Q
  obtain ⟨v, hv⟩ := exists_pointSmallEtale_fiber_ofOpens s v₀ Q (by
    rintro _ ⟨p, rfl⟩
    have hp : p = (IsLocalRing.closedPoint _ :
        Spec (.of (AlgebraicClosure (X.residueField η.val)))) :=
      @Subsingleton.elim (PrimeSpectrum (AlgebraicClosure (X.residueField η.val))) _ _ _
    rw [hp]
    exact hzQ)
  let ξ : V.left := ⟨z, hzQ⟩
  have hξ : IsGenericPoint ξ Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    exact (subtype_specializes_iff _ _).mpr
      ((hgen.specializes (Set.mem_univ (⟨y.val, y.property.1⟩ : W.toScheme))).map W.ι.continuous)
  have : IrreducibleSpace V.left := (irreducibleSpace_def V.left).mpr hξ.isIrreducible
  have hvξ : v.left (IsLocalRing.closedPoint _) = ξ := by
    apply Subtype.ext
    exact congrArg (fun q ↦ q (IsLocalRing.closedPoint _))
      (congrArg CategoryTheory.Over.Hom.left hv)
  let σ' : M →+ F.obj.obj (Opposite.op V) :=
    (F.obj.map (Scheme.Etale.ofOpensι V₀ Q).op).hom.comp σ
  have hσ' (a : M) : (pointSmallEtale s).toPresheafFiber V v F.obj (σ' a) = a := by
    change (pointSmallEtale s).toPresheafFiber V v F.obj
      (F.obj.map (Scheme.Etale.ofOpensι V₀ Q).op (σ a)) = a
    rw [(pointSmallEtale s).toPresheafFiber_w_apply, hv, hσ]
  obtain ⟨e⟩ := abelian_constant_chart_of_generic_sections F s V v (hvξ.symm ▸ hξ) M σ'
    (by intro a b hab; simpa only [hσ'] using hab) (fun y ↦ hsub y.property.2)
  have : Etale V.hom := V.prop
  let U : X.Opens := ⟨Set.range V.hom, V.hom.isOpenMap.isOpen_range⟩
  let f : V.left ⟶ U.toScheme := IsOpenImmersion.lift U.ι V.hom (by
    rw [Opens.range_ι]; exact subset_rfl)
  have hfac : f ≫ U.ι = V.hom := IsOpenImmersion.lift_fac _ _ _
  have : Etale f := by
    have : Etale (f ≫ U.ι) := hfac.symm ▸ V.prop
    exact Etale.of_comp f U.ι
  have : Surjective f := by
    constructor
    intro y
    obtain ⟨t, ht⟩ := y.property
    refine ⟨t, U.ι.isOpenEmbedding.injective ?_⟩
    change (f ≫ U.ι) t = y.val
    rw [hfac]
    exact ht
  let C : Cover.{u} etalePrecoverage U.toScheme :=
    .singleton f ((singleton_mem_precoverage_iff _ f).mpr ⟨f.surjective, inferInstance⟩)
  refine ⟨U, ⟨V.hom ξ, ⟨ξ, rfl⟩⟩, abelian_constructible_of_charts _ C fun _ ↦ ?_⟩
  refine ⟨M, inferInstance, ⟨?_⟩⟩
  exact ((AlgebraicGeometry.Etale.upperStarComp AddCommGrpCat.{u + 1} f U.ι).app F).symm ≪≫
    eqToIso (congrArg (fun k ↦ (AlgebraicGeometry.Etale.upperStar
      AddCommGrpCat.{u + 1} k).obj F) hfac) ≪≫ e

/-- Converse constructibility criterion from cardinality loci.

This is the Noetherian-induction converse of SGA 4, Exposé IX, Proposition 2.13(iii).
The proof uses the finite-stalk constant-cardinality open construction on an irreducible
Noetherian open, followed by Noetherian induction on closed complements.
(blueprint: fin4-lem-stalk-constructibility-criterion-converse) -/
theorem isConstructibleAbelianSheaf_of_constructible_stalk_cardinality_loci
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X),
      Finite (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F))
    (hloci : ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
      {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) = n}) :
    IsConstructibleAbelianSheaf F := by
  apply abelian_constructible_of_closed_generic F
  intro Z i _ _ _
  apply abelian_exists_nonempty_open
    ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} i).obj F)
  · intro Ω _ _ t
    let e := (AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
      AddCommGrpCat.{u + 1} i t).app F
    exact @Finite.of_equiv _ _ (hfinite Ω (t ≫ i))
      e.symm.addCommGroupIsoToAddEquiv.toEquiv
  · exact abelian_cardinality_loci_pullback i F hloci

/-- An abelian étale sheaf with finite geometric stalks on a Noetherian scheme is
constructible exactly when every positive stalk-cardinality locus is constructible.
The geometric point over `x` used for the locus is the spectrum of an algebraic closure
of its residue field. Constructibility means a single finite locally closed partition
with finite locally constant abelian restrictions, as in `IsConstructibleAbelianSheaf`.

Source: SGA 4, Exposé IX, Proposition 2.13(iii), and the blueprint lemma
`fin4-lem-stalk-constructibility-criterion`.

Proof:
1. Finite constant charts make the cardinality locus open on each stratum, so its
finite union over the constructible strata is constructible.
2. For the converse, use Noetherian induction on closed subsets, with the induction
assertion quantified over closed immersions whose image is contained in the subset.
Pullback preserves finite stalks and constructible cardinality loci by stalk comparison.
3. At a component generic point, its finite stalk cardinality is constant on an open
neighbourhood, by constructibility of that cardinality locus.
4. Represent every element of the finite generic group by a section, and make its
finitely many addition relations hold on a common pointed etale refinement.
5. Retain the marked point in an irreducible etale open neighbourhood and intersect
with the constant-cardinality open. The lifted sections still give the identity on
the marked stalk.
6. If two labels have equal germs anywhere over this neighbourhood, their sections
agree on a nonempty etale refinement. Its open image contains the generic point;
lifting the original generic point to it forces the labels to agree. Thus labels
inject into every geometric stalk. Equal finite cardinalities imply surjectivity.
The resulting constant-presheaf map to the localization restriction is locally
bijective, so its sheafification is an isomorphism. The localization comparison
identifies this with a finite constant chart of the inverse-image sheaf.
7. The etale image is a nonempty open with finite constant charts. Construct its
closed complement using the vanishing ideal and apply the induction hypothesis.
Concatenate the open and closed stratifications and transport their charts by
inverse-image composition. The empty case uses the empty etale cover.

(blueprint: fin4-lem-stalk-constructibility-criterion). -/
theorem isConstructibleAbelianSheaf_iff_constructible_stalk_cardinality_loci
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X),
      Finite (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)) :
    IsConstructibleAbelianSheaf F ↔
      ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
        {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj F) = n} := by
  constructor
  · intro hF n _
    exact abelian_constructible_cardinality F hF n
  · intro hloci
    exact isConstructibleAbelianSheaf_of_constructible_stalk_cardinality_loci
      X F hfinite hloci

end AlgebraicGeometry.Scheme
