/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Étale objects and cohomology over a separably closed field

Source: blueprint `sec-smooth-purity`, `sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-0ezp`; Stacks Project, Tags 02GL, 03QO and the field case of 0EZP
(blueprint: lem-kun-0ezp).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Lift separately on the rational-point components and use the sheaf axiom to glue.
The empty-cover sheaf axiom handles empty overlaps. This is the componentwise argument
of Stacks 02GL and 03QO, using the proved terminal lifting result in PointCohomology. -/
private theorem surjective_sections_of_epi (L : Type u) [Field L] [IsSepClosed L]
    {F G : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [Epi φ] (V : (Spec (.of L)).Etale) :
    Function.Surjective (φ.hom.app (Opposite.op V)) := by
  classical
  have : AlgebraicGeometry.Etale V.hom := V.prop
  have h (v : V.left) : ∃ l : Spec (.of L) ⟶ V.left,
      l ≫ V.hom = 𝟙 _ ∧ l default = v :=
    Scheme.exists_fac_of_etale_of_isSepClosed V.hom (𝟙 _) v
      (Subsingleton.elim (α := Spec (.of L)) _ _)
  choose l hl hv using h
  let T := Scheme.etalePoint L
  let g (v : V.left) : T ⟶ V := MorphismProperty.Over.homMk (l v) (hl v)
  have ho (v : V.left) : IsOpenImmersion (l v) := by
    have : IsOpenImmersion (l v ≫ V.hom) := (hl v) ▸ inferInstance
    exact FormallyUnramified.isOpenImmersion_of_comp V.hom (l v)
  have hg (v : V.left) : Set.range (g v).left = {v} := by
    change Set.range (l v) = {v}
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      change l v a = v
      rw [Subsingleton.elim a default, hv]
    · intro hx
      exact ⟨default, (hv v).trans (Set.mem_singleton_iff.mp hx).symm⟩
  have hcov : ⋃ v, Set.range (g v).left = Set.univ :=
    Set.eq_univ_of_forall fun v ↦ Set.mem_iUnion.mpr ⟨v, by rw [hg]; rfl⟩
  intro s
  choose e he using fun v ↦ Scheme.surjective_app_of_epi_of_isSepClosed L φ
    (G.obj.map (g v).op s)
  obtain ⟨y, hy, -⟩ := (Presieve.isSheafFor_arrows_iff _ g).mp
    (Scheme.isSheafFor_ofArrows F g hcov) e fun a b Z ga gb hab ↦ by
      by_cases hZ : IsEmpty Z.left
      · exact (Scheme.isSheafFor_ofArrows F
          (U := (PEmpty.elim : PEmpty.{1} → (Spec (.of L)).Etale)))
          (fun a ↦ a.elim) (Set.eq_univ_of_forall fun z ↦ isEmptyElim z)
          |>.isSeparatedFor.ext (fun _ _ ⟨a⟩ ↦ a.elim)
      obtain ⟨z⟩ := not_isEmpty_iff.mp hZ
      have hz : (g a).left (ga.left z) = (g b).left (gb.left z) :=
        congrArg (fun ψ ↦ ψ.left z) hab
      have ha : (g a).left (ga.left z) = a := (hg a).subset ⟨_, rfl⟩
      have hb : (g b).left (gb.left z) = b := (hg b).subset ⟨_, rfl⟩
      obtain rfl : a = b := ha.symm.trans (hz.trans hb)
      obtain rfl : ga = gb := MorphismProperty.Over.Hom.ext
        ((cancel_mono (l a)).mp (congrArg (fun ψ ↦ ψ.left) hab))
      rfl
  refine ⟨y, (Scheme.isSheafFor_ofArrows G g hcov).isSeparatedFor.ext
    fun Z f ⟨v⟩ ↦ ?_⟩
  change G.obj.map _ (φ.hom.app _ y) = G.obj.map _ s
  rw [← NatTrans.naturality_apply]
  erw [hy v]
  exact he v

/-- Every étale object over a separably closed field is a disjoint union of copies of its
spectrum, and every abelian étale sheaf has vanishing positive cohomology and positive
higher direct images along any morphism from that spectrum.
Source: blueprint lemma `lem-kun-0ezp`, Stacks Project Tags 02GL, 03QO and the field case
of 0EZP (blueprint: lem-kun-0ezp).

Proof:
1. Mathlib's `Scheme.exists_fac_of_etale_of_isSepClosed` supplies, for each point v of V,
   a section of V → Spec L with image v. A section of an étale morphism is an open
   immersion. These singleton images cover V and are pairwise disjoint, so
   `nonempty_isColimit_cofanMk_of` gives the coproduct decomposition indexed by V.left.
2. The proved terminal lifting result in PointCohomology gives lifts of an epimorphic
   quotient on each copy of Spec L. The sheaf axiom glues these lifts on their disjoint
   images. On an empty overlap the empty-cover axiom gives uniqueness; on a nonempty
   overlap both components and both restriction maps coincide. Thus the private helper
   proves surjectivity on every étale object, including the empty one.
3. Global sections is terminal evaluation, which preserves epimorphisms by the same
   terminal lifting result. As an additive right adjoint it preserves kernels; hence it
   preserves homology and finite colimits. Its total right derived functor applied to
   F[0] is therefore isomorphic to Γ(F)[0], whose positive homology is zero.
4. Direct image is evaluation on the étale base change of each target object. Step 2
   therefore makes it preserve epimorphisms. It already preserves kernels and is
   additive, so it too is exact. The bounded-below exact-functor comparison identifies
   Rf_*(F[0]) with (f_*F)[0]. Positive homology vanishes, with no condition on f or Y. -/
theorem sepClosedField_etale_decomposition_and_vanishing
    (L : Type u) [Field L] [IsSepClosed L] :
    (∀ V : (Spec (.of L)).Etale,
      ∃ (I : Type u) (ι : I → (Spec (.of L) ⟶ V.left)),
        (∀ i : I, ι i ≫ V.hom = 𝟙 (Spec (.of L))) ∧
          Nonempty (IsColimit (Cofan.mk V.left ι))) ∧
    (∀ (F : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℤ), 0 < q →
        IsZero ((cohomology AddCommGrpCat.{u + 1} (Spec (.of L)) q).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) ∧
    (∀ (Y : Scheme.{u}) (f : Spec (.of L) ⟶ Y)
      (F : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (q : ℤ), 0 < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro V
    have : AlgebraicGeometry.Etale V.hom := V.prop
    have h (v : V.left) : ∃ l : Spec (.of L) ⟶ V.left,
        l ≫ V.hom = 𝟙 _ ∧ l default = v :=
      Scheme.exists_fac_of_etale_of_isSepClosed V.hom (𝟙 _) v
        (Subsingleton.elim (α := Spec (.of L)) _ _)
    choose l hl hv using h
    have ho (v : V.left) : IsOpenImmersion (l v) := by
      have : IsOpenImmersion (l v ≫ V.hom) := (hl v) ▸ inferInstance
      exact FormallyUnramified.isOpenImmersion_of_comp V.hom (l v)
    have hr (v : V.left) : Set.range (l v) = {v} := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        rw [Subsingleton.elim a default, hv]
        exact Set.mem_singleton _
      · intro hx
        exact ⟨default, (hv v).trans (Set.mem_singleton_iff.mp hx).symm⟩
    refine ⟨V.left, l, hl, nonempty_isColimit_cofanMk_of l ?_ ?_⟩
    · apply top_unique
      intro x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, ⟨default, hv x⟩⟩
    · intro v w hvw
      change Disjoint (l v).opensRange (l w).opensRange
      rw [← TopologicalSpace.Opens.coe_disjoint]
      change Disjoint (Set.range (l v)) (Set.range (l w))
      rw [hr, hr]
      exact Set.disjoint_singleton.mpr hvw
  · intro F q hq
    let Γ := Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1}
    have : Γ.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso
      (Sheaf.ΓNatIsoSheafSections (Spec (.of L)).smallEtaleTopology
        AddCommGrpCat.{u + 1} Scheme.isTerminalEtalePoint).symm
    have : Γ.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels Γ
    have : PreservesFiniteColimits Γ := Functor.preservesFiniteColimits_of_preservesHomology Γ
    exact (DerivedCategory.isZero_of_isLE
      ((DerivedCategory.singleFunctor _ 0).obj (Γ.obj F)) 0 q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        (Γ.singleFunctorCompRightDerivedFunctorIso.app F))
  · intro Y f F q hq
    let P := lowerStar AddCommGrpCat.{u + 1} f
    have : P.PreservesEpimorphisms := ⟨fun {G H} φ hφ ↦ by
      apply (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} (P.map φ)).mp
      apply Presheaf.isLocallySurjective_of_surjective
      intro U
      exact surjective_sections_of_epi L φ _⟩
    have : P.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels P
    have : PreservesFiniteColimits P := Functor.preservesFiniteColimits_of_preservesHomology P
    let e := (P.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
      (P.mapDerivedCategoryPlusSingleFunctor 0).app F
    exact (DerivedCategory.isZero_of_isLE
      ((DerivedCategory.singleFunctor _ 0).obj (P.obj F)) 0 q hq).of_iso
      ((DerivedCategory.Plus.homologyFunctor _ q).mapIso e)

end AlgebraicGeometry.Etale
