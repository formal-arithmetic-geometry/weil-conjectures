/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups A2, A4
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
import Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Sheaf.Paper.ProfinitePointPullback
import Mathlib.Data.Fintype.Order
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Cohomological boundedness of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-bounded)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

private theorem abelian_isZero_of_finite_openCover (n : ℕ) :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (U : Fin n → X.Opens) (_ : ⨆ a, U a = ⊤)
      (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}),
      (∀ a, IsZero ((ProEtale.upperStar Ab.{u + 1} (U a).ι).obj F)) → IsZero F := by
  induction n with
  | zero =>
    intro X _ U hU F _
    have : IsEmpty X := by
      refine ⟨fun x ↦ ?_⟩
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hU] at hx
      simp at hx
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    have : IsEmpty T.left := ⟨fun t ↦ (inferInstance : IsEmpty X).false (T.hom t)⟩
    exact (isZero_zero _).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty F T).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  | succ n ih =>
    intro X _ U hU F hF
    obtain ⟨Z, i, _, hi⟩ : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
        Set.range i.base = (Set.range (U 0).ι.base)ᶜ :=
      ⟨_, _, inferInstance, (U 0).ι.range_closedComplement⟩
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    have : IsNoetherian Z := {}
    have hZ : IsZero ((ProEtale.upperStar Ab.{u + 1} i).obj F) := by
      apply ih (fun a ↦ i ⁻¹ᵁ U a.succ)
      · refine top_le_iff.1 fun z _ ↦ ?_
        obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU.ge (Set.mem_univ (i z)))
        have hz : i z ∉ Set.range (U 0).ι := by
          rw [← Set.mem_compl_iff, ← hi]
          exact ⟨z, rfl⟩
        obtain ⟨a, rfl⟩ := Fin.eq_succ_of_ne_zero (n := n) (i := m) (by
          rintro rfl
          exact hz (by simpa using hm))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hm⟩
      · intro a
        have hz := (ProEtale.upperStar Ab.{u + 1} (i ∣_ U a.succ)).map_isZero (hF a.succ)
        have hz' := hz.of_iso ((ProEtale.upperStarComp Ab.{u + 1}
          (i ∣_ U a.succ) (U a.succ).ι).app F)
        rw [morphismRestrict_ι] at hz'
        exact hz'.of_iso ((ProEtale.upperStarComp Ab.{u + 1}
          (i ⁻¹ᵁ U a.succ).ι i).app F).symm
    have hu := (abelian_closed_support i (U 0).ι (by rw [hi]; simp)).2 F (hF 0)
    have := hu
    exact ((ProEtale.lowerStar Ab.{u + 1} i).map_isZero hZ).of_iso
      (asIso ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- The supplied localizing right adjoint has finite cohomological amplitude on a bounded
constructible input.

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`, Part (2).
Proof: the proved affine-restriction theorem makes the restriction of `G K` bounded
constructible on every affine open of the source. Choose a finite affine cover and choose
an interval of cohomological vanishing on each member. Finite ranges of integers are bounded
above and below, so one interval contains all those intervals. Outside it the restrictions
of the corresponding homology module vanish, since exact pullback commutes with homology.
Forgetting the coefficient action identifies these restrictions with the abelian sheaf
restrictions. Finite open-cover zero detection follows by open/closed induction and the
supported-unit isomorphism. Thus each homology module outside the common interval is zero.
No integral-model comparison or second choice of a right adjoint is used.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded)
-/
theorem ellAdic_localizing_rightAdjoint_obj_isBounded
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  classical
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Z.left := {}
  let C := Z.left.affineCover.finiteSubcover
  let e := (Fintype.equivFin C.I₀).symm
  let U (a : Fin (Fintype.card C.I₀)) : Z.left.Opens := (C.f (e a)).opensRange
  have hU : ⨆ a, U a = ⊤ :=
    (e.surjective.iSup_comp (fun a ↦ (C.f a).opensRange)).trans C.iSup_opensRange
  let A := (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj
  have hlocal (a) : ∃ l r : ℤ, ∀ n : ℤ, (n < l ∨ r < n) →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj
        (D(((U a).ι)^*⟦Λ⟧).obj A)) := by
    let Ua : Over (Spec (.of k)) := Over.mk ((U a).ι ≫ Z.hom)
    let j : Ua ⟶ Z := Over.homMk (U a).ι rfl
    have : IsAffine Ua.left := isAffineOpen_opensRange (C.f (e a))
    have : LocallyOfFiniteType Ua.hom := inferInstanceAs
      (LocallyOfFiniteType ((U a).ι ≫ Z.hom))
    have : QuasiCompact Ua.hom := inferInstanceAs (QuasiCompact ((U a).ι ≫ Z.hom))
    have : IsSeparated Ua.hom := inferInstanceAs (IsSeparated ((U a).ι ≫ Z.hom))
    have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (U a).ι)
    have h := affine_restriction_boundedConstructible Λ ℓ g hΛ G adj K j
    have h' := (mem_boundedConstructible_iff _ _).mp h
    simpa only [j, Ua, Over.homMk_left, Over.mk_left] using h'.1
  choose l r hlr using hlocal
  obtain ⟨a, ha⟩ := Finite.bddBelow_range l
  obtain ⟨b, hb⟩ := Finite.bddAbove_range r
  refine ⟨a, b, fun n hn ↦ ?_⟩
  let M := (DerivedCategory.homologyFunctor _ n).obj A
  have hM : IsZero M.X := by
    apply abelian_isZero_of_finite_openCover _ U hU M.X
    intro q
    have hz : IsZero ((DerivedCategory.homologyFunctor _ n).obj
        (D(((U q).ι)^*⟦Λ⟧).obj A)) := hlr q n (by
      rcases hn with hn | hn
      · exact Or.inl (lt_of_lt_of_le hn (ha ⟨q, rfl⟩))
      · exact Or.inr (lt_of_le_of_lt (hb ⟨q, rfl⟩) hn))
    have hz' := hz.of_iso
      ((((U q).ι)^*⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).app A)
    have hz'' := (Mod.forget (condensedRingObj Λ (U q).toScheme)).map_isZero hz'
    exact hz''.of_iso ((profinitePointModuleForgetPullbackIso Λ (U q).ι).app M).symm
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (Mod.forget (condensedRingObj Λ Z.left)).map_injective
  exact hM.eq_of_src _ _

/-- The canonical right adjoint inherits the same finite bounds as any supplied adjoint.

Source: blueprint `det-existence-restriction.proof.md`, Part (2).
Proof: apply the preceding finite-affine-cover theorem to the adjunction associated to
exactly the supplied `IsLeftAdjoint` witness. No choice comparison is needed.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded-canonical)
-/
theorem ellAdic_localizing_canonical_rightAdjoint_obj_isBounded
    (hF : (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsLeftAdjoint)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (((@Functor.rightAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF).obj
          ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  exact ellAdic_localizing_rightAdjoint_obj_isBounded Λ ℓ g hΛ
    (@Functor.rightAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF)
    (@Adjunction.ofIsLeftAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF) K

end AlgebraicGeometry.ProEtale.CondensedRing
