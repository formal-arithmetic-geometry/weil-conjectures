/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Exact open/closed calculus on unbounded derived categories

Source: blueprint `det-prop-scalar-six-pullback`, proof (2), exact open/closed route;
Stacks 015F, 04VG, 010N, 05QB, 05RT and 05RU.
(blueprint: lem-sfb-exact-open-closed-unbounded-calculus).

The four functors below are Mathlib's termwise-localized `mapDerivedCategory`.
The four component equations specify the actual localized adjunction maps using
`mapDerivedCategoryFactors`, rather than merely asserting existence of some adjunction.
The triangle identities are part of each resulting `Adjunction` structure.
-/

@[expose] public section

set_option autoImplicit false

universe uX uU uZ vX vU vZ wX wU wZ

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem iso_of_localized_components
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : D ⥤ E} (t : F ⟶ G) (h : ∀ K, IsIso (t.app (L.obj K))) : IsIso t := by
  have := Localization.essSurj L W
  have (H : D) : IsIso (t.app H) := by
    rw [NatTrans.isIso_app_iff_of_iso t (L.objObjPreimageIso H).symm]
    exact h _
  exact NatIso.isIso_of_isIso_app t

private theorem derived_mixed_zero
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : ∀ M, IsZero (G.obj (F.obj M))) (H : DerivedCategory A) :
    IsZero (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj H)) := by
  apply G.isZero_mapDerivedCategory_obj
  intro n
  exact (h _).of_iso (G.mapIso ((F.mapDerivedCategoryHomologyFunctorIso n).symm.app H))

/-- Exact open/closed localization data descend to the ordinary unbounded derived
categories with their actual adjunction maps and support calculus.
Source: blueprint `det-prop-scalar-six-pullback`, proof (2), exact open/closed route;
Stacks 015F, 04VG, 010N, 05QB, 05RT and 05RU.
(blueprint: lem-sfb-exact-open-closed-unbounded-calculus).

Proof: (1) Apply `lem-weil-pbc-exact-functor-derived-factorization` to all four exact
functors; their standard factorizations identify the derived value on a complex
with termwise application. (2) Localize the degreewise adjunctions as in
`def-weil-exact-derived-adjunction`. The localization universal property
`lem-weil-pbc-localization-universal-property` gives precisely the four component
formulas displayed below. (3) Precompose both triangle equations with the complex
localization functor. They become the original triangle equations in each degree;
localization extensionality proves the derived triangle identities.
(4) Localize the inverses of the open unit and closed counit, and the two mixed
zero functors; this proves the first four support conclusions.
(5) Descend the natural cohomology comparisons of
`lem-weil-pbc-exact-functor-complex-cohomology` through localization in every integer
degree. (6) For a derived morphism whose two restrictions are invertible, apply the
assumed short exact sequence to its cohomology objects. Naturality gives a diagram
of short exact rows. Its outside maps are invertible, so
`lem-weil-pbc-short-five-lemma` makes the middle map invertible. Apply
`lem-weil-pbc-unbounded-derived-iso-cohomology` in all degrees.
(7) If the open restriction of H is zero, the open restriction of the closed unit
is a map between zero objects. Its closed restriction is the inverse closed
counit by the left triangle identity. Joint reflection makes that unit invertible.
(8) On two objects X,Y in the essential image of the derived closed extension,
their closed units are invertible. The inverse on Hom sets sends a to
`eta_X ≫ D(I).map a ≫ inv eta_Y`. Naturality of eta proves one inverse equation;
the closed triangle identity and naturality of the counit prove the other.
No step imposes a bound, an injective resolution or a recollement hypothesis. -/
theorem exactOpenClosedUnboundedCalculus
    {AX : Type uX} {AU : Type uU} {AZ : Type uZ}
    [Category.{vX} AX] [Category.{vU} AU] [Category.{vZ} AZ]
    [Abelian AX] [Abelian AU] [Abelian AZ]
    [HasDerivedCategory.{wX} AX] [HasDerivedCategory.{wU} AU]
    [HasDerivedCategory.{wZ} AZ]
    (J : AU ⥤ AX) (P : AX ⥤ AU) (Q : AX ⥤ AZ) (I : AZ ⥤ AX)
    [J.Additive] [P.Additive] [Q.Additive] [I.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (a : J ⊣ P) (b : Q ⊣ I)
    (hopen : IsIso a.unit) (hclosed : IsIso b.counit)
    (hPI : ∀ M : AZ, IsZero (P.obj (I.obj M)))
    (hQJ : ∀ M : AU, IsZero (Q.obj (J.obj M)))
    (hseq : ∀ M : AX, ∃ h : a.counit.app M ≫ b.unit.app M = 0,
      (ShortComplex.mk (a.counit.app M) (b.unit.app M) h).ShortExact) :
    ∃ (da : J.mapDerivedCategory ⊣ P.mapDerivedCategory)
      (db : Q.mapDerivedCategory ⊣ I.mapDerivedCategory),
      (∀ K : CochainComplex AU ℤ,
        da.unit.app (DerivedCategory.Q.obj K) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
            P.mapDerivedCategoryFactors.inv.app ((J.mapHomologicalComplex (.up ℤ)).obj K) ≫
            P.mapDerivedCategory.map (J.mapDerivedCategoryFactors.inv.app K)) ∧
      (∀ K : CochainComplex AX ℤ,
        da.counit.app (DerivedCategory.Q.obj K) =
          J.mapDerivedCategory.map (P.mapDerivedCategoryFactors.hom.app K) ≫
            J.mapDerivedCategoryFactors.hom.app ((P.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app K)) ∧
      (∀ K : CochainComplex AX ℤ,
        db.unit.app (DerivedCategory.Q.obj K) =
          DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
            I.mapDerivedCategoryFactors.inv.app ((Q.mapHomologicalComplex (.up ℤ)).obj K) ≫
            I.mapDerivedCategory.map (Q.mapDerivedCategoryFactors.inv.app K)) ∧
      (∀ K : CochainComplex AZ ℤ,
        db.counit.app (DerivedCategory.Q.obj K) =
          Q.mapDerivedCategory.map (I.mapDerivedCategoryFactors.hom.app K) ≫
            Q.mapDerivedCategoryFactors.hom.app ((I.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).counit.app K)) ∧
      IsIso da.unit ∧ IsIso db.counit ∧
      (∀ H : DerivedCategory AZ,
        IsZero (P.mapDerivedCategory.obj (I.mapDerivedCategory.obj H))) ∧
      (∀ H : DerivedCategory AU,
        IsZero (Q.mapDerivedCategory.obj (J.mapDerivedCategory.obj H))) ∧
      (∀ (K L : DerivedCategory AX) (f : K ⟶ L),
        IsIso (P.mapDerivedCategory.map f) → IsIso (Q.mapDerivedCategory.map f) → IsIso f) ∧
      (∀ H : DerivedCategory AX,
        IsZero (P.mapDerivedCategory.obj H) → IsIso (db.unit.app H)) ∧
      (∀ K L : DerivedCategory AX,
        I.mapDerivedCategory.essImage K → I.mapDerivedCategory.essImage L →
          Function.Bijective (fun f : K ⟶ L ↦ Q.mapDerivedCategory.map f)) := by
  let : CatCommSq (J.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q J.mapDerivedCategory := ⟨J.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (P.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q P.mapDerivedCategory := ⟨P.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (Q.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q Q.mapDerivedCategory := ⟨Q.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (I.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q I.mapDerivedCategory := ⟨I.mapDerivedCategoryFactors.symm⟩
  let da := (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso AU (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso AX (.up ℤ))
    J.mapDerivedCategory P.mapDerivedCategory
  let db := (b.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso AX (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso AZ (.up ℤ))
    Q.mapDerivedCategory I.mapDerivedCategory
  have au (K : CochainComplex AU ℤ) :=
    (a.mapHomologicalComplex (.up ℤ)).localization_unit_app
      DerivedCategory.Q (HomologicalComplex.quasiIso AU (.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso AX (.up ℤ))
      J.mapDerivedCategory P.mapDerivedCategory K
  have ac (K : CochainComplex AX ℤ) :=
    (a.mapHomologicalComplex (.up ℤ)).localization_counit_app
      DerivedCategory.Q (HomologicalComplex.quasiIso AU (.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso AX (.up ℤ))
      J.mapDerivedCategory P.mapDerivedCategory K
  have bu (K : CochainComplex AX ℤ) :=
    (b.mapHomologicalComplex (.up ℤ)).localization_unit_app
      DerivedCategory.Q (HomologicalComplex.quasiIso AX (.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso AZ (.up ℤ))
      Q.mapDerivedCategory I.mapDerivedCategory K
  have bc (K : CochainComplex AZ ℤ) :=
    (b.mapHomologicalComplex (.up ℤ)).localization_counit_app
      DerivedCategory.Q (HomologicalComplex.quasiIso AX (.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso AZ (.up ℤ))
      Q.mapDerivedCategory I.mapDerivedCategory K
  have hau : IsIso da.unit := by
    apply iso_of_localized_components DerivedCategory.Q
      (HomologicalComplex.quasiIso AU (.up ℤ))
    intro K
    rw [au]
    have : IsIso ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
      have (n : ℤ) : IsIso (((a.mapHomologicalComplex (.up ℤ)).unit.app K).f n) := by
        change IsIso (a.unit.app (K.X n))
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  have hbc : IsIso db.counit := by
    apply iso_of_localized_components DerivedCategory.Q
      (HomologicalComplex.quasiIso AZ (.up ℤ))
    intro K
    rw [bc]
    have : IsIso ((b.mapHomologicalComplex (.up ℤ)).counit.app K) := by
      have (n : ℤ) : IsIso (((b.mapHomologicalComplex (.up ℤ)).counit.app K).f n) := by
        change IsIso (b.counit.app (K.X n))
        infer_instance
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  have hPI' := derived_mixed_zero I P hPI
  have hQJ' := derived_mixed_zero J Q hQJ
  have hreflect (K L : DerivedCategory AX) (f : K ⟶ L)
      (hp : IsIso (P.mapDerivedCategory.map f))
      (hq : IsIso (Q.mapDerivedCategory.map f)) : IsIso f := by
    rw [DerivedCategory.isIso_iff]
    intro n
    let g := (DerivedCategory.homologyFunctor AX n).map f
    have : IsIso (P.map g) :=
      (NatIso.isIso_map_iff (P.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by change IsIso ((DerivedCategory.homologyFunctor AU n).map
              (P.mapDerivedCategory.map f)); infer_instance)
    have : IsIso (Q.map g) :=
      (NatIso.isIso_map_iff (Q.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by change IsIso ((DerivedCategory.homologyFunctor AZ n).map
              (Q.mapDerivedCategory.map f)); infer_instance)
    obtain ⟨hK, hsK⟩ := hseq ((DerivedCategory.homologyFunctor AX n).obj K)
    obtain ⟨hL, hsL⟩ := hseq ((DerivedCategory.homologyFunctor AX n).obj L)
    let t : ShortComplex.mk _ _ hK ⟶ ShortComplex.mk _ _ hL :=
      { τ₁ := J.map (P.map g)
        τ₂ := g
        τ₃ := I.map (Q.map g)
        comm₁₂ := a.counit.naturality g
        comm₂₃ := b.unit.naturality g }
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ t hsK hsL
  have hunit (H : DerivedCategory AX) (hH : IsZero (P.mapDerivedCategory.obj H)) :
      IsIso (db.unit.app H) := by
    apply hreflect
    · exact isIso_of_source_target_iso_zero _ hH.isoZero (hPI' _).isoZero
    · have : IsIso (Q.mapDerivedCategory.map (db.unit.app H) ≫
          db.counit.app (Q.mapDerivedCategory.obj H)) := by
        rw [db.left_triangle_components H]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (db.counit.app _)
  refine ⟨da, db, au, ac, bu, bc, hau, hbc, hPI', hQJ', hreflect, hunit, ?_⟩
  intro K L hK hL
  have hηK : IsIso (db.unit.app K) :=
    hunit K ((hPI' hK.witness).of_iso (P.mapDerivedCategory.mapIso hK.getIso).symm)
  have hηL : IsIso (db.unit.app L) :=
    hunit L ((hPI' hL.witness).of_iso (P.mapDerivedCategory.mapIso hL.getIso).symm)
  let s (f : Q.mapDerivedCategory.obj K ⟶ Q.mapDerivedCategory.obj L) : K ⟶ L :=
    db.unit.app K ≫ I.mapDerivedCategory.map f ≫ inv (db.unit.app L)
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨s, ?_, ?_⟩
  · intro f
    dsimp [s]
    rw [← Functor.comp_map, ← db.unit.naturality_assoc]
    simp
  · intro f
    dsimp [s]
    simp only [Functor.map_comp]
    have hk : Q.mapDerivedCategory.map (db.unit.app K) =
        inv (db.counit.app (Q.mapDerivedCategory.obj K)) :=
      IsIso.eq_inv_of_inv_hom_id (db.left_triangle_components K)
    have hl : Q.mapDerivedCategory.map (inv (db.unit.app L)) =
        db.counit.app (Q.mapDerivedCategory.obj L) := by
      rw [Functor.map_inv]
      exact IsIso.inv_eq_of_hom_inv_id (db.left_triangle_components L)
    rw [hk, hl]
    change inv (db.counit.app _) ≫ (I.mapDerivedCategory ⋙ Q.mapDerivedCategory).map f ≫
      db.counit.app _ = f
    rw [db.counit.naturality]
    simp

end CategoryTheory
