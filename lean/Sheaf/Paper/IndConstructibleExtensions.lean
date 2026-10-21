/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q20, K4
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import Sheaf.CategoryTheory.ExtOneExtensionClassification
import Sheaf.Paper.ConstructibleExtContinuity
import Sheaf.Paper.CoefficientHeartClosure
import Sheaf.Paper.IndHeartFullFaithfulness
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected

/-!
# Extensions of ind-constructible module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart,
`sk-prop-ind-heart-extensions.md` and its proof (blueprint: det-ind-heart-extensions).

The two coefficient cases use the existing finite constant-model constructibility predicate.
IndCons is `ObjectProperty.ind.{u + 1}` in the internal-module category itself, with small
filtered presentations and closure under isomorphisms. No abstract ind-category replaces
this ambient category.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Surjectivity of the degree-one Hom comparison descends each Ext class to one stage.
Source: blueprint extension proof, Pullback to C_alpha
(blueprint: det-ind-heart-extensions). -/
private theorem ext_stage_of_comparison
    {A : Type w} [Category.{u + 1} A] [Abelian A]
    [HasDerivedCategory.{u + 1} A] [HasExt.{u + 1} A]
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (C : A) {N : A} (pres : ColimitPresentation J N)
    (hcont : IsIso (colimit.desc _
      (((DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ (1 : ℤ) ⋙
        preadditiveCoyoneda.obj
          (Opposite.op ((DerivedCategory.singleFunctor A 0).obj C))).mapCocone
            (Cocone.mk N pres.ι)))))
    (ξ : Abelian.Ext C N 1) :
    ∃ (i : J) (η : Abelian.Ext C (pres.diag.obj i) 1),
      η.comp (Abelian.Ext.mk₀ (pres.ι.app i)) (add_zero 1) = ξ := by
  classical
  let F := DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ (1 : ℤ) ⋙
    preadditiveCoyoneda.obj
      (Opposite.op ((DerivedCategory.singleFunctor A 0).obj C))
  let c := F.mapCocone (Cocone.mk N pres.ι)
  let f := colimit.desc _ c
  have : IsIso f := hcont
  obtain ⟨i, y, hy⟩ := Concrete.colimit_exists_rep (pres.diag ⋙ F) (inv f ξ.hom)
  refine ⟨i, Abelian.Ext.homEquiv.symm y, ?_⟩
  apply Abelian.Ext.ext
  have he : f (colimit.ι (pres.diag ⋙ F) i y) = ξ.hom := by
    rw [hy]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id f) ξ.hom
  have he' : (F.map (pres.ι.app i)) y = ξ.hom := by
    calc
      _ = f ((colimit.ι (pres.diag ⋙ F) i) y) :=
        (ConcreteCategory.congr_hom (colimit.ι_desc c i) y).symm
      _ = _ := he
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  change Abelian.Ext.homEquiv (Abelian.Ext.homEquiv.symm y) ≫ _ = _
  rw [Equiv.apply_symm_apply]
  exact he'

/-- A pushout of a finite-stage extension is a filtered colimit of constructible extensions.
Source: blueprint extension proof, Colimit over beta-prime
(blueprint: det-ind-heart-extensions). -/
private theorem ind_pushout_extension
    {A : Type w} [Category.{u + 1} A] [Abelian A]
    (P : ObjectProperty A) [P.IsClosedUnderExtensions]
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    {N : A} (pres : ColimitPresentation J N) (hp : ∀ j, P (pres.diag.obj j))
    (i : J) (T : ShortComplex A) (hT : T.ShortExact)
    (e : T.X₁ ≅ pres.diag.obj i) (hC : P T.X₃) :
    ObjectProperty.ind.{u + 1} P (pushout (pres.ι.app i) (e.inv ≫ T.f)) := by
  classical
  have : IsConnected (Under i) := IsFiltered.isConnected _
  let G := Under.pushout (e.inv ≫ T.f) ⋙ Under.forget T.X₂
  let F := Under.post (X := i) pres.diag ⋙ G
  let c := G.mapCocone ((Cocone.mk N pres.ι).underPost i)
  have : PreservesColimitsOfShape (Under i) G :=
    Limits.comp_preservesColimitsOfShape _ _
  have hc : IsColimit c := isColimitOfPreserves G (pres.isColimit.underPost i)
  refine ⟨Under i, inferInstance, inferInstance, ⟨F, c.ι, hc⟩, ?_⟩
  intro j
  let T' := ShortComplex.mk (e.inv ≫ T.f) T.g (by simp [T.zero])
  have hT' : T'.ShortExact := by
    exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by simp [T']) (by simp [T'])) hT
  obtain ⟨_, p, hz, _, _, hE, _⟩ :=
    pushout_short_exact_sequence T' hT' (pres.diag.map j.hom)
  exact P.prop_X₂_of_shortExact hE (hp j.right) hC

/-- Filtered-colimit closures of finitely presentable extension-closed objects are extension closed.
Source: Stacks Project, Homology, Tag 010I and Categories, Tag 002V
(blueprint: det-ind-heart-extensions).
The proof uses the stated degree-one Ext descent hypothesis. It presents the quotient
and pulls back the short exact sequence; degree-one Ext
continuity descends each pullback extension to a finitely presentable stage, and exact
filtered colimits reassemble the original extension. -/
private theorem ind_extension_of_finitelyPresentable
    {A : Type w} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (P : ObjectProperty A)
    (hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} A)
    [P.IsClosedUnderExtensions] [HasExt.{u + 1} A]
    (hdesc : ∀ (C : A), P C → ∀ {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
      {N : A} (pres : ColimitPresentation J N) (_hp : ∀ j, P (pres.diag.obj j))
      (ξ : Abelian.Ext C N 1), ∃ (i : J) (η : Abelian.Ext C (pres.diag.obj i) 1),
        η.comp (Abelian.Ext.mk₀ (pres.ι.app i)) (add_zero 1) = ξ)
    (S : ShortComplex A) (hS : S.ShortExact)
    (hN : ObjectProperty.ind.{u + 1} P S.X₁)
    (hB : ObjectProperty.ind.{u + 1} P S.X₃) :
    ObjectProperty.ind.{u + 1} P S.X₂ := by
  classical
  let := HasDerivedCategory.standard A
  have hquot : ∀ (T : ShortComplex A), T.ShortExact →
      ObjectProperty.ind.{u + 1} P T.X₁ → P T.X₃ →
      ObjectProperty.ind.{u + 1} P T.X₂ := by
    intro T hT hN hC
    obtain ⟨I, _, _, pres, hp⟩ := hN
    obtain ⟨i, η, hη⟩ := hdesc T.X₃ hC pres hp hT.extClass
    obtain ⟨B, a, b, hz, hE, hξ⟩ :=
      (ext_one_extension_classification.{u + 1, u + 1, max (u + 1) w,
        max (u + 1) w, u + 1, u + 1, w, w} (pres.diag.obj i) T.X₃).1 η
    let E := ShortComplex.mk a b hz
    obtain ⟨_, p, hpz, hp', _, hL, m, hm₁, hm₂, hm₃⟩ :=
      pushout_short_exact_sequence E hE (pres.ι.app i)
    have heq : hL.extClass = hT.extClass := by
      have hn := hE.extClass_naturality hL m
      rw [hm₁, hm₃, hξ] at hn
      rw [Abelian.Ext.mk₀_id_comp] at hn
      exact hn.symm.trans hη
    obtain ⟨e, _, _⟩ := ((ext_one_extension_classification.{u + 1, u + 1, max (u + 1) w,
      max (u + 1) w, u + 1, u + 1, w, w} T.X₁ T.X₃).2.1
      _ _ _ _ _ hL _ _ _ hT).mp heq
    exact (ObjectProperty.ind P).prop_of_iso e
      (by
        have h := ind_pushout_extension P pres hp i E hE (Iso.refl _) hC
        exact (ObjectProperty.ind P).prop_of_iso
          (pushout.congrHom (f₂ := pres.ι.app i) (g₂ := E.f) rfl
            (Category.id_comp E.f)) h)
  obtain ⟨J, _, _, pres, hp⟩ := hB
  have : IsConnected J := IsFiltered.isConnected _
  let c : Cocone pres.diag := ⟨S.X₃, pres.ι⟩
  let F := pullback c.ι ((Functor.const J).map S.g)
  have hc : IsColimit c := pres.isColimit
  have hF : ∀ j, ObjectProperty.ind.{u + 1} P (F.obj j) := by
    intro j
    let a := c.ι.app j
    let k : S.X₁ ⟶ pullback a S.g := pullback.lift 0 S.f (by simp [S.zero])
    have hk : k ≫ pullback.fst a S.g = 0 := by simp [k]
    let T := ShortComplex.mk k (pullback.fst a S.g) hk
    have := hS.mono_f
    have := hS.epi_g
    have : Mono k := mono_of_mono_fac
      (show k ≫ pullback.snd a S.g = S.f by simp [k])
    have hT : T.ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
      rw [ShortComplex.exact_iff_exact_up_to_refinements]
      intro W x hx
      obtain ⟨W', π, hπ, y, hy⟩ := hS.exact.exact_up_to_refinements
        (x ≫ pullback.snd a S.g) (by
          rw [Category.assoc, ← pullback.condition, reassoc_of% hx, zero_comp])
      refine ⟨W', π, hπ, y, ?_⟩
      apply pullback.hom_ext
      · simpa [T, k] using congrArg (π ≫ ·) hx
      · simpa [T, k] using hy
    exact (ObjectProperty.ind P).prop_of_iso
      (pullbackObjIso c.ι ((Functor.const J).map S.g) j).symm (hquot T hT hN (hp j))
  have hM : ObjectProperty.ind.{u + 1} (ObjectProperty.ind.{u + 1} P) S.X₂ :=
    ⟨J, inferInstance, inferInstance,
      ⟨F, pullback.snd c.ι ((Functor.const J).map S.g),
        hc.pullbackOfHasExactColimitsOfShape S.g⟩, hF⟩
  rwa [ObjectProperty.ind_ind hfp] at hM


/-- Extensions of ind-constructible sheaves with finite field coefficients are
ind-constructible. Source: blueprint sk-prop-ind-heart-extensions, with the Noetherian
setting of det-ind-heart-extensions (blueprint: det-ind-heart-extensions).

Proof:
1. The existing ambient sheaf and module instances make the category Grothendieck abelian.
2. Present the kernel and quotient by small filtered diagrams of constructibles. Pull back
along the quotient stages. Exactness is verified by the exact-up-to-refinements criterion.
3. Apply constructible-sheaf Ext continuity in degree one to the kernel presentation.
4. Every element of a filtered colimit of abelian groups comes from one stage. The existing
Ext-one classification represents it by a short exact sequence; pushout and Ext naturality
identify its pushout with the pullback extension, up to an endpoint-fixed isomorphism.
5. The filtered undercategory of a kernel stage has final projection to the index category;
its induced under-cocone is colimiting by Mathlib IsColimit.underPost.
6. Push out the finite-stage extension over this undercategory. Constructible extension
closure, supplied by det-lem-coefficient-heart-closure, makes every stage constructible.
7. Cobase change preserves colimits, and the undercategory forgetful functor preserves
connected colimits. Their composite exhibits the pushout as the required ind-presentation.
8. Exact filtered colimits commute with the quotient-stage pullbacks by Mathlib
IsColimit.pullbackOfHasExactColimitsOfShape. Finite presentability, supplied by
det-ind-heart-full-faithfulness, and ObjectProperty.ind_ind flatten this ind-of-ind
presentation to an ind-constructible presentation. -/
theorem indConstructible_of_shortExact
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (S : ShortComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hS : S.ShortExact)
    (hN : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) S.X₁)
    (hB : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) S.X₃) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) S.X₂ := by
  have : IsNoetherian X := ⟨⟩
  let P : ObjectProperty _ := IsConstantModelConstructible (Profinite.continuousMapRingObj E) X
  have hP : P.IsClosedUnderExtensions := by
    let := (coefficientHeart_closure ℓ
      (Profinite.padicSubfieldCondensedRing ℓ E.1) (by
        left
        exact ⟨E.1, E.2, rfl⟩)).2 X |>.2.2.1
    infer_instance
  have := hP
  have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ := by
    intro M hM
    obtain ⟨h, _⟩ := (indHeart_fullFaithfulness ℓ X).1 E
    exact h ⟨M, hM⟩
  apply ind_extension_of_finitelyPresentable P hfp ?_ S hS hN hB
  intro C hC J _ _ N pres hp ξ
  apply ext_stage_of_comparison C pres _ ξ
  exact constructible_sheaf_ext_continuity ℓ E
    (Profinite.padicSubfieldCondensedRing ℓ E.1) (Or.inl rfl)
    X C hC pres.diag (Cocone.mk N pres.ι) pres.isColimit 1

/-- Extensions of ind-constructible sheaves with condensed algebraic-closure coefficients
are ind-constructible. Source: blueprint sk-prop-ind-heart-extensions, with the Noetherian
setting of det-ind-heart-extensions (blueprint: det-ind-heart-extensions).

Proof: use the same eight-step extension-class and filtered-pushout argument as the
finite-field coefficient theorem. Constructible extension closure and finite presentability
are supplied by the algebraic-closure clauses of the same existing declarations. Apply
constructible-sheaf Ext continuity with algebraic-closure coefficients; its auxiliary finite
intermediate field can be the bottom field. This does not change the coefficient category
or impose an additional hypothesis on the extension. -/
theorem indConstructible_of_shortExact_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (S : ShortComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hS : S.ShortExact)
    (hN : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) S.X₁)
    (hB : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) S.X₃) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) S.X₂ := by
  have : IsNoetherian X := ⟨⟩
  let P : ObjectProperty _ := IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X
  have hP : P.IsClosedUnderExtensions := by
    let := (coefficientHeart_closure ℓ
      (Profinite.padicAlgClCondensedRing ℓ) (by right; rfl)).2 X |>.2.2.1
    infer_instance
  have := hP
  have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ := by
    intro M hM
    obtain ⟨_, h⟩ := indHeart_fullFaithfulness ℓ X
    exact h.1 ⟨M, hM⟩
  apply ind_extension_of_finitelyPresentable P hfp ?_ S hS hN hB
  intro C hC J _ _ N pres hp ξ
  apply ext_stage_of_comparison C pres _ ξ
  exact constructible_sheaf_ext_continuity ℓ ⟨⊥, inferInstance⟩
    (Profinite.padicAlgClCondensedRing ℓ) (Or.inr rfl)
    X C hC pres.diag (Cocone.mk N pres.ι) pres.isColimit 1

end AlgebraicGeometry.ProEtale
