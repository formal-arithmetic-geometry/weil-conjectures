/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Over
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!+# Assembly of finitely many quasi-compact scheme atlases

Source: Stacks Project, Properties of Spaces, Tags 03E3 and 040T;
Topologies, Tag 0217(2),(3); Schemes, Tags 01JB and 01JC
(blueprint: lem-trf-space-finite-qc-atlas-assembly).

The coproduct is taken in schemes over the base. The forgetful functor creates this
coproduct, so its underlying scheme is the disjoint union of the given schemes.
The restriction equations characterize the induced atlas map uniquely. Presheaf
pullbacks here are also sheaf pullbacks, since the factors are fppf sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

private noncomputable def underlyingColimit {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {U : I → Over S} {T : Over S} {j : ∀ i, U i ⟶ T}
    (h : IsColimit (Cofan.mk T j)) :
    IsColimit (Cofan.mk T.left (fun i ↦ (j i).left)) :=
  (Cofan.isColimitMapCoconeEquiv (Over.forget S) U _).1
    (isColimitOfPreserves (Over.forget S) h)

private noncomputable def coproductIso {I : Type v} [Small.{u} I] {U : I → Scheme.{u}}
    {T : Scheme.{u}} {j : ∀ i, U i ⟶ T} (h : IsColimit (Cofan.mk T j)) :
    (∐ U) ≅ T :=
  (coproductIsCoproduct U).coconePointUniqueUpToIso h

private lemma coproductIso_ι {I : Type v} [Small.{u} I] {U : I → Scheme.{u}}
    {T : Scheme.{u}} {j : ∀ i, U i ⟶ T} (h : IsColimit (Cofan.mk T j)) (i : I) :
    Sigma.ι U i ≫ (coproductIso h).hom = j i := by
  exact (coproductIsCoproduct U).comp_coconePointUniqueUpToIso_hom h ⟨i⟩

private noncomputable abbrev coproductCover {I : Type v} [Small.{u} I] {U : I → Scheme.{u}}
    {T : Scheme.{u}} {j : ∀ i, U i ⟶ T} (h : IsColimit (Cofan.mk T j)) :
    T.OpenCover :=
  (sigmaOpenCover U).pushforwardIso (coproductIso h).hom

private lemma coproduct_open {I : Type v} [Small.{u} I] {U : I → Scheme.{u}}
    {T : Scheme.{u}} {j : ∀ i, U i ⟶ T} (h : IsColimit (Cofan.mk T j)) (i : I) :
    IsOpenImmersion (j i) := by
  rw [← coproductIso_ι h i]
  infer_instance

private noncomputable def sheafCoproduct {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {U : I → Over S} {T : Over S} {j : ∀ i, U i ⟶ T}
    (h : IsColimit (Cofan.mk T j)) :
    IsColimit (Cofan.mk ((Scheme.fppfTopology.over S).yoneda.obj T)
      (fun i ↦ (Scheme.fppfTopology.over S).yoneda.map (j i))) := by
  let h' := underlyingColimit h
  have hop (i : I) : IsOpenImmersion (j i).left := coproduct_open h' i
  have (i : I) : Mono (j i) := by
    exact (Over.forget S).mono_of_mono_map (inferInstance : Mono (j i).left)
  have (i : I) : Mono ((Cofan.mk T j).inj i) := by
    change Mono (j i)
    infer_instance
  have hz : Scheme.zariskiTopology ≤ Scheme.fppfTopology :=
    Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
  apply (Scheme.fppfTopology.over S).isColimitCofanMkYoneda U (c := Cofan.mk T j)
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply hz
    change Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (j i).left) ∈
      Scheme.zariskiTopology T.left
    have heq : (fun i ↦ (coproductCover h').f i) = (fun i ↦ (j i).left) :=
      funext (coproductIso_ι h')
    rw [← heq]
    exact (coproductCover h').mem_grothendieckTopology
  · intro Y hi
    have : IsEmpty Y.left := isInitial_iff_isEmpty.mp
      ⟨hi.isInitialObj (Over.forget S)⟩
    rw [GrothendieckTopology.mem_over_iff]
    simpa only [OrderIso.map_bot] using
      hz _ (Y.left.bot_mem_grothendieckTopology (P := @IsOpenImmersion))
  · intro i k hik Y a b hab
    change a ≫ j i = b ≫ j k at hab
    have hcomm : a.left ≫ Sigma.ι (fun i ↦ (U i).left) i =
        b.left ≫ Sigma.ι (fun i ↦ (U i).left) k := by
      apply (cancel_mono (coproductIso h').hom).1
      simpa only [Category.assoc, coproductIso_ι, Over.comp_left] using congrArg Over.Hom.left hab
    have : IsEmpty Y.left := isEmpty_of_commSq_sigmaι_of_ne ⟨hcomm⟩ hik
    let hi := isInitialOfIsEmpty (X := Y.left)
    let (Z : Over S) : Unique (Y ⟶ Z) :=
      { default := Over.homMk (hi.to Z.left) (hi.hom_ext _ _)
        uniq := fun f ↦ by ext; exact hi.hom_ext _ _ }
    exact ⟨IsInitial.ofUnique Y⟩

private theorem atlas_relative_iff {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) [P.RespectsIso]
    {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
    IsRepresentableWith P f ↔ P.relative yoneda f := by
  constructor
  · intro h
    apply MorphismProperty.relative.of_exists
    intro T a
    obtain ⟨U, p, q, h, hp⟩ := h T a
    exact ⟨U, q, p, h, hp⟩
  · intro h T a
    exact ⟨h.rep.pullback a, h.rep.snd a, h.rep.fst a,
      h.rep.isPullback a, h.property_snd a⟩

private instance atlas_etale_baseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.inverseImage @Etale (Over.forget S)) where
  of_isPullback h hp := MorphismProperty.of_isPullback (P := @Etale)
    (h.map (Over.forget S)) hp

private theorem atlas_test {S : Scheme.{u}} {J : Type v} [Small.{u} J]
    (Z : Over S) (A : AlgebraicSpace S) (a : A.obj.obj ⟶ yoneda.obj Z)
    (W : J → Over S) (p : ∀ j, W j ⟶ Z) (hp : ∀ j, Etale (p j).left)
    (hcover : ∀ z : Z.left, ∃ j w, (p j).left w = z)
    (U : J → Over S)
    (qj : ∀ j, yoneda.obj (U j) ⟶ Limits.pullback a (yoneda.map (p j)))
    (hqjEt : ∀ j, IsEtale (qj j)) (hqjSurj : ∀ j, IsSurjective (qj j))
    (q : yoneda.obj (∐ U) ⟶ A.obj.obj)
    (hq : ∀ j, yoneda.map (Sigma.ι U j) ≫ q =
      qj j ≫ Limits.pullback.fst a (yoneda.map (p j)))
    (T : Over S) (t : yoneda.obj T ⟶ A.obj.obj) :
    ∃ (V : Over S) (v : V ⟶ T) (r : yoneda.obj V ⟶ yoneda.obj (∐ U)),
      IsPullback r (yoneda.map v) q t ∧ Surjective v.left ∧ Etale v.left := by
  classical
  let E : MorphismProperty (Over S) :=
    MorphismProperty.inverseImage @Etale (Over.forget S)
  have he {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
      IsEtale f ↔ E.relative yoneda f := atlas_relative_iff E f
  have := MorphismProperty.relative_isStableUnderBaseChange E (F := yoneda)
  -- Each chart followed by the etale projection is etale.
  have haj (j : J) : E.relative yoneda (yoneda.map (Sigma.ι U j) ≫ q) := by
    rw [hq]
    apply (E.relative yoneda).comp_mem _ _ ((he _).1 (hqjEt j))
    exact (E.relative yoneda).of_isPullback
      (IsPullback.of_hasPullback a (yoneda.map (p j))).flip
      (MorphismProperty.relative_map (P := E) (hp j))
  obtain ⟨V, v, r, hV, _⟩ := representable_etale_scheme_tests.1 A (∐ U) q T t
  let rU : V ⟶ ∐ U := yoneda.preimage r
  have hr : yoneda.map rU = r := yoneda.map_preimage r
  have hV' : IsPullback (yoneda.map rU) (yoneda.map v) q t := hr ▸ hV
  -- Test etaleness on the inverse images of the coproduct summands.
  have het : Etale v.left := by
    let D (j : J) := Limits.pullback rU (Sigma.ι U j)
    let d (j : J) : D j ⟶ V := Limits.pullback.fst _ _
    let e (j : J) : D j ⟶ U j := Limits.pullback.snd _ _
    let h' := underlyingColimit (coproductIsCoproduct U)
    have hcov : Presieve.ofArrows (fun j ↦ (U j).left)
        (fun j ↦ (Sigma.ι U j).left) ∈ Scheme.zariskiPrecoverage (∐ U).left := by
      have heq : (fun j ↦ (coproductCover h').f j) =
          (fun j ↦ (Sigma.ι U j).left) := funext (coproductIso_ι h')
      rw [← heq]
      exact (coproductCover h').mem₀
    have hD : Presieve.ofArrows (fun j ↦ (D j).left) (fun j ↦ (d j).left) ∈
        Scheme.zariskiPrecoverage V.left := by
      apply Precoverage.mem_coverings_of_isPullback _ hcov rU.left
        (fun j ↦ (d j).left) (fun j ↦ (e j).left)
      intro j
      exact (IsPullback.of_hasPullback rU (Sigma.ι U j)).map (Over.forget S)
    let 𝒰 : V.left.OpenCover :=
      { I₀ := J, X := fun j ↦ (D j).left, f := fun j ↦ (d j).left, mem₀ := hD }
    apply IsZariskiLocalAtSource.of_openCover (P := @Etale) 𝒰
    intro j
    have hDj := ((IsPullback.of_hasPullback rU (Sigma.ι U j)).flip.map yoneda).paste_vert hV'
    have hh : E (d j ≫ v) := (haj j).property t (yoneda.map (e j)) (d j ≫ v)
      (by simpa only [Functor.map_comp] using hDj)
    exact hh
  -- A point of T lifts through a base chart, its local atlas, and then V.
  have hsurj : Surjective v.left := by
    let tZ : T ⟶ Z := yoneda.preimage (t ≫ a)
    have htZ : yoneda.map tZ = t ≫ a := yoneda.map_preimage (t ≫ a)
    let B (j : J) := Limits.pullback tZ (p j)
    let b (j : J) : B j ⟶ T := Limits.pullback.fst _ _
    let w (j : J) : B j ⟶ W j := Limits.pullback.snd _ _
    have hcov : Presieve.ofArrows (fun j ↦ (W j).left) (fun j ↦ (p j).left) ∈
        (Scheme.precoverage @Etale) Z.left := by
      rw [Scheme.ofArrows_mem_precoverage_iff]
      exact ⟨hcover, hp⟩
    have hB : Presieve.ofArrows (fun j ↦ (B j).left) (fun j ↦ (b j).left) ∈
        (Scheme.precoverage @Etale) T.left := by
      apply Precoverage.mem_coverings_of_isPullback _ hcov tZ.left
        (fun j ↦ (b j).left) (fun j ↦ (w j).left)
      intro j
      exact (IsPullback.of_hasPullback tZ (p j)).map (Over.forget S)
    have hlift (j : J) (y : (B j).left) : ∃ x : V.left, v.left x = (b j).left y := by
      let cB : yoneda.obj (B j) ⟶ Limits.pullback a (yoneda.map (p j)) :=
        Limits.pullback.lift (yoneda.map (b j) ≫ t) (yoneda.map (w j)) (by
          rw [Category.assoc, ← htZ, ← Functor.map_comp, ← Functor.map_comp]
          exact congrArg (fun f ↦ yoneda.map f) Limits.pullback.condition)
      obtain ⟨L, l, z, hL, hl⟩ := hqjSurj j (B j) cB
      have hcomm : (z ≫ yoneda.map (Sigma.ι U j)) ≫ q =
          yoneda.map (l ≫ b j) ≫ t := by
        rw [Category.assoc, hq, ← Category.assoc]
        have hz := hL.w =≫ Limits.pullback.fst a (yoneda.map (p j))
        simpa only [Category.assoc, cB, Limits.pullback.lift_fst, Functor.map_comp] using hz
      let liftV : L ⟶ V := yoneda.preimage
        (hV.lift (z ≫ yoneda.map (Sigma.ι U j)) (yoneda.map (l ≫ b j)) hcomm)
      have hv : liftV ≫ v = l ≫ b j := by
        apply yoneda.map_injective
        simpa only [Functor.map_comp, liftV, yoneda.map_preimage] using
          hV.lift_snd (z ≫ yoneda.map (Sigma.ι U j)) (yoneda.map (l ≫ b j)) hcomm
      obtain ⟨x, hx⟩ := hl.surj y
      refine ⟨liftV.left x, ?_⟩
      change (liftV ≫ v).left x = _
      rw [hv, Over.comp_left, Scheme.Hom.comp_apply, hx]
    constructor
    intro x
    obtain ⟨j, y, hy⟩ := ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mp hB).1 x
    obtain ⟨z, hz⟩ := hlift j y
    exact ⟨z, hz.trans hy⟩
  exact ⟨V, v, r, hV, hsurj, het⟩

/-- The map from the finite disjoint union of the local atlas schemes is uniquely
determined by its prescribed restrictions to the summands; it is representable,
surjective and étale, and its source is quasi-compact. Together these
clauses give a quasi-compact scheme atlas of `A`.
Source: Stacks Project, Tags 03E3, 040T and 0217(2),(3)
(blueprint: lem-trf-space-finite-qc-atlas-assembly).

Proof:
1. Form the disjoint union using lem-weil-pbc-scheme-coproduct-family. For a test
   scheme mapping to this union, the inverse images of the summands are a disjoint
   open cover by lem-weil-pbc-open-immersion-base-change. This cover is fppf by
   lem-pc-zariski-coverings-are-fppf. Glue the component sections of `A` using its
   sheaf equalizer axiom from def-weil-pbc-sites-and-cohomology and
   def-trf-algebraic-space. The empty-cover axiom handles distinct overlaps and the
   empty union. Uniqueness of gluing makes this natural in the test scheme and
   uniquely determines `q` by the displayed restrictions.
2. By lem-trf-space-representable-etale-scheme-tests, `q` is representable. For a
   test `h_T → A`, let `V` represent its pullback with `h_U`, with maps `V → T`
   and `V → U`. By lem-pc-yoneda the test also determines a scheme map `T → Z`.
3. The schemes `B_j = T ×_Z W_j` form an étale cover by
   lem-weil-pbc-etale-covering-base-change. Testing `q_j` on `B_j` gives schemes
   `E_j` with surjective étale maps `E_j → B_j` by def-trf-algebraic-space.
   Lemma lem-weil-pbc-etale-covering-composition makes `E_j → T` an étale cover.
4. The inverse-image summands `D_j = V ×_U U_j` decompose `V`, using
   lem-sc-etale-fibre-product-base-change-coproduct. A section of `D_j` is a pair
   `(x,u)` with the same image in `A`. A section of `E_j` adds a map to `W_j`,
   uniquely forced by `u`; compatibility over `Z` follows from equality in `A`.
   Forgetting or inserting that map gives inverse natural transformations. By
   lem-pc-yoneda these identify `D_j` with `E_j` over `T`.
5. Thus `V → T` restricts to `E_j → T` on its disjoint open summands. It is étale
   by lem-weil-pbc-etale-local-on-source, and surjective by joint surjectivity in
   step 3. Scheme tests in def-trf-algebraic-space give the asserted properties.
6. Restrict an open cover of `U` to each `U_j`, select finite subcovers using
   def-weil-pbc-quasi-compact-scheme, and combine them over finite `J`. This proves
   quasi-compactness and the atlas conclusion. Empty `J` forces empty `Z` and
   empty test schemes; gluing and the empty finite subcover still apply. No
   affineness of `Z` or `W_j` is used. -/
theorem finite_qc_atlas_assembly {S : Scheme.{u}} (Z : Over S) (A : AlgebraicSpace S)
    (a : A.obj.obj ⟶ yoneda.obj Z) {J : Type v} [Finite J]
    (W : J → Over S) (p : ∀ j : J, W j ⟶ Z)
    (hp : ∀ j : J, Etale (p j).left)
    (hcover : ∀ z : Z.left, ∃ (j : J) (w : (W j).left), (p j).left w = z)
    (U : J → Over S) (hU : ∀ j : J, CompactSpace (U j).left)
    (qj : ∀ j : J, yoneda.obj (U j) ⟶ Limits.pullback a (yoneda.map (p j)))
    (hqjEt : ∀ j : J, IsEtale (qj j)) (hqjSurj : ∀ j : J, IsSurjective (qj j)) :
    CompactSpace (∐ U).left ∧
      ∃ q : yoneda.obj (∐ U) ⟶ A.obj.obj,
        (∀ q' : yoneda.obj (∐ U) ⟶ A.obj.obj, (∀ j : J, yoneda.map (Sigma.ι U j) ≫ q' =
          qj j ≫ Limits.pullback.fst a (yoneda.map (p j))) ↔ q' = q) ∧
        IsRepresentable q ∧ IsSurjective q ∧ IsEtale q := by
  classical
  let h := sheafCoproduct (coproductIsCoproduct U)
  let c := Cofan.mk A.obj (fun j ↦
    (⟨qj j ≫ Limits.pullback.fst a (yoneda.map (p j))⟩ :
      (Scheme.fppfTopology.over S).yoneda.obj (U j) ⟶ A.obj))
  let q : yoneda.obj (∐ U) ⟶ A.obj.obj := (h.desc c).hom
  have hq (j : J) : yoneda.map (Sigma.ι U j) ≫ q =
      qj j ≫ Limits.pullback.fst a (yoneda.map (p j)) := by
    exact congrArg (fun f ↦ f.hom) (h.fac c ⟨j⟩)
  have hc : CompactSpace (∐ U).left := by
    let h' := underlyingColimit (coproductIsCoproduct U)
    have : Finite (coproductCover h').I₀ := by
      change Finite J
      infer_instance
    have (j : (coproductCover h').I₀) : CompactSpace ((coproductCover h').X j) := by
      change CompactSpace (U j).left
      exact hU j
    exact (coproductCover h').compactSpace
  refine ⟨hc, q, ?_, representable_etale_scheme_tests.1 A (∐ U) q, ?_, ?_⟩
  · intro q'
    constructor
    · intro hq'
      have hh : (⟨q'⟩ : (Scheme.fppfTopology.over S).yoneda.obj (∐ U) ⟶ A.obj) =
          h.desc c := by
        apply h.hom_ext
        intro j
        apply Sheaf.hom_ext
        exact (hq' j.as).trans (hq j.as).symm
      exact congrArg (fun f ↦ f.hom) hh
    · rintro rfl
      exact hq
  · intro T t
    obtain ⟨V, v, r, hV, hs, _⟩ := atlas_test Z A a W p hp hcover U qj
      hqjEt hqjSurj q hq T t
    exact ⟨V, v, r, hV, hs⟩
  · intro T t
    obtain ⟨V, v, r, hV, _, he⟩ := atlas_test Z A a W p hp hcover U qj
      hqjEt hqjSurj q hq T t
    exact ⟨V, v, r, hV, he⟩

end AlgebraicGeometry.AlgebraicSpace
