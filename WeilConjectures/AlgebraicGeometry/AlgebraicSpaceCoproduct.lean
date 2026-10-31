/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.FppfSheafCoproductPartition
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.FppfCoproductEqualityLocus
import WeilConjectures.AlgebraicGeometry.CoproductSchemePullback
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.AlgebraicGeometry.LimitsOver

/-!
# Coproducts of algebraic spaces

Source: Stacks Project, Spaces, Tag 02WQ (blueprint: lem-trf-algebraic-space-coproduct).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def underlyingColimit {S : Scheme.{u}} {I : Type u}
    {U : I → Over S} {T : Over S} {j : ∀ i, U i ⟶ T}
    (h : IsColimit (Cofan.mk T j)) :
    IsColimit (Cofan.mk T.left (fun i ↦ (j i).left)) :=
  (Cofan.isColimitMapCoconeEquiv (Over.forget S) U _).1
    (isColimitOfPreserves (Over.forget S) h)

private noncomputable def coproductIso {I : Type u} {U : I → Scheme.{u}}
    {T : Scheme.{u}} {j : ∀ i, U i ⟶ T} (h : IsColimit (Cofan.mk T j)) :
    (∐ U) ≅ T :=
  (coproductIsCoproduct U).coconePointUniqueUpToIso h

private lemma coproductIso_ι {I : Type u} {U : I → Scheme.{u}}
    {T : Scheme.{u}} {j : ∀ i, U i ⟶ T} (h : IsColimit (Cofan.mk T j)) (i : I) :
    Sigma.ι U i ≫ (coproductIso h).hom = j i := by
  exact (coproductIsCoproduct U).comp_coconePointUniqueUpToIso_hom h ⟨i⟩

private noncomputable def coproductCover {I : Type u} {U : I → Scheme.{u}}
    {T : Scheme.{u}} {j : ∀ i, U i ⟶ T} (h : IsColimit (Cofan.mk T j)) :
    T.OpenCover :=
  (sigmaOpenCover U).pushforwardIso (coproductIso h).hom

private lemma coproduct_open {I : Type u} {U : I → Scheme.{u}}
    {T : Scheme.{u}} {j : ∀ i, U i ⟶ T} (h : IsColimit (Cofan.mk T j)) (i : I) :
    IsOpenImmersion (j i) := by
  rw [← coproductIso_ι h i]
  infer_instance

private noncomputable def sheafCoproduct {S : Scheme.{u}} {I : Type u}
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

private lemma lifted_pullback {S : Scheme.{u}} {T V : Over S}
    {G H : (Over S)ᵒᵖ ⥤ Type u} {q : yoneda.obj V ⟶ G} {p : V ⟶ T}
    {f : G ⟶ H} {a : yoneda.obj T ⟶ H}
    (h : IsPullback q (yoneda.map p) f a) :
    IsPullback ((uliftYonedaIsoYoneda.{u, u, u + 1}.app V).hom ≫ q) (uliftYoneda.{u}.map p)
      f ((uliftYonedaIsoYoneda.{u, u, u + 1}.app T).hom ≫ a) := by
  apply h.of_iso' (uliftYonedaIsoYoneda.{u, u, u + 1}.app V) (Iso.refl _)
    (uliftYonedaIsoYoneda.{u, u, u + 1}.app T) (Iso.refl _)
  · simp
  · exact (uliftYonedaIsoYoneda.{u, u, u + 1}.hom.naturality p).symm
  · simp
  · simp

private lemma unlifted_pullback {S : Scheme.{u}} {T V : Over S}
    {G H : (Over S)ᵒᵖ ⥤ Type u} {q : yoneda.obj V ⟶ G} {p : V ⟶ T}
    {f : G ⟶ H} {a : yoneda.obj T ⟶ H}
    (h : IsPullback ((uliftYonedaIsoYoneda.{u, u, u + 1}.app V).hom ≫ q) (uliftYoneda.{u}.map p)
      f ((uliftYonedaIsoYoneda.{u, u, u + 1}.app T).hom ≫ a)) :
    IsPullback q (yoneda.map p) f a := by
  apply h.of_iso (uliftYonedaIsoYoneda.{u, u, u + 1}.app V) (Iso.refl _)
    (uliftYonedaIsoYoneda.{u, u, u + 1}.app T) (Iso.refl _)
  · simp
  · exact uliftYonedaIsoYoneda.{u, u, u + 1}.hom.naturality p
  · simp
  · simp

private lemma lifted_section {S : Scheme.{u}} {T : Over S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (a : G.obj (op T)) :
    (uliftYonedaIsoYoneda.{u, u, u + 1}.app T).hom ≫ yonedaEquiv.symm a =
      uliftYonedaEquiv.{u}.symm a := by
  ext Z x
  rfl

private lemma coproduct_diagonal {S : Scheme.{u}} {I : Type u}
    (F : I → AlgebraicSpace S) (C : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (c : ∀ i, (F i).obj ⟶ C) (hC : IsColimit (Cofan.mk C c)) :
    AlgebraicSpace.IsRepresentable (prod.lift (𝟙 C.obj) (𝟙 C.obj)) := by
  classical
  intro T a
  let sa := yonedaEquiv (a ≫ prod.fst)
  let sb := yonedaEquiv (a ≫ prod.snd)
  have ha : a = prod.lift (yonedaEquiv.symm sa) (yonedaEquiv.symm sb) := by
    apply prod.hom_ext <;> simp [sa, sb]
  obtain ⟨A, hA, _⟩ :=
    (Scheme.fppfSheaf_coproduct_partition (fun i ↦ (F i).obj)).2 C c hC |>.2.1 T sa
  obtain ⟨B, hB, _⟩ :=
    (Scheme.fppfSheaf_coproduct_partition (fun i ↦ (F i).obj)).2 C c hC |>.2.1 T sb
  let D (i : I) := Scheme.fppfPartitionOpen T (A.opens i ⊓ B.opens i)
  let ai (i : I) : (F i).obj.obj.obj (op (D i)) := (F i).obj.obj.map
    (Scheme.fppfEqualityOpenInclusion T inf_le_left).op (A.sections i)
  let bi (i : I) : (F i).obj.obj.obj (op (D i)) := (F i).obj.obj.map
    (Scheme.fppfEqualityOpenInclusion T inf_le_right).op (B.sections i)
  have hlocal (i : I) := (F i).property.1 (D i)
    (prod.lift (yonedaEquiv.symm (ai i)) (yonedaEquiv.symm (bi i)))
  choose E e z hz _ using hlocal
  have hze (i : I) : z i = yoneda.map (e i) ≫ yonedaEquiv.symm (ai i) := by
    simpa using (hz i).w =≫ prod.fst
  have hl (i : I) : IsPullback
      (uliftYonedaEquiv.{u}.symm ((F i).obj.obj.map (e i).op (ai i)))
      (uliftYoneda.{u}.map (e i)) (prod.lift (𝟙 (F i).obj.obj) (𝟙 (F i).obj.obj))
      (prod.lift (uliftYonedaEquiv.{u}.symm (ai i)) (uliftYonedaEquiv.{u}.symm (bi i))) := by
    have hh := lifted_pullback (hz i)
    rw [hze i] at hh
    convert hh using 1
    · rw [uliftYonedaEquiv_symm_map]
      rw [← lifted_section]
      simp only [← Category.assoc]
      rfl
    · apply prod.hom_ext
      · simpa only [Category.assoc, prod.lift_fst] using (lifted_section (ai i)).symm
      · simpa only [Category.assoc, prod.lift_snd] using (lifted_section (bi i)).symm
  let L := ∐ E
  let j := Sigma.ι E
  let hL := coproductIsCoproduct E
  let eL := Scheme.fppfEqualityCoproductProjection T
    (fun i ↦ A.opens i ⊓ B.opens i) E e L j hL
  have h := Scheme.fppfSheaf_coproduct_equality_locus (fun i ↦ (F i).obj)
    C c hC T sa sb A B hA hB E e hl L j hL
  refine ⟨L, eL, yonedaEquiv.symm (C.obj.map eL.op sa), ?_, trivial⟩
  rw [ha]
  apply unlifted_pullback
  convert h using 1
  · exact lifted_section _
  · apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using lifted_section sa
    · simpa only [Category.assoc, prod.lift_snd] using lifted_section sb

private lemma atlas_test {S : Scheme.{u}} {U T : Over S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (p : yoneda.obj U ⟶ G)
    (he : AlgebraicSpace.IsEtale p) (hs : AlgebraicSpace.IsSurjective p)
    (a : yoneda.obj T ⟶ G) :
    ∃ (V : Over S) (q : V ⟶ T) (r : V ⟶ U),
      IsPullback (yoneda.map r) (yoneda.map q) p a ∧ Etale q.left ∧ Surjective q.left := by
  obtain ⟨V, q, r, h, hq⟩ := he T a
  obtain ⟨W, q', r', h', hq'⟩ := hs T a
  let rV := yoneda.preimage r
  have hr : yoneda.map rV = r := yoneda.map_preimage r
  let e := Yoneda.fullyFaithful.preimageIso (h.isoIsPullback _ _ h')
  have heq : e.hom ≫ q' = q := by
    apply yoneda.map_injective
    simp [e]
  have : Surjective q'.left := hq'
  have : IsIso e.hom.left := inferInstance
  have hsurj : Surjective q.left := by
    rw [← heq, Over.comp_left]
    infer_instance
  exact ⟨V, q, rV, hr ▸ h, hq, hsurj⟩

private lemma atlas_pullback {S : Scheme.{u}} {I : Type u}
    (F : I → AlgebraicSpace S) (U : I → Over S)
    (p : ∀ i, yoneda.obj (U i) ⟶ (F i).obj.obj)
    (hp : ∀ i, AlgebraicSpace.IsEtale (p i) ∧ AlgebraicSpace.IsSurjective (p i))
    (Ucop : Over S) (ι : ∀ i, U i ⟶ Ucop)
    (hU : IsColimit (Cofan.mk Ucop ι))
    (C : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (c : ∀ i, (F i).obj ⟶ C) (hC : IsColimit (Cofan.mk C c))
    (aU : yoneda.obj Ucop ⟶ C.obj)
    (haU : ∀ i, yoneda.map (ι i) ≫ aU = p i ≫ (c i).hom)
    (T : Over S) (a : yoneda.obj T ⟶ C.obj) :
    ∃ (V : Over S) (q : V ⟶ T) (r : V ⟶ Ucop),
      IsPullback (yoneda.map r) (yoneda.map q) aU a ∧
        Etale q.left ∧ Surjective q.left := by
  classical
  let s := yonedaEquiv a
  obtain ⟨d, hd, _⟩ :=
    (Scheme.fppfSheaf_coproduct_partition (fun i ↦ (F i).obj)).2 C c hC |>.2.1 T s
  have hlocal (i : I) := atlas_test (p i) (hp i).1 (hp i).2
    (yonedaEquiv.symm (d.sections i))
  choose V q r hV hqe hqs using hlocal
  have hl (i : I) : IsPullback (uliftYoneda.{u}.map (q i))
      (uliftYoneda.{u}.map (r i)) (uliftYonedaEquiv.{u}.symm (d.sections i))
      ((uliftYonedaIsoYoneda.{u, u, u + 1}.app (U i)).hom ≫ p i) := by
    have hh := lifted_pullback (hV i)
    have hn := uliftYonedaIsoYoneda.{u, u, u + 1}.hom.naturality (r i)
    exact (hh.of_iso' (Iso.refl _) (uliftYonedaIsoYoneda.{u, u, u + 1}.app (U i))
      (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom]; exact hn.symm)
      (by simp) (by simp) (lifted_section _)).flip
  have hcomp (i : I) : uliftYoneda.{u}.map (ι i) ≫
      ((uliftYonedaIsoYoneda.{u, u, u + 1}.app Ucop).hom ≫ aU) =
      ((uliftYonedaIsoYoneda.{u, u, u + 1}.app (U i)).hom ≫ p i) ≫ (c i).hom := by
    have hn := uliftYonedaIsoYoneda.{u, u, u + 1}.hom.naturality (ι i)
    change uliftYoneda.{u}.map (ι i) ≫
      uliftYonedaIsoYoneda.{u, u, u + 1}.hom.app Ucop ≫ aU = _
    rw [← Category.assoc, hn]
    simp only [Category.assoc, haU]
    rfl
  obtain ⟨_, W, j, ⟨hW⟩, Q, R, hQ, _, h, _⟩ :=
    Scheme.fppfSheaf_coproduct_scheme_pullback (fun i ↦ (F i).obj) C c hC
      U Ucop ι (underlyingColimit hU)
      (fun i ↦ (uliftYonedaIsoYoneda.{u, u, u + 1}.app (U i)).hom ≫ p i)
      ((uliftYonedaIsoYoneda.{u, u, u + 1}.app Ucop).hom ≫ aU)
      hcomp T s d hd V q r hl
  have hQE : Etale Q.left := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Etale) (coproductCover hW)
    intro i
    have : Etale (q i).left := hqe i
    have eqi : (coproductCover hW).f i = (j i).left := coproductIso_ι hW i
    rw [eqi, ← Over.comp_left, hQ, Over.comp_left]
    change Etale ((q i).left ≫ (d.opens i).ι)
    infer_instance
  have hQS : Surjective Q.left := by
    constructor
    intro x
    have hx : x ∈ iSup d.opens := by rw [d.covers]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : Surjective (q i).left := hqs i
    obtain ⟨v, hv⟩ := (q i).left.surjective ⟨x, hi⟩
    refine ⟨(j i).left v, ?_⟩
    change ((j i).left ≫ Q.left) v = x
    rw [← Over.comp_left, hQ, Over.comp_left]
    change (d.opens i).ι ((q i).left v) = x
    rw [hv]
    rfl
  refine ⟨W, Q, R, ?_, hQE, hQS⟩
  apply h.flip.of_iso (uliftYonedaIsoYoneda.{u, u, u + 1}.app W)
    (uliftYonedaIsoYoneda.{u, u, u + 1}.app Ucop)
    (uliftYonedaIsoYoneda.{u, u, u + 1}.app T) (Iso.refl _)
  · exact uliftYonedaIsoYoneda.{u, u, u + 1}.hom.naturality R
  · exact uliftYonedaIsoYoneda.{u, u, u + 1}.hom.naturality Q
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id, s, Equiv.symm_apply_apply]
      using (lifted_section s).symm

/-- A set-indexed coproduct of algebraic spaces over a scheme is an algebraic space when
there is a scheme coproduct of the chosen surjective étale atlases.

Source: Stacks Project, Spaces, Tag 02WQ (blueprint: lem-trf-algebraic-space-coproduct).

Proof:
1. Apply lem-trf-fppf-sheaf-coproduct-partition to the underlying fppf sheaves of the
   `F i` (def-trf-algebraic-space). The coprojections `c i` are injective on sections.
   Every section `a ∈ C(T)` has a unique clopen partition `T = ∐ T_i(a)` with component
   sections `a_i ∈ F_i(T_i(a))`, and `h_{T_i(a)} ≅ h_T ×_C F_i`, compatibly with every
   scheme test. These partitions replace the generally false identity `C(T) = ∐ F_i(T)`.
2. Diagonal. For `a, b ∈ C(T)` put `T_ij = T_i(a) ∩ T_j(b)`. For `i = j` the scheme
   `E_i = h_{T_ii} ×_{F_i × F_i} F_i` exists by the representable diagonal of `F i`
   (def-trf-algebraic-space); let `E = ∐ E_i` (lem-weil-pbc-scheme-coproduct-family). On a
   test `Z → T`, equality `a|_Z = b|_Z` forces equal partitions by uniqueness in
   lem-trf-fppf-sheaf-coproduct-partition, so the `Z ×_T T_ij` with `i ≠ j` are empty and
   the `Z ×_T T_ii` cover `Z`. Injectivity of `c i` turns equality on each piece into a
   unique map to `E_i`; these glue to `Z → E` (lem-weil-pbc-scheme-morphism-gluing).
   Conversely a map `Z → E` gives equality on each summand, hence on `Z` by the sheaf
   condition (def-weil-pbc-sites-and-cohomology). So `E` represents `h_T ×_{C × C} C`.
3. Atlas. Let `U = ∐ U_i` be the given scheme coproduct; its summands form a disjoint
   clopen covering (lem-weil-pbc-scheme-coproduct-family). The sections `c_i(p_i)` agree
   on the empty overlaps (a sheaf has one section over the empty scheme,
   def-weil-pbc-sites-and-cohomology) and glue to `p : h_U → C` with `p|_{U_i} = c_i p_i`.
   The hypothesis that `U` is an object of the site makes it an allowed atlas.
4. Representability of `p`. For `a : h_T → C` with partition `T_i`, the scheme
   `V_i = h_{T_i} ×_{F_i} h_{U_i}` exists and `V_i → T_i` is surjective étale
   (def-trf-algebraic-space); put `V = ∐ V_i` (lem-weil-pbc-scheme-coproduct-family).
   A map `u : Z → U` with `p u = a|_Z` has `u⁻¹(U_i) = Z ×_T T_i` by uniqueness in
   lem-trf-fppf-sheaf-coproduct-partition; on each piece the datum is exactly a map to
   `V_i` since `c i` is injective, and the pieces glue uniquely to `Z → V`
   (lem-weil-pbc-scheme-morphism-gluing). Hence `h_V ≅ h_T ×_C h_U`.
5. Surjective étale. Each `t ∈ T` lies in a unique `T_i` and has a preimage in `V_i`.
   Étaleness of `V → T` holds by the affine-chart characterization of
   def-weil-etale-morphism, since `V_i ⊆ V` and `T_i ⊆ T` are open. Steps 1, 2 and 4 give
   the sheaf, diagonal and atlas conditions of def-trf-algebraic-space. For empty `I`
   every test `T → C` is empty and `U = V = ∅`; empty summands change nothing. -/
theorem algebraicSpace_coproduct
    {S : Scheme.{u}} (I : Type u) (F : I → AlgebraicSpace S) (U : I → Over S)
    (p : ∀ i, yoneda.obj (U i) ⟶ (F i).obj.obj)
    (hp : ∀ i, AlgebraicSpace.IsEtale (p i) ∧ AlgebraicSpace.IsSurjective (p i))
    (Ucoprod : Over S) (ι : ∀ i, U i ⟶ Ucoprod)
    (hU : Nonempty (IsColimit (Cofan.mk Ucoprod ι)))
    (C : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (c : ∀ i, (F i).obj ⟶ C)
    (hC : IsColimit (Cofan.mk C c)) : AlgebraicSpace.IsAlgebraicSpace C := by
  classical
  obtain ⟨hU⟩ := hU
  let h := sheafCoproduct hU
  let aU : yoneda.obj Ucoprod ⟶ C.obj :=
    (h.desc (Cofan.mk C (fun i ↦ ⟨p i ≫ (c i).hom⟩))).hom
  have haU (i : I) : yoneda.map (ι i) ≫ aU = p i ≫ (c i).hom := by
    exact congrArg (fun f ↦ f.hom) (h.fac (Cofan.mk C (fun i ↦ ⟨p i ≫ (c i).hom⟩)) ⟨i⟩)
  refine ⟨coproduct_diagonal F C c hC, Ucoprod, aU, ?_, ?_⟩
  · intro T a
    obtain ⟨V, q, r, hv, he, _⟩ :=
      atlas_pullback F U p hp Ucoprod ι hU C c hC aU haU T a
    exact ⟨V, q, yoneda.map r, hv, he⟩
  · intro T a
    obtain ⟨V, q, r, hv, _, hs⟩ :=
      atlas_pullback F U p hp Ucoprod ι hU C c hC aU haU T a
    exact ⟨V, q, yoneda.map r, hv, hs⟩

end AlgebraicGeometry
