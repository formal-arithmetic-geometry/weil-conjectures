/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
import WeilConjectures.AlgebraicGeometry.OpenCoverRepresentableDiagonal
import WeilConjectures.AlgebraicGeometry.SmallOpenCoproductCover
import WeilConjectures.AlgebraicGeometry.OpenSheafCoproductBaseChange
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Gluing algebraic spaces along open subfunctors

Source: Stacks Project, Spaces, Tag 02WR (blueprint: lem-trf-algebraic-space-open-gluing).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem sheaf_mono_presheaf {S : Scheme.{u}}
    {G F : Sheaf (Scheme.fppfTopology.over S) (Type u)} (f : G ⟶ F) [Mono f] :
    Mono f.hom := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  intro x y h
  let J := Scheme.fppfTopology.over S
  let a : J.yoneda.obj T.unop ⟶ G := ⟨yonedaEquiv.symm x⟩
  let b : J.yoneda.obj T.unop ⟶ G := ⟨yonedaEquiv.symm y⟩
  have hab : a ≫ f = b ≫ f := by
    apply Sheaf.hom_ext
    apply yonedaEquiv.injective
    change yonedaEquiv (yonedaEquiv.symm x ≫ f.hom) =
      yonedaEquiv (yonedaEquiv.symm y ≫ f.hom)
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  have hab' := congrArg (fun c ↦ c.hom.app T (𝟙 T.unop)) ((cancel_mono f).mp hab)
  change G.obj.map (𝟙 T.unop).op x = G.obj.map (𝟙 T.unop).op y at hab'
  simpa using hab'

private theorem representable_iff_relative {S : Scheme.{u}}
    {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
    AlgebraicSpace.IsRepresentable f ↔ yoneda.relativelyRepresentable f := by
  constructor
  · intro h T a
    obtain ⟨U, p, b, hb, _⟩ := h T a
    exact ⟨U, p, b, hb⟩
  · intro h T a
    obtain ⟨U, p, b, hb⟩ := h a
    exact ⟨U, p, b, hb, trivial⟩

private theorem diagonal_of_small_open_cover {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) (I : Type u)
    (Fi : I → Sheaf (Scheme.fppfTopology.over S) (Type u))
    (ι : ∀ i, Fi i ⟶ F) (hmono : ∀ i, Mono (ι i))
    (hdiag : ∀ i,
      AlgebraicSpace.IsRepresentable (prod.lift (𝟙 (Fi i).obj) (𝟙 (Fi i).obj)))
    (hopen : ∀ i, AlgebraicSpace.IsRepresentableWith
      (fun _ _ p ↦ IsOpenImmersion p.left) (ι i).hom)
    (hlocal : ∀ (T : Over S) (a : F.obj.obj (op T)),
      ∃ (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left) (k : 𝒰.I₀ → I),
        ∀ j : 𝒰.I₀,
          F.obj.map (Over.homMk (𝒰.f j) rfl : Over.mk (𝒰.f j ≫ T.hom) ⟶ T).op a ∈
            Set.range ((ι (k j)).hom.app (op (Over.mk (𝒰.f j ≫ T.hom))))) :
    AlgebraicSpace.IsRepresentable (prod.lift (𝟙 F.obj) (𝟙 F.obj)) := by
  have (i : I) : Mono (ι i) := hmono i
  have (i : I) : Mono (ι i).hom := sheaf_mono_presheaf (ι i)
  let R (i : I) : Subfunctor F.obj := Subfunctor.range (ι i).hom
  let e (i : I) : (Fi i).obj ≅ (R i).toFunctor := asIso (Subfunctor.toRange (ι i).hom)
  have he (i : I) : (e i).hom ≫ (R i).ι = (ι i).hom := Subfunctor.toRange_ι _
  apply (AlgebraicSpace.open_cover_representable_diagonal F I R ?_ ?_ ?_ hlocal).2.2
  · intro i
    exact (Presheaf.isSheaf_of_iso_iff (J := Scheme.fppfTopology.over S) (e i)).mp
      (Fi i).property
  · intro i T a
    obtain ⟨U, p, b, hb, hp⟩ := hopen i T a
    refine ⟨U, p, b ≫ (e i).hom, ?_, hp⟩
    exact hb.of_iso (Iso.refl _) (e i) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simpa using (he i).symm) (by simp)
  · intro i T T' a b
    have ha := Functor.relativelyRepresentable.of_diag
      ((representable_iff_relative _).mp (hdiag i)) (a ≫ (e i).inv)
    obtain ⟨U, p, c, hc⟩ := ha (b ≫ (e i).inv)
    have hd : IsPullback c (yoneda.map p) a b :=
      hc.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (e i)
        (by simp) (by simp) (by simp) (by simp)
    exact isRepresentable_of_natIso _ hd.isoPullback

private theorem representableWith_lift {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F)
    (hf : AlgebraicSpace.IsRepresentableWith P f) :
    AlgebraicSpace.IsRepresentableWithLift.{u, 0} P f := by
  let e := uliftYonedaIsoYoneda.{0, u} (C := Over S)
  intro T a
  obtain ⟨U, p, b, hb, hp⟩ := hf T ((e.app T).inv ≫ a)
  refine ⟨U, p, (e.app U).hom ≫ b, ?_, hp⟩
  exact hb.of_iso (e.app U).symm (Iso.refl _) (e.app T).symm (Iso.refl _)
    (by simp) (by simp [e]) (by simp) (by simp)

private theorem open_coproduct_test_exists {S : Scheme.{u}} {I : Type u}
    {F : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (Fi : I → Sheaf (Scheme.fppfTopology.over S) (Type u))
    (ι : ∀ i, Fi i ⟶ F)
    (hopen : ∀ i, AlgebraicSpace.IsRepresentableWithLift.{u, 0}
      (fun _ _ p ↦ IsOpenImmersion p.left) (ι i).hom)
    (T : Over S) (a : uliftYoneda.{0}.obj T ⟶ F.obj) :
    Nonempty (Scheme.OpenSheafCoproductTest Fi ι T a) := by
  classical
  choose V inclusion sectionMap cartesian isOpen using fun i ↦ hopen i T a
  let C : Over S := Over.mk (Sigma.desc (fun i ↦ (V i).hom))
  let injection (i : I) : V i ⟶ C := Over.homMk (Sigma.ι (fun i ↦ (V i).left) i)
    (by simp [C])
  let p : C ⟶ T := Over.homMk (Sigma.desc (fun i ↦ (inclusion i).left)) (by
    apply Sigma.hom_ext
    intro i
    simp [C, Over.w (inclusion i)])
  exact ⟨{
    V := V
    inclusion := inclusion
    sectionMap := sectionMap
    cartesian := cartesian
    isOpen := isOpen
    C := C
    injection := injection
    isColimit := coproductIsCoproduct _
    p := p
    injection_p := fun i ↦ by ext; simp [injection, p]
  }⟩

private theorem open_coproduct_test_etale {S : Scheme.{u}} {I : Type u}
    {F : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {Fi : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {ι : ∀ i, Fi i ⟶ F} {T : Over S} {a : uliftYoneda.{0}.obj T ⟶ F.obj}
    (D : Scheme.OpenSheafCoproductTest Fi ι T a) : Etale D.p.left := by
  let V : I → Scheme.{u} := fun i ↦ (D.V i).left
  let e : (∐ V) ≅ D.C.left :=
    (coproductIsCoproduct V).coconePointUniqueUpToIso D.isColimit
  have he (i : I) : Sigma.ι V i ≫ e.hom = (D.injection i).left :=
    (coproductIsCoproduct V).comp_coconePointUniqueUpToIso_hom D.isColimit ⟨i⟩
  have hf : Etale (e.hom ≫ D.p.left) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Etale) (sigmaOpenCover V)
    intro i
    have hi : Sigma.ι V i ≫ (e.hom ≫ D.p.left) = (D.inclusion i).left := by
      rw [← Category.assoc, he]
      exact congrArg Over.Hom.left (D.injection_p i)
    rw [show (sigmaOpenCover V).f i = Sigma.ι V i from rfl, hi]
    have := D.isOpen i
    infer_instance
  have := hf
  have : Etale (e.inv ≫ (e.hom ≫ D.p.left)) := inferInstance
  simpa using this

private theorem open_coproduct_test_surjective {S : Scheme.{u}} {I : Type u}
    {F : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {Fi : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {ι : ∀ i, Fi i ⟶ F}
    (hlocal : ∀ (T : Over S) (a : F.obj.obj (op T)),
      ∃ (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left) (k : 𝒰.I₀ → I),
        ∀ j : 𝒰.I₀,
          F.obj.map (Over.homMk (𝒰.f j) rfl : Over.mk (𝒰.f j ≫ T.hom) ⟶ T).op a ∈
            Set.range ((ι (k j)).hom.app (op (Over.mk (𝒰.f j ≫ T.hom)))))
    {T : Over S} {a : uliftYoneda.{0}.obj T ⟶ F.obj}
    (D : Scheme.OpenSheafCoproductTest Fi ι T a) : Surjective D.p.left := by
  classical
  obtain ⟨𝒰, k, h𝒰⟩ := hlocal T (uliftYonedaEquiv a)
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage :=
    inferInstanceAs (Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  constructor
  intro x
  obtain ⟨r, y, hy⟩ := 𝒰.exists_eq x
  obtain ⟨s, hs⟩ := h𝒰 r
  let f : Over.mk (𝒰.f r ≫ T.hom) ⟶ T := Over.homMk (𝒰.f r) rfl
  have hsec : uliftYonedaEquiv.symm s ≫ (ι (k r)).hom = uliftYoneda.map f ≫ a := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hs.trans (uliftYonedaEquiv_naturality a f.op)
  let l := (D.cartesian (k r)).lift (uliftYonedaEquiv.symm s) (uliftYoneda.map f) hsec
  let g : Over.mk (𝒰.f r ≫ T.hom) ⟶ D.V (k r) := uliftYoneda.preimage l
  have hg : g ≫ D.inclusion (k r) = f := by
    apply uliftYoneda.map_injective
    rw [Functor.map_comp, show uliftYoneda.map g = l from uliftYoneda.map_preimage l]
    exact (D.cartesian (k r)).lift_snd _ _ hsec
  refine ⟨(D.injection (k r)).left (g.left y), ?_⟩
  have hh := congrArg (fun z ↦ z.left) ((Category.assoc g (D.injection (k r)) D.p).trans
    ((congrArg (fun z ↦ g ≫ z) (D.injection_p (k r))).trans hg))
  simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
    (congrArg (fun z : (Over.mk (𝒰.f r ≫ T.hom)).left ⟶ T.left ↦ z y) hh).trans hy

private theorem representable_surjective_comp {S : Scheme.{u}}
    {G H K : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ H) (g : H ⟶ K)
    (hf : AlgebraicSpace.IsSurjective f) (hg : AlgebraicSpace.IsSurjective g) :
    AlgebraicSpace.IsSurjective (f ≫ g) := by
  intro T a
  obtain ⟨V, p, b, hV, hp⟩ := hg T a
  obtain ⟨W, r, c, hW, hr⟩ := hf V b
  have := hp
  have := hr
  refine ⟨W, r ≫ p, c, ?_, ?_⟩
  · simpa only [Functor.map_comp] using hW.paste_vert hV
  · change Surjective (r.left ≫ p.left)
    infer_instance

private theorem algebraicSpace_of_representable_cover {S : Scheme.{u}}
    {H F : Sheaf (Scheme.fppfTopology.over S) (Type u)} (q : H ⟶ F)
    (hdiag : AlgebraicSpace.IsRepresentable (prod.lift (𝟙 F.obj) (𝟙 F.obj)))
    (het : AlgebraicSpace.IsEtale q.hom) (hsur : AlgebraicSpace.IsSurjective q.hom)
    (hH : AlgebraicSpace.IsAlgebraicSpace H) :
    AlgebraicSpace.IsAlgebraicSpace F := by
  obtain ⟨U, a, ha, hsa⟩ := hH.2
  exact ⟨hdiag, U, a ≫ q.hom, AlgebraicSpace.isEtale_comp a q.hom ha het,
    representable_surjective_comp a q.hom hsa hsur⟩

/-- A sheaf covered by algebraic-space open subfunctors is an algebraic space.

Source: Stacks Project, Spaces, Tag 02WR, lemma-glueing-algebraic-spaces
(blueprint: lem-trf-algebraic-space-open-gluing).

Proof: representable maps are sheaves for the fppf topology by affine refinement and
fpqc representable descent.  The sheaf coproduct of the open algebraic subspaces is
locally represented by one summand, so its pullback to every scheme test is represented
by the coproduct of the corresponding open subschemes and is surjective.  Pullbacks of
two scheme tests are covered by representable open pieces coming from the summands;
the scheme representability criterion gives representability of the diagonal.  The
coproduct map is therefore representable, étale, and surjective.  Composing it with
a representable surjective étale atlas of the algebraic-space coproduct gives such an
atlas for the target sheaf, proving the conclusion by the definition of algebraic space.
The proof uses the statement dependencies `def-pc-scheme`, `def-pc-fppf-site`,
`def-weil-pbc-sheafification`, `def-trf-algebraic-space`, `def-pc-subfunctor`, and
`def-weil-open-immersion`; its proof dependencies are recorded in the DAG node. -/
theorem algebraicSpace_of_open_gluing {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) (I : Type w)
    (Fi : I → Sheaf (Scheme.fppfTopology.over S) (Type u))
    (H : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (j : ∀ i : I, (Fi i) ⟶ H)
    (hcol : IsColimit (Cofan.mk H j))
    (ι : ∀ i : I, (Fi i) ⟶ F)
    (q : H ⟶ F)
    (hfac : ∀ i : I, j i ≫ q = ι i)
    (hmono : ∀ i : I, Mono (ι i))
    (hFi : ∀ i : I, AlgebraicSpace.IsAlgebraicSpace (Fi i))
    (hopen : ∀ i : I,
      AlgebraicSpace.IsRepresentableWith
        (fun _ _ p ↦ IsOpenImmersion p.left) (ι i).hom)
    (hq : Epi q)
    (hcop : AlgebraicSpace.IsAlgebraicSpace H) :
    AlgebraicSpace.IsAlgebraicSpace F := by
  obtain ⟨J, k, hcol', hlocal⟩ :=
    small_open_coproduct_cover F I Fi H j hcol ι q hfac hmono hopen hq hcop
  have hdiag : AlgebraicSpace.IsRepresentable (prod.lift (𝟙 F.obj) (𝟙 F.obj)) :=
    diagonal_of_small_open_cover F J (fun r ↦ Fi (k r)) (fun r ↦ ι (k r))
      (fun r ↦ hmono (k r)) (fun r ↦ (hFi (k r)).1) (fun r ↦ hopen (k r)) hlocal
  classical
  let F' : J → Sheaf (Scheme.fppfTopology.over S) (Type u) := fun r ↦ Fi (k r)
  let ι' : ∀ r, F' r ⟶ F := fun r ↦ ι (k r)
  have hopen' (r : J) : AlgebraicSpace.IsRepresentableWithLift.{u, 0}
      (fun _ _ p ↦ IsOpenImmersion p.left) (ι' r).hom :=
    representableWith_lift _ _ (hopen (k r))
  have hsite := open_coproduct_test_exists F' ι' hopen'
  have hbc := Scheme.openSheafCoproduct_baseChange F F' ι' (fun r ↦ hmono (k r))
    hopen' H (fun r ↦ j (k r)) hcol'.some q (fun r ↦ hfac (k r)) hsite
  have htest (T : Over S) (a : yoneda.obj T ⟶ F.obj) :
      ∃ (C : Over S) (p : C ⟶ T) (b : yoneda.obj C ⟶ H.obj),
        IsPullback b (yoneda.map p) q.hom a ∧ Etale p.left ∧ Surjective p.left := by
    let e := uliftYonedaIsoYoneda.{0, u} (C := Over S)
    let a' : uliftYoneda.{0}.obj T ⟶ F.obj := (e.app T).hom ≫ a
    let D := (hsite T a').some
    obtain ⟨c, hc, _⟩ := hbc.2.2 T a' D
    let b' := c.hom ≫ pullback.fst q.hom a'
    have hpull : IsPullback b' (uliftYoneda.map D.p) q.hom a' :=
      IsPullback.of_iso_pullback ⟨by
        rw [← hc.1.2]
        simp [b', Category.assoc, pullback.condition]⟩ c rfl hc.1.2
    refine ⟨D.C, D.p, (e.app D.C).inv ≫ b', ?_, open_coproduct_test_etale D,
      open_coproduct_test_surjective hlocal D⟩
    exact hpull.of_iso (e.app D.C) (Iso.refl _) (e.app T) (Iso.refl _)
      (by simp) (by simp [e]) (by simp) (by simp [a'])
  apply algebraicSpace_of_representable_cover q hdiag ?_ ?_ hcop
  · intro T a
    obtain ⟨C, p, b, hb, he, _⟩ := htest T a
    exact ⟨C, p, b, hb, he⟩
  · intro T a
    obtain ⟨C, p, b, hb, _, hs⟩ := htest T a
    exact ⟨C, p, b, hb, hs⟩

end AlgebraicGeometry
