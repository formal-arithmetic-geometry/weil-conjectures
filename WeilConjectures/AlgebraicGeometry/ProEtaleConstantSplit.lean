/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import all WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport

/-! # Split schemes from a constant represented sheaf on a pro-etale slice -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem arbitraryConstantComparison_isIso (U : Scheme.{u}) (E : Type u) :
    IsIso (proEtaleFiniteConstantComparison U E) := by
  let H := proEtaleFiniteConstantPresheaf U E
  let P := (Functor.const U.ProEtᵒᵖ).obj (ULift.{u + 1, u} E)
  let c := proEtaleFiniteConstantSections U E
  have hc : ∀ (W : U.ProEt) (e : E), ((c.app (Opposite.op W)) ⟨e⟩).down.left =
      W.hom ≫ Sigma.ι (fun _ : E ↦ U) e := fun _ _ ↦ rfl
  have hH : Presheaf.IsSheaf (ProEt.topology U) H :=
    ((ProEt.topology U).uliftYoneda.{u + 1}.obj
      (proEtaleFiniteConstantObject U E)).property
  have hinj : Presheaf.IsLocallyInjective (ProEt.topology U) c := by
    constructor
    intro W a b hab
    by_cases h : a = b
    · subst b
      exact (ProEt.topology U).superset_covering (fun _ _ _ ↦ rfl)
        ((ProEt.topology U).top_mem _)
    · have hne : a.down ≠ b.down := fun h' ↦ h (ULift.ext a b h')
      have heq : W.unop.hom ≫ Sigma.ι (fun _ : E ↦ U) a.down =
          W.unop.hom ≫ Sigma.ι (fun _ : E ↦ U) b.down :=
        congrArg (fun t ↦ t.down.left) hab
      have ha := (coproductCopiesMorphismsClopen U W.unop.left E W.unop.hom).2.2.2.2.1
      have htop : (⊤ : W.unop.left.Opens) = ⊥ := by
        have h₁ := ha a.down a.down
        have h₂ := ha b.down a.down
        rw [heq] at h₁
        simpa [hne] using h₁.symm.trans h₂
      have : IsEmpty W.unop.left := ⟨fun x ↦ by
        have hx : x ∈ (⊤ : W.unop.left.Opens) := trivial
        rw [htop] at hx
        exact hx⟩
      let j : ∀ i : PEmpty.{u + 1}, (i.elim : Scheme.{u}) ⟶ W.unop.left :=
        fun i ↦ i.elim
      let : ∀ i, IsOpenImmersion (j i) := fun i ↦ i.elim
      apply ProEt.mem_topology_of_openImmersion _ j
      · intro x
        exact isEmptyElim x
      · intro i
        exact i.elim
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology U) c := by
    constructor
    intro W s
    let f : W.left ⟶ ∐ fun _ : E ↦ U := s.down.left
    have hf : f ≫ Sigma.desc (fun _ : E ↦ 𝟙 U) = W.hom := s.down.w
    let V (e : E) := f ⁻¹ᵁ (Sigma.ι (fun _ : E ↦ U) e).opensRange
    have hdecomp := (coproductCopiesMorphismsClopen U W.left E W.hom).1 f hf
    let Z (e : E) : U.ProEt := ProEt.mk ((V e).ι ≫ W.hom)
    let j (e : E) : Z e ⟶ W := MorphismProperty.Over.homMk (V e).ι rfl
    apply ProEt.mem_topology_of_openImmersion _ (fun e ↦ (V e).ι)
    · intro x
      have hx : x ∈ (⨆ e, V e) := by rw [hdecomp.1.2]; trivial
      obtain ⟨e, he⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨e, ⟨⟨x, he⟩, rfl⟩⟩
    · intro e
      refine ⟨⟨e⟩, ?_⟩
      apply ULift.ext
      apply MorphismProperty.Over.Hom.ext
      exact (hdecomp.2 e).symm
  let φ : (constantSheaf (ProEt.topology U) (Type (u + 1))).obj
      (ULift.{u + 1, u} E) ⟶ ⟨H, hH⟩ :=
    ⟨sheafifyLift (ProEt.topology U) c hH⟩
  have hφ : toSheafify (ProEt.topology U) P ≫ φ.hom = c :=
    toSheafify_sheafifyLift (ProEt.topology U) c hH
  change IsIso φ
  apply (Sheaf.isLocallyBijective_iff_isIso φ).mp
  constructor
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _
      (toSheafify (ProEt.topology U) P), hφ]
    exact hinj
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _
      (toSheafify (ProEt.topology U) P), hφ]
    exact hsurj


private def collapseLift (T : Type u) :
    ULift.{u + 2} (ULift.{u + 1} T) ≃ ULift.{u + 2} T where
  toFun x := ⟨x.down.down⟩
  invFun x := ⟨⟨x.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def arbitraryConstantIso (Y : Scheme.{u}) (S : Type u) :
    (constantSheaf (ProEt.topology Y) (Type (u + 2))).obj (ULift.{u + 2} S) ≅
      (ProEt.topology Y).uliftYoneda.{u + 2}.obj (proEtaleFiniteConstantObject Y S) := by
  have := arbitraryConstantComparison_isIso Y S
  let J := ProEt.topology Y
  let B := proEtaleFiniteConstantObject Y S
  have : J.PreservesSheafification uliftFunctor.{u + 2, u + 1} :=
    AlgebraicGeometry.ProEtale.ulift_preservesSheafification J
  let e : (sheafCompose J uliftFunctor.{u + 2, u + 1}).obj
      ((constantSheaf J (Type (u + 1))).obj (ULift.{u + 1} S)) ≅
        (constantSheaf J (Type (u + 2))).obj (ULift.{u + 2} S) :=
    (constantCommuteCompose J uliftFunctor.{u + 2, u + 1}).app _ ≪≫
      (constantSheaf J (Type (u + 2))).mapIso
        (collapseLift S).toIso
  refine e.symm ≪≫ (sheafCompose J uliftFunctor.{u + 2, u + 1}).mapIso
    (asIso (proEtaleFiniteConstantComparison Y S)) ≪≫ ?_
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun U ↦ (collapseLift (U.unop ⟶ B)).toIso) ?_
  intro V W f
  rfl

private def pullbackRepresentableEquiv
    {X Y : Scheme.{u}} (p : Y ⟶ X) [WeaklyEtale p] (Z : X.Etale)
    (U : Y.ProEt) :
    ((ProEt.forget X).obj
      ((ProEt.sliceFrom X (ProEt.mk p)).obj U).left ⟶ (Etale.forget X).obj Z) ≃
      (U ⟶ ProEt.mk (pullback.snd Z.hom p)) where
  toFun a := MorphismProperty.Over.homMk
    (pullback.lift a.left U.hom a.w)
    (pullback.lift_snd _ _ _)
  invFun a := Over.homMk (a.left ≫ pullback.fst Z.hom p) (by
    change (a.left ≫ pullback.fst Z.hom p) ≫ Z.hom = U.hom ≫ p
    have ha : a.left ≫ pullback.snd Z.hom p = U.hom := a.w
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha])
  left_inv a := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  right_inv a := MorphismProperty.Over.Hom.ext (pullback.hom_ext
    (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans a.w.symm))

/-- If a represented sheaf is constant on a pro-etale slice, the representing
scheme after that base change is a coproduct of copies of the new base.

Source: Bhatt--Scholze, Section 6.8, the split lattice-class scheme;
the project constant-representable comparison.
(blueprint: lisse-qlbar-constant-representable-split)

Proof. Equivalence of the slice site and the new base's small pro-etale site
transports the supplied constant sheaf isomorphism. The pullback universal
property identifies the restriction of the represented sheaf with the sheaf
represented by the base-changed scheme. Arbitrary constant sheaves are
represented by coproducts of copies: maps into these coproducts are locally
constant labels, and the constant-section map is locally bijective. Yoneda
full faithfulness now identifies the two representing pro-etale objects.
Transport the coprojections through this isomorphism. They are sections of
the base-changed structure map and form a coproduct cocone. Empty label sets
are allowed, as are empty schemes. -/
theorem split_of_constant_representable_slice
    {X Y : Scheme.{u}} (p : Y ⟶ X) [WeaklyEtale p] (Z : X.Etale)
    (F : Sheaf (ProEt.topology X) (Type (u + 2)))
    (e : F.obj ≅ (ProEt.forget X).op ⋙
      yoneda.obj ((Etale.forget X).obj Z) ⋙ uliftFunctor.{u + 2})
    (S : Type u)
    (k : (constantSheaf ((ProEt.topology X).over (ProEt.mk p)) (Type (u + 2))).obj
      (ULift.{u + 2} S) ≅ F.over (ProEt.mk p)) :
    ∃ (ι : S → (Y ⟶ pullback Z.hom p)),
      (∀ i, ι i ≫ pullback.snd Z.hom p = 𝟙 Y) ∧
      Nonempty (IsColimit (Cofan.mk (pullback Z.hom p) ι)) := by
  let W := ProEt.mk p
  let H := (ProEt.sliceEquiv X W).inverse
  have : H.IsDenseSubsite (ProEt.topology Y) ((ProEt.topology X).over W) :=
    ProEt.sliceDense X W
  let A := H.sheafPushforwardContinuous (Type (u + 2))
    (ProEt.topology Y) ((ProEt.topology X).over W)
  let V : Y.ProEt := ProEt.mk (𝟙 Y)
  let hV : IsTerminal V := MorphismProperty.Over.mkIdTerminal _ _
  let hHV : IsTerminal (H.obj V) := hV.isTerminalObj H
  let ek : (constantSheaf (ProEt.topology Y) (Type (u + 2))).obj (ULift.{u + 2} S) ≅
      A.obj (F.over W) :=
    (equivCommuteConstant' (ProEt.topology Y) (Type (u + 2))
      ((ProEt.topology X).over W) H hV hHV).app _ ≪≫ A.mapIso k
  let Q : Y.ProEt := ProEt.mk (pullback.snd Z.hom p)
  let er : (A.obj (F.over W)).obj ≅
      ((ProEt.topology Y).uliftYoneda.{u + 2}.obj Q).obj := by
    refine Functor.isoWhiskerLeft H.op
      (Functor.isoWhiskerLeft (Over.forget W).op e) ≪≫ ?_
    refine NatIso.ofComponents (fun U ↦
      ((Equiv.ulift.trans (pullbackRepresentableEquiv p Z U.unop)).trans
        Equiv.ulift.symm).toIso) ?_
    intro U U' a
    ext b
    apply ULift.ext
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (a.unop.left ≫ b.down.left) U'.unop.hom _ =
      a.unop.left ≫ pullback.lift b.down.left U.unop.hom _
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
      exact a.unop.w.symm
  let er' : A.obj (F.over W) ≅ (ProEt.topology Y).uliftYoneda.{u + 2}.obj Q :=
    ObjectProperty.isoMk _ er
  let j : Q ≅ proEtaleFiniteConstantObject Y S :=
    (ProEt.topology Y).fullyFaithfulUliftYoneda.preimageIso
      (er'.symm ≪≫ ek.symm ≪≫ arbitraryConstantIso Y S)
  let ι (s : S) : Y ⟶ pullback Z.hom p := Sigma.ι (fun _ : S ↦ Y) s ≫ j.inv.left
  refine ⟨ι, ?_, ?_⟩
  · intro s
    change (Sigma.ι (fun _ : S ↦ Y) s ≫ j.inv.left) ≫ Q.hom = 𝟙 Y
    have hj : j.inv.left ≫ Q.hom = (proEtaleFiniteConstantObject Y S).hom := j.inv.w
    rw [Category.assoc, hj]
    exact Sigma.ι_desc _ _
  · have hι : Sigma.desc ι = j.inv.left := by
      apply Sigma.hom_ext
      intro s
      simp only [Sigma.ι_desc, ι]
    have : IsIso (Sigma.desc ι) := by
      rw [hι]
      exact Functor.map_isIso (ProEt.forget Y ⋙ Over.forget Y) j.inv
    apply (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk (pullback Z.hom p) ι)).mpr
    change IsIso (Sigma.desc ι)
    infer_instance

end AlgebraicGeometry.Scheme
