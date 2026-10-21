/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Subterminal
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Sheaf.CategoryTheory.Sites.ClosedComplementSiteConstruction
import Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation

/-!
# Open and closed complements of a subterminal object

Source: Stacks Project, Sites, Tags 08LW, 08LY, 08LZ and 08M0
(blueprint: lem-trf-topos-complement-factorization).

Full faithfulness on geometric-morphism categories is expressed as bijectivity of right
whiskering on all direct-image natural transformations. The essential image is expressed by
existence of a factor and a direct-image natural isomorphism. Together these are exactly an
equivalence onto the indicated full subcategory, including unique compatible isomorphisms.
-/

@[expose] public section

universe w u v uH vH

namespace CategoryTheory

open Limits

/-- The objects of the complementary closed subtopos: the projection `u × A → u` is an
isomorphism. The symmetry of binary products identifies this with `A × u → u`.
Source: Stacks Project, Sites, Tag 08LY
(blueprint: lem-trf-topos-complement-factorization). -/
def closedComplementObjects {E : Type u} [Category.{v} E] [HasBinaryProducts E]
    (u : E) : ObjectProperty E :=
  fun A ↦ IsIso (prod.fst : u ⨯ A ⟶ u)

private theorem topos_finiteLimits {T : Type u} [Category.{v} T]
    (hT : IsGrothendieckTopos.{w} T) : HasFiniteLimits T := by
  obtain ⟨D, c, J, ⟨e⟩⟩ := hT
  exact { out := fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor }

private theorem topos_initialProduct {T : Type u} [Category.{v} T]
    (hT : IsGrothendieckTopos.{w} T) [HasBinaryProducts T]
    {Z : T} (hZ : IsInitial Z) (B : T) : Nonempty (IsInitial (Z ⨯ B)) := by
  obtain ⟨D, c, J, ⟨e⟩⟩ := hT
  -- Products preserve initial objects in the Cartesian closed presenting sheaf category.
  let h := (hZ.isInitialObj e.functor Z).isInitialObj
    (prod.functor.obj (e.functor.obj B)) (e.functor.obj Z)
  exact ⟨(h.ofIso ((prod.braiding _ _) ≪≫
    (PreservesLimitPair.iso e.functor Z B).symm)).isInitialOfObj e.functor _⟩

private def subterminalForgetFF {T : Type u} [Category.{v} T]
    (U : T) (hU : IsSubterminal U) : (Over.forget U).FullyFaithful where
  preimage f := Over.homMk f (hU _ _)
  map_preimage _ := rfl
  preimage_map _ := by ext; rfl

private theorem open_directFF {T : Type u} [Category.{v} T] [HasBinaryProducts T]
    (U : T) (hU : IsSubterminal U) (j : GeometricMorphism (Over U) T)
    (e : j.inverse ≅ Over.star U) : Nonempty j.direct.FullyFaithful := by
  -- The fully faithful forgetful functor is the other outer adjoint of this triple.
  let t : Adjunction.Triple (Over.forget U) j.inverse j.direct :=
    ⟨(Over.forgetAdjStar U).ofNatIsoRight e.symm, j.adj⟩
  exact ⟨t.fullyFaithfulEquiv (subterminalForgetFF U hU)⟩

private noncomputable def star_subterminal_terminal {T : Type u} [Category.{v} T]
    [HasBinaryProducts T] (U : T) (hU : IsSubterminal U) :
    IsTerminal ((Over.star U).obj U) := by
  let i : U ⨯ U ≅ U := hU.isoDiag
  exact Over.mkIdTerminal.ofIso (Over.isoMk i (by apply hU)).symm

private noncomputable def open_factor {T : Type u} [Category.{v} T]
    {H : Type uH} [Category.{vH} H] [HasFiniteLimits T]
    (U : T) (a : GeometricMorphism H T) (h : IsTerminal (a.inverse.obj U)) :
    GeometricMorphism H (Over U) := by
  -- Compose the existing slice adjunction; left exactness reduces to terminal and pullbacks.
  let F := Over.forget U ⋙ a.inverse
  letI := a.leftExact
  haveI : PreservesLimitsOfShape WalkingCospan F := inferInstance
  have ht : IsTerminal (F.obj (Over.mk (𝟙 U))) := h
  haveI : PreservesLimit (Functor.empty.{0} (Over U)) F :=
    preservesLimit_of_preserves_limit_cone Over.mkIdTerminal
      ((isLimitMapConeEmptyConeEquiv F _).symm ht)
  haveI := preservesLimitsOfShape_pempty_of_preservesTerminal F
  exact ⟨F, a.direct ⋙ Over.star U, (Over.forgetAdjStar U).comp a.adj,
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks F⟩

private noncomputable def open_factor_comparison {T : Type u} [Category.{v} T]
    {H : Type uH} [Category.{vH} H] [HasFiniteLimits T]
    (U : T) (a : GeometricMorphism H T) (h : IsTerminal (a.inverse.obj U))
    (j : GeometricMorphism (Over U) T) (e : j.inverse ≅ Over.star U) :
    ((open_factor U a h).comp j).direct ≅ a.direct := by
  letI := a.leftExact
  let n : Over.star U ⋙ Over.forget U ⋙ a.inverse ⟶ a.inverse :=
    { app := fun B ↦ a.inverse.map prod.snd
      naturality := fun B C f ↦ by
        change a.inverse.map (prod.map (𝟙 U) f) ≫ a.inverse.map prod.snd =
          a.inverse.map prod.snd ≫ a.inverse.map f
        simp only [← Functor.map_comp, prod.map_snd] }
  haveI : ∀ B, IsIso (n.app B) := fun B ↦ by
    exact (BinaryFan.isLimit_iff_isIso_snd h
      (BinaryFan.mk (a.inverse.map (prod.fst : U ⨯ B ⟶ U))
        (a.inverse.map prod.snd))).mp
      ⟨mapIsLimitOfPreservesOfIsLimit a.inverse _ _ (prodIsProd U B)⟩
  haveI : IsIso n := NatIso.isIso_of_isIso_app n
  let q : ((open_factor U a h).comp j).inverse ≅ a.inverse :=
    Functor.isoWhiskerRight e ((open_factor U a h).inverse) ≪≫ asIso n
  exact conjugateIsoEquiv ((open_factor U a h).comp j).adj a.adj q.symm

private theorem open_universal {T : Type u} [Category.{v} T]
    {H : Type uH} [Category.{vH} H] [HasFiniteLimits T]
    (U : T) (hU : IsSubterminal U) (j : GeometricMorphism (Over U) T)
    (e : j.inverse ≅ Over.star U) (a : GeometricMorphism H T) :
    (∃ b : GeometricMorphism H (Over U), Nonempty ((b.comp j).direct ≅ a.direct)) ↔
      Nonempty (IsTerminal (a.inverse.obj U)) := by
  constructor
  · rintro ⟨b, ⟨q⟩⟩
    have := b.leftExact
    let t := (star_subterminal_terminal U hU).ofIso (e.app U).symm
    exact ⟨(t.isTerminalObj b.inverse _).ofIso
      ((GeometricMorphism.inverseIso q).app U).symm⟩
  · rintro ⟨h⟩
    exact ⟨open_factor U a h, ⟨open_factor_comparison U a h j e⟩⟩

private noncomputable def closed_unit_initial {T : Type u} [Category.{v} T]
    [HasBinaryProducts T] (U : T)
    (k : GeometricMorphism (closedComplementObjects U).FullSubcategory T)
    (e : k.direct ≅ (closedComplementObjects U).ι) : IsInitial (k.inverse.obj U) := by
  let P := closedComplementObjects U
  let adj := k.adj.ofNatIsoRight e
  let f : ∀ C : P.FullSubcategory, U ⟶ C.obj := fun C ↦ by
    have : IsIso (prod.fst : U ⨯ C.obj ⟶ U) := C.property
    exact inv (prod.fst : U ⨯ C.obj ⟶ U) ≫ prod.snd
  have uniq : ∀ (C : P.FullSubcategory) (g : U ⟶ C.obj), g = f C := by
    intro C g
    have : IsIso (prod.fst : U ⨯ C.obj ⟶ U) := C.property
    have eq : prod.lift (𝟙 U) g = inv (prod.fst : U ⨯ C.obj ⟶ U) := by
      apply (cancel_mono (prod.fst : U ⨯ C.obj ⟶ U)).mp
      simp
    simpa [f] using congrArg (fun t ↦ t ≫ prod.snd) eq
  exact IsInitial.ofUniqueHom (fun C ↦ (adj.homEquiv U C).symm (f C))
    (by
      intro C g
      apply (adj.homEquiv U C).injective
      rw [Equiv.apply_symm_apply]
      exact uniq C _)

private theorem closed_direct_lands {T : Type u} [Category.{v} T]
    {H : Type uH} [Category.{vH} H] [HasBinaryProducts T]
    (hH : IsGrothendieckTopos.{w} H) (U : T)
    (a : GeometricMorphism H T) (h : IsInitial (a.inverse.obj U)) (B : H) :
    closedComplementObjects U (a.direct.obj B) := by
  let := topos_finiteLimits hH
  let := a.leftExact
  let t : U ⟶ a.direct.obj B := (a.adj.homEquiv U B) (h.to B)
  let g : U ⟶ U ⨯ a.direct.obj B := prod.lift (𝟙 U) t
  have hz : Nonempty (IsInitial (a.inverse.obj (U ⨯ a.direct.obj B))) := by
    obtain ⟨hz⟩ := topos_initialProduct hH h (a.inverse.obj (a.direct.obj B))
    exact ⟨hz.ofIso (PreservesLimitPair.iso a.inverse U (a.direct.obj B)).symm⟩
  let z := hz.some
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply prod.hom_ext
    · simp [g]
    · apply (a.adj.homEquiv _ B).symm.injective
      exact z.hom_ext _ _
  · simp [g]

private noncomputable def closed_factor {T : Type u} [Category.{v} T]
    {H : Type uH} [Category.{vH} H] [HasBinaryProducts T]
    (hH : IsGrothendieckTopos.{w} H) (U : T)
    (a : GeometricMorphism H T) (h : IsInitial (a.inverse.obj U))
    (k : GeometricMorphism (closedComplementObjects U).FullSubcategory T)
    (e : k.direct ≅ (closedComplementObjects U).ι) :
    GeometricMorphism H (closedComplementObjects U).FullSubcategory := by
  let P := closedComplementObjects U
  -- Restriction keeps the original Hom bijection and hence its naturality.
  let R := P.lift a.direct (closed_direct_lands hH U a h)
  let L := P.ι ⋙ a.inverse
  haveI := a.leftExact
  haveI : PreservesLimitsOfSize.{0, 0} P.ι :=
    (k.adj.ofNatIsoRight e).rightAdjoint_preservesLimits
  exact ⟨L, R, a.adj.restrictFullyFaithful P.fullyFaithfulι
    (Functor.FullyFaithful.id H) (Iso.refl _) (Iso.refl _),
    comp_preservesFiniteLimits _ _⟩

private theorem closed_universal {T : Type u} [Category.{v} T]
    {H : Type uH} [Category.{vH} H] [HasBinaryProducts T]
    (hH : IsGrothendieckTopos.{w} H) (U : T)
    (k : GeometricMorphism (closedComplementObjects U).FullSubcategory T)
    (e : k.direct ≅ (closedComplementObjects U).ι) (a : GeometricMorphism H T) :
    (∃ b : GeometricMorphism H (closedComplementObjects U).FullSubcategory,
      Nonempty ((b.comp k).direct ≅ a.direct)) ↔
      Nonempty (IsInitial (a.inverse.obj U)) := by
  constructor
  · rintro ⟨b, ⟨q⟩⟩
    have := b.adj.leftAdjoint_preservesColimits
    exact ⟨((closed_unit_initial U k e).isInitialObj b.inverse _).ofIso
      ((GeometricMorphism.inverseIso q).app U).symm⟩
  · rintro ⟨h⟩
    let b := closed_factor hH U a h k e
    exact ⟨b, ⟨Functor.isoWhiskerLeft b.direct e⟩⟩

private theorem closed_product_transport {T : Type u} [Category.{v} T]
    {D : Type uH} [Category.{vH} D] [HasBinaryProducts T] [HasBinaryProducts D]
    (F : T ⥤ D) [F.ReflectsIsomorphisms] [PreservesFiniteLimits F]
    (U V : T) (U' V' : D) (i : F.obj U ≅ U') (j : F.obj V ≅ V') :
    closedComplementObjects U V ↔ closedComplementObjects U' V' := by
  let p := PreservesLimitPair.iso F U V ≪≫ prod.mapIso i j
  have comm : p.hom ≫ prod.fst = F.map (prod.fst : U ⨯ V ⟶ U) ≫ i.hom := by
    simp [p]
  change IsIso (prod.fst : U ⨯ V ⟶ U) ↔ IsIso (prod.fst : U' ⨯ V' ⟶ U')
  rw [← isIso_iff_of_reflects_iso _ F,
    ← isIso_comp_right_iff _ i.hom, ← comm, isIso_comp_left_iff]

private theorem subterminal_transport {T : Type u} [Category.{v} T]
    {D : Type uH} [Category.{vH} D] (e : T ≌ D)
    (U : T) (V : D) (i : e.functor.obj U ≅ V) (hU : IsSubterminal U) :
    IsSubterminal V := by
  intro X f g
  apply e.inverse.map_injective
  apply (cancel_mono (e.inverse.map i.inv ≫ (e.unitIso.app U).inv)).mp
  exact hU _ _

private theorem image_subtopos {T : Type u} [Category.{v} T]
    {D : Type uH} [Category.{vH} D]
    (hD : IsGrothendieckTopos.{w} D) (q : GeometricMorphism D T)
    (hq : q.direct.FullyFaithful) (P : ObjectProperty T)
    (hp : ∀ A, q.direct.essImage A ↔ P A) :
    IsGrothendieckTopos.{w} P.FullSubcategory ∧
      ∃ k : GeometricMorphism P.FullSubcategory T,
        Nonempty (k.direct ≅ P.ι) ∧ Nonempty k.direct.FullyFaithful := by
  let := hq.full
  let := hq.faithful
  let F := P.lift q.direct (fun A ↦ (hp _).mp (q.direct.obj_mem_essImage A))
  have : F.EssSurj := ⟨fun A ↦ by
    obtain ⟨B, ⟨i⟩⟩ := (hp A.obj).mpr A.property
    exact ⟨B, ⟨P.isoMk i⟩⟩⟩
  have : F.IsEquivalence := { }
  let r := F.asEquivalence
  have hP : IsGrothendieckTopos.{w} P.FullSubcategory := by
    obtain ⟨C, c, J, ⟨b⟩⟩ := hD
    exact ⟨C, c, J, ⟨r.symm.trans b⟩⟩
  let := q.leftExact
  let k : GeometricMorphism P.FullSubcategory T :=
    ⟨q.inverse ⋙ r.functor, r.inverse ⋙ q.direct, q.adj.comp r.toAdjunction,
      comp_preservesFiniteLimits _ _⟩
  let i : k.direct ≅ P.ι :=
    (Functor.associator r.inverse F P.ι).symm ≪≫
      Functor.isoWhiskerRight r.counitIso P.ι ≪≫ Functor.leftUnitor P.ι
  exact ⟨hP, k, ⟨i⟩, ⟨P.fullyFaithfulι.ofIso i.symm⟩⟩

private theorem closed_embedding_from_site {T : Type u} [Category.{v} T]
    [HasBinaryProducts T] (V : T) (hV : IsSubterminal V)
    {C : Type w} [SmallCategory C] [HasFiniteLimits C]
    (J : GrothendieckTopology C) [J.Subcanonical]
    (e : T ≌ Sheaf J (Type w)) (U : C) (theta : e.functor.obj V ≅ J.yoneda.obj U) :
    IsGrothendieckTopos.{w} (closedComplementObjects V).FullSubcategory ∧
      ∃ k : GeometricMorphism (closedComplementObjects V).FullSubcategory T,
        Nonempty (k.direct ≅ (closedComplementObjects V).ι) ∧
        Nonempty k.direct.FullyFaithful := by
  -- Representability and full faithfulness turn the given subterminal into a site mono.
  have hs := subterminal_transport e V (J.yoneda.obj U) theta hV
  have hu : IsSubterminal U := fun X f g ↦ J.yoneda.map_injective (hs _ _)
  let := hu.mono_terminal_from
  obtain ⟨Jc, _, q, _, ⟨hq⟩, himg⟩ := closed_complement_site_construction
    C J (⊤_ C) terminalIsTerminal U (terminal.from U)
  let b : GeometricMorphism (Sheaf J (Type w)) T :=
    ⟨e.functor, e.inverse, e.toAdjunction, inferInstance⟩
  let q' := q.comp b
  -- Transport both the essential image and the product-projection criterion.
  have hp : ∀ A, q'.direct.essImage A ↔ closedComplementObjects V A := by
    intro A
    have he : q'.direct.essImage A ↔ q.direct.essImage (e.functor.obj A) := by
      constructor
      · rintro ⟨B, ⟨i⟩⟩
        exact ⟨B, ⟨(e.counitIso.app (q.direct.obj B)).symm ≪≫ e.functor.mapIso i⟩⟩
      · rintro ⟨B, ⟨i⟩⟩
        exact ⟨B, ⟨e.inverse.mapIso i ≪≫ (e.unitIso.app A).symm⟩⟩
    exact he.trans ((himg _).trans
      (closed_product_transport e.functor V A _ _ theta (Iso.refl _)).symm)
  exact image_subtopos ⟨C, inferInstance, Jc, ⟨Equivalence.refl⟩⟩ q'
    (hq.comp e.fullyFaithfulInverse) (closedComplementObjects V) hp

/-- A subterminal object determines complementary open and closed embeddings, with the
universal factorization properties on objects and all direct-image 2-morphisms.
Source: Stacks Project, Sites, Tags 08LW, 08LY, 08LZ and 08M0
(blueprint: lem-trf-topos-complement-factorization).

Proof plan:
1. Use `lem-trf-topos-localization-site-presentation` to present the topos on a small
   subcanonical finite-limit site, with `u` represented by a mono `U → X`, and the slice by
   the slice site. Transport back after the following constructions.
2. `lem-trf-slice-subtopos-site-presentation` gives the restriction/direct-image adjunction.
   Subterminality identifies `W → W × U` with an isomorphism over `U`, so its graph counit
   is invertible. Thus the slice direct image is fully faithful (Tag 08LW).
3. `lem-trf-closed-complement-site-construction` gives a fully faithful geometric direct
   image whose essential image is precisely `closedComplementObjects u`. Replace its source
   by this full subcategory to obtain the geometric morphism `k` with inclusion direct image.
   Tags 08LZ and 08M0 identify this as the complementary closed subtopos.
4. In a sheaf topos the initial sheaf has singleton sections on empty-covered objects and
   empty sections elsewhere. The empty-family sheaf condition and coordinatewise products
   show `0 × B ≅ 0`, also after transport along equivalences.
5. For a closed object `C`, invertibility of `u × C → u` gives exactly one map `u → C`.
   Adjunction makes `k.inverse.obj u` initial. Subterminality makes `j.inverse.obj u` terminal.
6. If `a.inverse.obj u` is initial, adjunction gives a unique map `u → a.direct.obj B`.
   Its graph inverts the projection: the other composite is checked after transposition,
   where the source is `a.inverse(u × a.direct B) ≅ 0 × a.inverse(a.direct B) ≅ 0`.
   Hence `a.direct` lands in the closed full subcategory.
7. Define the closed factor's direct image by this restriction, and inverse image by
   `inclusion ⋙ a.inverse`. The original Hom adjunction and full-subcategory identification
   give natural bijections; `lem-weil-pbc-adjunction-of-natural-bijection` gives the adjunction.
   The inclusion is right adjoint to `k.inverse`, so it preserves finite limits by
   `lem-weil-pbc-right-adjoint-preserves-limits`; the new inverse image is left exact.
   `lem-weil-pbc-conjugate-iso-unit-equation` constructs the compatible composite comparison
   from equality of direct images.
8. Conversely a closed factor sends `u` to an initial object, since left adjoints preserve
   initial objects. Full faithfulness of the inclusion lifts every direct-image natural
   transformation uniquely; naturality is checked after the faithful inclusion. This gives
   the closed equivalence and unique compatible isomorphisms.
9. If `a.inverse.obj u` is terminal, define the open factor's inverse image on `(V → u)`
   by `a.inverse.obj V`, and direct image by `(u × a.direct.obj B → u)`. Pairing with the
   structure map and the original adjunction give natural Hom bijections. The same
   natural-bijection lemma supplies its adjunction. It preserves terminal objects by the
   hypothesis and pullbacks by the underlying slice pullback calculation; hence finite limits.
10. The open composite comparison is `a.inverse(A × u) ≅ a.inverse A`. Apply the conjugate
    isomorphism lemma to opposite adjunctions to obtain the direct-image comparison and unit
    compatibility. Conversely an open factor sends `u` to a terminal object by left exactness.
11. Full faithfulness of `j.direct` lifts all direct-image transformations uniquely,
    including their naturality, identities and compositions. This proves the open equivalence
    and unique compatible isomorphisms. Transport everything to the original presentation.
-/
theorem topos_complement_factorization {E : Type u} [Category.{v} E]
    (hE : IsGrothendieckTopos.{w} E) (u : E) (hu : IsSubterminal u) :
    ∃ (products : HasBinaryProducts E),
      IsGrothendieckTopos.{w} (@closedComplementObjects E _ products u).FullSubcategory ∧
      IsGrothendieckTopos.{w} (Over u) ∧
      ∃ (j : GeometricMorphism (Over u) E)
        (k : GeometricMorphism (@closedComplementObjects E _ products u).FullSubcategory E),
        Nonempty (j.inverse ≅ @Over.star E _ u products) ∧
        Nonempty (k.direct ≅ (@closedComplementObjects E _ products u).ι) ∧
        Nonempty j.direct.FullyFaithful ∧ Nonempty k.direct.FullyFaithful ∧
        ∀ (H : Type uH) [Category.{vH} H], IsGrothendieckTopos.{w} H →
          ((∀ (a : GeometricMorphism H E),
              (∃ (b : GeometricMorphism H
                (@closedComplementObjects E _ products u).FullSubcategory),
                Nonempty ((b.comp k).direct ≅ a.direct)) ↔
              Nonempty (IsInitial (a.inverse.obj u))) ∧
            (∀ (b d : GeometricMorphism H
                (@closedComplementObjects E _ products u).FullSubcategory),
              Function.Bijective
                (fun τ : b.direct ⟶ d.direct ↦ Functor.whiskerRight τ k.direct))) ∧
          ((∀ (a : GeometricMorphism H E),
              (∃ (b : GeometricMorphism H (Over u)),
                Nonempty ((b.comp j).direct ≅ a.direct)) ↔
              Nonempty (IsTerminal (a.inverse.obj u))) ∧
            (∀ (b d : GeometricMorphism H (Over u)),
              Function.Bijective
                (fun τ : b.direct ⟶ d.direct ↦ Functor.whiskerRight τ j.direct))) := by
  classical
  obtain ⟨products, C, c, hC, K, _hK, hJ, e, U, ⟨theta⟩, s, j, ⟨je⟩, _⟩ :=
    topos_localization_site_presentation E hE u
  let := products
  let := hC
  let := hJ
  have := topos_finiteLimits hE
  have hOver : IsGrothendieckTopos.{w} (Over u) :=
    ⟨Over U, inferInstance, K.toGrothendieck.over U, ⟨s⟩⟩
  obtain ⟨hc, k, ⟨ki⟩, hk⟩ :=
    closed_embedding_from_site u hu K.toGrothendieck e U theta
  have hj := open_directFF u hu j je
  refine ⟨products, hc, hOver, j, k, ⟨je⟩, ⟨ki⟩, hj, hk, ?_⟩
  intro H _ hH
  refine ⟨⟨fun a ↦ closed_universal hH u k ki a, ?_⟩,
    ⟨fun a ↦ open_universal u hu j je a, ?_⟩⟩
  · intro b d
    exact (hk.some.whiskeringRight H).map_bijective b.direct d.direct
  · intro b d
    exact (hj.some.whiskeringRight H).map_bijective b.direct d.direct

end CategoryTheory
