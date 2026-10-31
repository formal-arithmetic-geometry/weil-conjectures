/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Ring.Subring.Basic

/-! # Images of commutative algebra sheaves

Source: Stacks Project, Sheaves, Tag 0087, lemma-sheafify-presheaf-structures;
Modules, Tag 01AG, lemma-abelian and the preceding image/coimage construction
(blueprint: lem-weil-pbc-ringed-space-algebra-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory

private abbrev localImage {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A) :=
  (Subfunctor.range (Functor.whiskerRight ψ.hom (forget CommRingCat))).sheafify
    (Opens.grothendieckTopology X)

private def localImageRing {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A)
    (U : (Opens X)ᵒᵖ) : Subring (A.obj.obj U) where
  carrier := (localImage ψ).obj U
  zero_mem' := (Subfunctor.range _).le_sheafify _ U ⟨0, (ψ.hom.app U).hom.map_zero⟩
  one_mem' := (Subfunctor.range _).le_sheafify _ U ⟨1, (ψ.hom.app U).hom.map_one⟩
  add_mem' := by
    intro a b ha hb
    apply (Opens.grothendieckTopology X).superset_covering ?_
      ((Opens.grothendieckTopology X).intersection_covering ha hb)
    rintro V f ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
    change ψ.hom.app _ a' = A.obj.map f.op a at ha'
    change ψ.hom.app _ b' = A.obj.map f.op b at hb'
    refine ⟨a' + b', ?_⟩
    change ψ.hom.app _ (a' + b') = A.obj.map f.op (a + b)
    rw [map_add, map_add, ha', hb']
  mul_mem' := by
    intro a b ha hb
    apply (Opens.grothendieckTopology X).superset_covering ?_
      ((Opens.grothendieckTopology X).intersection_covering ha hb)
    rintro V f ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
    change ψ.hom.app _ a' = A.obj.map f.op a at ha'
    change ψ.hom.app _ b' = A.obj.map f.op b at hb'
    refine ⟨a' * b', ?_⟩
    change ψ.hom.app _ (a' * b') = A.obj.map f.op (a * b)
    rw [map_mul, map_mul, ha', hb']
  neg_mem' := by
    intro a ha
    apply (Opens.grothendieckTopology X).superset_covering ?_ ha
    rintro V f ⟨a', ha'⟩
    change ψ.hom.app _ a' = A.obj.map f.op a at ha'
    refine ⟨-a', ?_⟩
    change ψ.hom.app _ (-a') = A.obj.map f.op (-a)
    rw [map_neg, map_neg, ha']

private def localImagePresheaf {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A) :
    (Opens X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (localImageRing ψ U)
  map f := CommRingCat.ofHom
    (((A.obj.map f).hom.comp (localImageRing ψ _).subtype).codRestrict
      (localImageRing ψ _) (fun a ↦ (localImage ψ).map f a.property))
  map_id U := by ext a; exact congrArg (fun f ↦ f a.val) (A.obj.map_id U)
  map_comp f g := by ext a; exact congrArg (fun f ↦ f a.val) (A.obj.map_comp f g)

private def localImageSheaf {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A) :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  ⟨localImagePresheaf ψ, by
    rw [Presheaf.isSheaf_iff_isSheaf_comp _ _ (forget CommRingCat)]
    change Presheaf.IsSheaf _ (localImage ψ).toFunctor
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose (Opens.grothendieckTopology X) (forget CommRingCat.{u})).obj A).property⟩

private def localImageι {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A) :
    localImageSheaf ψ ⟶ A where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom (localImageRing ψ U).subtype
      naturality := by intros; rfl }

private def localImageπ {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A) :
    B ⟶ localImageSheaf ψ where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom ((ψ.hom.app U).hom.codRestrict
        (localImageRing ψ U) (fun b ↦ (Subfunctor.range _).le_sheafify _ U ⟨b, rfl⟩))
      naturality := by
        intro U V f
        ext b
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (ψ.hom.naturality f) b }

private theorem localImage_fac {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A) :
    localImageπ ψ ≫ localImageι ψ = ψ := rfl

private theorem localImage_injective {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A)
    (U : (Opens X)ᵒᵖ) : Function.Injective ((localImageι ψ).hom.app U) :=
  Subtype.val_injective

private theorem localImage_surjective {X : Type u} [TopologicalSpace X]
    {B A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (ψ : B ⟶ A) :
    Sheaf.IsLocallySurjective (localImageπ ψ) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Sheaf.IsLocallySurjective
    (Sheaf.toImage ((sheafCompose _ (forget CommRingCat.{u})).map ψ))
  infer_instance

private theorem localImage_universal {X : Type u} [TopologicalSpace X]
    {B A H : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (ψ : B ⟶ A) (f : B ⟶ H) (j : H ⟶ A)
    (hj : ∀ U, Function.Injective (j.hom.app U)) (hf : f ≫ j = ψ) :
    ∃ k : localImageSheaf ψ ⟶ H,
      k ≫ j = localImageι ψ ∧ localImageπ ψ ≫ k = f := by
  let T := sheafCompose (Opens.grothendieckTopology X) (forget CommRingCat.{u})
  have : Mono (T.map j) := Sheaf.mono_of_injective _ hj
  let M : MonoFactorisation (T.map ψ) :=
    { I := T.obj H, m := T.map j, e := T.map f, fac := by rw [← T.map_comp, hf] }
  let k := (imageFactorization (T.map ψ)).isImage.lift M
  have hk : k ≫ T.map j = Sheaf.imageι (T.map ψ) :=
    (imageFactorization (T.map ψ)).isImage.lift_fac M
  let q (U : (Opens X)ᵒᵖ) : localImageRing ψ U → H.obj.obj U :=
    fun a ↦ k.hom.app U a
  have hk' (U : (Opens X)ᵒᵖ) (a : (localImageSheaf ψ).obj.obj U) :
      j.hom.app U (q U a) = a.val :=
    congrArg (fun t : Sheaf.image (T.map ψ) ⟶ T.obj A ↦ t.hom.app U a) hk
  let kR : localImageSheaf ψ ⟶ H :=
    { hom :=
      { app := fun U ↦ CommRingCat.ofHom
          { toFun := q U
            map_one' := hj U (by rw [map_one, hk']; rfl)
            map_mul' := fun a b ↦ hj U (by rw [map_mul, hk', hk', hk']; rfl)
            map_zero' := hj U (by rw [map_zero, hk']; rfl)
            map_add' := fun a b ↦ hj U (by rw [map_add, hk', hk', hk']; rfl) }
        naturality := by
          intro U V g
          ext a
          exact ConcreteCategory.congr_hom (k.hom.naturality g) a } }
  have hkR : kR ≫ j = localImageι ψ := by
    ext U a
    exact hk' U a
  have : Mono j := Sheaf.mono_of_injective j hj
  refine ⟨kR, hkR, ?_⟩
  apply (cancel_mono j).mp
  rw [Category.assoc, hkR, localImage_fac, hf]

/-- The locally liftable sections form an algebra sheaf whose underlying module is the
categorical module image. The injective section maps identify `D` with precisely the
specified subsets of `A`; their naturality and algebra compatibility give the inherited
restrictions and operations under this identification.

Source: Stacks Project, Sheaves, Tag 0087, lemma-sheafify-presheaf-structures;
Modules, Tag 01AG, lemma-abelian; Homology, Tag 0106, definition-kernel
(blueprint: lem-weil-pbc-ringed-space-algebra-image).

Proof:
1. Sheafify the set-valued range as a subfunctor of `A`. Intersect the covering
   sieves of local lifts to prove closure under addition and multiplication; negatives,
   zero and one lift as well. This gives subrings with inherited restrictions.
2. Mathlib's `Subfunctor.sheafify_isSheaf` proves the sheaf condition for these
   subsets. The forgetful functor from commutative rings reflects the sheaf condition.
3. The sectionwise range restriction and inclusion give `p` and `i`. Their underlying
   set maps are Mathlib's `Sheaf.toImage` and `Sheaf.imageι`; hence `p` is locally
   surjective and `i` is sectionwise injective. Choose neighborhoods indexed by the
   points of an open to obtain the asserted covering, also for the empty open.
4. Forget to the underlying abelian sheaves to prove that the module map of `i` is
   monic and that of `p` is epic. Local surjectivity depends only on section maps,
   and the faithful underlying-sheaf functor reflects epimorphisms.
5. In the abelian module category, an epimorphism is strong. Apply
   `image.isoStrongEpiMono` to identify this factorization with the chosen module
   image. Cancel its monic inclusion to get the equality for the map from `B`.
6. For any sectionwise injective algebra factorization, Mathlib's image universal
   property for sheaves of sets gives the unique map to its middle object. Applying
   the injective map to `A` proves preservation of one, multiplication, zero and
   addition, so this is a ring-sheaf map.
7. Cancellation proves its compatibility with the structure map from `O`, its
   compatibility with `p`, and uniqueness as an algebra-sheaf morphism.
-/
theorem commAlgebraSheaf_image_factorization
    {X : Type u} [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    {B A : Under O} (ψ : B ⟶ A) :
    ∃ (D : Under O) (p : B ⟶ D) (i : D ⟶ A),
      p ≫ i = ψ ∧
      (∀ U : Opens X, Function.Injective (i.right.hom.app (op U))) ∧
      (∀ (U : Opens X) (a : A.right.obj.obj (op U)),
        (∃ d : D.right.obj.obj (op U), i.right.hom.app (op U) d = a) ↔
          ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U), (x : X) ∈ V ∧
            ∃ b : B.right.obj.obj (op V),
              A.right.obj.map (homOfLE hV).op a = ψ.right.hom.app (op V) b) ∧
      (∀ (U : Opens X) (d : D.right.obj.obj (op U)),
        ∃ (I : Type u) (V : I → Opens X) (hV : ∀ t, V t ≤ U)
          (b : ∀ t, B.right.obj.obj (op (V t))),
          (⨆ t, V t) = U ∧ ∀ t,
            p.right.hom.app (op (V t)) (b t) =
              D.right.obj.map (homOfLE (hV t)).op d) ∧
      (∃ e : (commAlgebraSheafModuleFunctor O).obj D ≅
          image ((commAlgebraSheafModuleFunctor O).map ψ),
        e.hom ≫ image.ι ((commAlgebraSheafModuleFunctor O).map ψ) =
          (commAlgebraSheafModuleFunctor O).map i ∧
        (commAlgebraSheafModuleFunctor O).map p ≫ e.hom =
          factorThruImage ((commAlgebraSheafModuleFunctor O).map ψ)) ∧
      (∀ (H : Under O) (f : B ⟶ H) (j : H ⟶ A),
        (∀ U : Opens X, Function.Injective (j.right.hom.app (op U))) →
        f ≫ j = ψ → ∃! k : D ⟶ H, k ≫ j = i ∧ p ≫ k = f) := by
  classical
  let π := localImageπ ψ.right
  let ι := localImageι ψ.right
  have hfac : π ≫ ι = ψ.right := localImage_fac ψ.right
  have hmono : Mono ι := Sheaf.mono_of_injective ι (localImage_injective ψ.right)
  let D : Under O := Under.mk (B.hom ≫ π)
  let p : B ⟶ D := Under.homMk π rfl
  let i : D ⟶ A := Under.homMk ι (by
    change (B.hom ≫ π) ≫ ι = A.hom
    rw [Category.assoc, hfac, Under.w ψ])
  have hpi : p ≫ i = ψ := by apply Under.UnderMorphism.ext; exact hfac
  have hcover (U : Opens X) (d : D.right.obj.obj (op U)) :
      ∃ (I : Type u) (V : I → Opens X) (hV : ∀ t, V t ≤ U)
        (b : ∀ t, B.right.obj.obj (op (V t))),
        (⨆ t, V t) = U ∧ ∀ t,
          p.right.hom.app (op (V t)) (b t) =
            D.right.obj.map (homOfLE (hV t)).op d := by
    have hl := (TopCat.Presheaf.isLocallySurjective_iff
      (X := TopCat.of X) π.hom).mp (localImage_surjective ψ.right)
    choose V hV hb hx using fun x : U ↦ hl U d x.val x.property
    choose b hb using hb
    refine ⟨U, V, hV, b, ?_, hb⟩
    apply le_antisymm (iSup_le hV)
    intro x hxU
    exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩
  refine ⟨D, p, i, hpi, fun U ↦ localImage_injective ψ.right (op U), ?_, hcover, ?_, ?_⟩
  · intro U a
    change (∃ d : localImageRing ψ.right (op U), d.val = a) ↔ _
    have hm : (∃ d : localImageRing ψ.right (op U), d.val = a) ↔
        a ∈ (localImage ψ.right).obj (op U) := by
      constructor
      · rintro ⟨d, rfl⟩; exact d.property
      · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
    rw [hm]
    change (∀ x ∈ U, ∃ (V : Opens X) (f : V ⟶ U),
      (∃ b, ψ.right.hom.app (op V) b = A.right.obj.map f.op a) ∧ x ∈ V) ↔ _
    constructor
    · intro h x
      obtain ⟨V, f, ⟨b, hb⟩, hx⟩ := h x.val x.property
      exact ⟨V, leOfHom f, hx, b, hb.symm⟩
    · intro h x hx
      obtain ⟨V, hV, hxV, b, hb⟩ := h ⟨x, hx⟩
      exact ⟨V, homOfLE hV, ⟨b, hb.symm⟩, hxV⟩
  · let F := commAlgebraSheafModuleFunctor O
    let R := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat)).obj O
    let T := SheafOfModules.toSheaf.{u} R
    have hmi : Mono (F.map i) := by
      apply T.mono_of_mono_map
      apply Sheaf.mono_of_injective
      intro U
      change Function.Injective (ι.hom.app U)
      exact localImage_injective ψ.right U
    have hep : Epi (F.map p) := by
      apply T.epi_of_epi_map
      have : Sheaf.IsLocallySurjective (T.map (F.map p)) := by
        change Presheaf.IsLocallySurjective _ (Functor.whiskerRight π.hom
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
        apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
        change Presheaf.IsLocallySurjective _ (Functor.whiskerRight π.hom
          (forget CommRingCat))
        exact (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mp
          (localImage_surjective ψ.right)
      exact Sheaf.epi_of_isLocallySurjective _
    have : StrongEpi (F.map p) := strongEpi_of_epi _
    let e := image.isoStrongEpiMono (F.map p) (F.map i) (by rw [← F.map_comp, hpi])
    refine ⟨e, image.isoStrongEpiMono_hom_comp_ι _ _ _, ?_⟩
    apply (cancel_mono (image.ι (F.map ψ))).mp
    rw [Category.assoc, image.isoStrongEpiMono_hom_comp_ι,
      ← F.map_comp, hpi, image.fac]
  · intro H f j hj hf
    obtain ⟨k, hk, hpk⟩ := localImage_universal ψ.right f.right j.right
      (fun U ↦ hj U.unop) (congrArg CommaMorphism.right hf)
    have hmj : Mono j.right := Sheaf.mono_of_injective j.right (fun U ↦ hj U.unop)
    let k' : D ⟶ H := Under.homMk k (by
      apply (cancel_mono j.right).mp
      rw [Category.assoc, hk]
      change (B.hom ≫ π) ≫ ι = H.hom ≫ j.right
      rw [Category.assoc, hfac, Under.w ψ, Under.w j])
    have hk' : k' ≫ j = i := by apply Under.UnderMorphism.ext; exact hk
    have hpk' : p ≫ k' = f := by apply Under.UnderMorphism.ext; exact hpk
    refine ⟨k', ⟨hk', hpk'⟩, ?_⟩
    intro l hl
    apply Under.UnderMorphism.ext
    apply (cancel_mono j.right).mp
    exact (congrArg CommaMorphism.right hl.1).trans hk.symm

end CategoryTheory
