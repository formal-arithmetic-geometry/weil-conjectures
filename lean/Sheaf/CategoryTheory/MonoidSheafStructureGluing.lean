/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.SiteCoveringAxioms

import Sheaf.CategoryTheory.MonoidSheafLocalOperations
import Sheaf.CategoryTheory.OverSheafMapGluing
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Group.Ext

/-!
# Gluing a commutative monoid structure on a fixed sheaf of sets

Source: Stacks Project, Sites, Tag 04TQ, lemma-glue-maps, applied to multiplication,
identity and the structural map (blueprint: lem-trf-monoid-sheaf-structure-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The canonical identification of the two composites from a double overlap to the base.
Source: Stacks Project, Sites, Tag 04TQ, relocalization of a double overlap
(blueprint: lem-trf-monoid-sheaf-structure-gluing). Its component has identity underlying
arrow; it only identifies the two equal composites to the base. -/
noncomputable def monoidGluingOverlapIso {C : Type u} [Category.{v} C] [HasPullbacks C]
    {U A B : C} (f : A ⟶ U) (g : B ⟶ U) :
    Over.map (pullback.fst f g) ⋙ Over.map f ≅
      Over.map (pullback.snd f g) ⋙ Over.map g :=
  (Over.mapComp _ _).symm ≪≫ Over.mapCongr _ _ (pullback.condition (f := f) (g := g)) ≪≫
    Over.mapComp _ _

private noncomputable abbrev gluingCoverObject {C : Type u} [Category.{v} C] [HasPullbacks C]
    {U T : C} (f : T ⟶ U) (V : Over U) : Over U :=
  (Over.map f).obj (Over.mk (pullback.snd V.hom f))

private noncomputable def gluingCoverArrow {C : Type u} [Category.{v} C] [HasPullbacks C]
    {U T : C} (f : T ⟶ U) (V : Over U) : gluingCoverObject f V ⟶ V :=
  Over.homMk (pullback.fst V.hom f) pullback.condition

private theorem gluingCover_mem {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) {I : Type (max u v w)}
    {U : C} {X : I → C} (f : ∀ a, X a ⟶ U)
    (hcov : Sieve.ofArrows X f ∈ J U) (V : Over U) :
    Sieve.ofArrows (fun a ↦ gluingCoverObject (f a) V)
      (fun a ↦ gluingCoverArrow (f a) V) ∈ (J.over U) V := by
  rw [J.mem_over_iff, Sieve.overEquiv_ofArrows]
  change Sieve.ofArrows (fun a ↦ pullback V.hom (f a))
    (fun a ↦ pullback.fst V.hom (f a)) ∈ J V.left
  rw [Sieve.ofArrows_eq_pullback_of_isPullback _
    (fun a ↦ IsPullback.of_hasPullback V.hom (f a))]
  exact J.pullback_stable _ hcov

private theorem gluingCover_ext {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) {I : Type (max u v w)}
    {U : C} {X : I → C} (f : ∀ a, X a ⟶ U)
    (hcov : Sieve.ofArrows X f ∈ J U)
    (G : Sheaf (J.over U) (Type (max u v w)))
    (V : Over U) (x y : G.obj.obj (op V))
    (h : ∀ a, G.obj.map (gluingCoverArrow (f a) V).op x =
      G.obj.map (gluingCoverArrow (f a) V).op y) : x = y := by
  have hxy : (↾fun _ : PUnit ↦ x) = (↾fun _ : PUnit ↦ y) :=
    G.property.hom_ext_ofArrows (fun a ↦ gluingCoverArrow (f a) V)
      (gluingCover_mem J f hcov V) (fun a ↦ by ext z; exact h a)
  exact ConcreteCategory.congr_hom hxy PUnit.unit

/-- Compatible local monoid structures and structural maps glue uniquely on a fixed set sheaf.
Source: Stacks Project, Sites, Tag 04TQ, lemma-glue-maps
(blueprint: lem-trf-monoid-sheaf-structure-gluing).

The `CommMonoid` family is on the original section sets of `F`, so uniqueness is equality
of structures, rather than merely uniqueness up to an isomorphism of another sheaf. The
first clause says that `M` is the only family with homomorphic restrictions for which every
`e a` is a monoid isomorphism; the second gives the unique structural map for `M`.
The local isomorphisms are given on underlying presheaves; since both are sheaves these
are precisely the underlying set-sheaf isomorphisms. Overlap equations include a = b.

Proof:
1. Form the sectionwise product F × F and the singleton sheaf using
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise. Restriction to slice sites is sectionwise
   by def-pur-localized-ringed-site.
2. Transport local multiplication and identity through e_a. On a double overlap the equation
   e_b = phi_ab e_a and preservation of multiplication and identity by phi_ab show that these
   transported maps agree, also for repeated indices.
3. Cancel e_a in phi_bc phi_ab e_a = e_c = phi_ac e_a to obtain the triple cocycle.
   The morphism clause of lem-pe-set-sheaf-cover-descent glues the transported operations
   uniquely. Naturality makes every restriction preserve multiplication and identity.
4. Pull the cover back to any V. The sheaf equalizer from def-weil-pbc-sites-and-cohomology
   makes restriction to the product of the local section sets injective. Associativity,
   commutativity and the two identity laws follow from their local versions through e_a.
   Thus the local bijections are monoid isomorphisms, including their inverses.
5. The maps alpha_a e_a agree on overlaps by the two overlap hypotheses. Apply the same
   morphism-gluing clause to obtain the unique natural structural map alpha.
6. Test multiplication and identity preservation by alpha on the pulled-back cover, using
   separatedness of the underlying set sheaf of R and preservation by alpha_a and e_a.
7. Any other structure gives multiplication and identity maps with these same localizations.
   Uniqueness of gluing gives equality of both operations, hence of CommMonoid structures.
   The uniqueness in step 5 also gives uniqueness among the required monoid homomorphisms.
-/
theorem monoidSheafStructureGluing
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) {I : Type (max u v w)}
    (U : C) (X : I → C) (f : ∀ a, X a ⟶ U)
    (hcov : Sieve.ofArrows X f ∈ J U)
    (R : Sheaf (J.over U) CommMonCat.{max u v w})
    (A : ∀ a, Sheaf (J.over (X a)) CommMonCat.{max u v w})
    (alpha : ∀ a, A a ⟶ (J.overMapPullback CommMonCat (f a)).obj R)
    (phi : ∀ a b,
      (J.overMapPullback CommMonCat (pullback.fst (f a) (f b))).obj (A a) ≅
        (J.overMapPullback CommMonCat (pullback.snd (f a) (f b))).obj (A b))
    (hphi : ∀ (a b : I) (V : Over (pullback (f a) (f b)))
      (x : (A a).obj.obj (op ((Over.map (pullback.fst (f a) (f b))).obj V))),
      R.obj.map ((monoidGluingOverlapIso (f a) (f b)).hom.app V).op
        ((alpha b).hom.app _ ((phi a b).hom.hom.app (op V) x)) =
          (alpha a).hom.app _ x)
    (F : Sheaf (J.over U) (Type (max u v w)))
    (e : ∀ a, (Over.map (f a)).op ⋙ F.obj ≅ (A a).obj ⋙ forget CommMonCat)
    (he : ∀ (a b : I) (V : Over (pullback (f a) (f b)))
      (x : F.obj.obj (op ((Over.map (pullback.snd (f a) (f b)) ⋙
        Over.map (f b)).obj V))),
      (e b).hom.app _ x = (phi a b).hom.hom.app (op V)
        ((e a).hom.app _
          (F.obj.map ((monoidGluingOverlapIso (f a) (f b)).hom.app V).op x))) :
    ∃ M : ∀ V : (Over U)ᵒᵖ, CommMonoid (F.obj.obj V),
      (∀ M' : ∀ V : (Over U)ᵒᵖ, CommMonoid (F.obj.obj V),
      ((∀ (V W : (Over U)ᵒᵖ) (k : V ⟶ W) (x y : F.obj.obj V),
          F.obj.map k ((M' V).mul x y) = (M' W).mul (F.obj.map k x) (F.obj.map k y)) ∧
        (∀ (V W : (Over U)ᵒᵖ) (k : V ⟶ W),
          F.obj.map k (M' V).one = (M' W).one)) ∧
      ((∀ (a : I) (V : (Over (X a))ᵒᵖ)
          (x y : F.obj.obj ((Over.map (f a)).op.obj V)),
          (e a).hom.app V ((M' _).mul x y) = (e a).hom.app V x * (e a).hom.app V y) ∧
        (∀ (a : I) (V : (Over (X a))ᵒᵖ),
          (e a).hom.app V (M' _).one = 1)) ↔ M' = M) ∧
      ∃! beta : F.obj ⟶ R.obj ⋙ forget CommMonCat,
        ((∀ (V : (Over U)ᵒᵖ) (x y : F.obj.obj V),
            beta.app V ((M V).mul x y) = beta.app V x * beta.app V y) ∧
          (∀ V : (Over U)ᵒᵖ, beta.app V (M V).one = 1)) ∧
        (∀ (a : I) (V : (Over (X a))ᵒᵖ)
          (x : F.obj.obj ((Over.map (f a)).op.obj V)),
          beta.app _ x = (alpha a).hom.app V ((e a).hom.app V x)) := by
  classical
  obtain ⟨mul, one, ⟨hmul, hone⟩, ⟨hemul, heone⟩⟩ :=
    monoidSheafLocalOperations J U X f hcov A phi F e he
  let t (V : (Over U)ᵒᵖ) (a : I) (x : F.obj.obj V) :=
    (e a).hom.app (op (Over.mk (pullback.snd V.unop.hom (f a))))
      (F.obj.map (gluingCoverArrow (f a) V.unop).op x)
  have ht (V : (Over U)ᵒᵖ) (x y : F.obj.obj V)
      (h : ∀ a, t V a x = t V a y) : x = y := by
    apply gluingCover_ext J f hcov F V.unop x y
    intro a
    exact ((e a).app _).toEquiv.injective (h a)
  have htmul (V : (Over U)ᵒᵖ) (a : I) (x y : F.obj.obj V) :
      t V a (mul V x y) = t V a x * t V a y := by
    dsimp [t]
    rw [hmul]
    exact hemul a _ _ _
  have htone (V : (Over U)ᵒᵖ) (a : I) : t V a (one V) = 1 := by
    dsimp [t]
    rw [hone]
    exact heone a _
  let M : ∀ V : (Over U)ᵒᵖ, CommMonoid (F.obj.obj V) := fun V ↦
    { mul := mul V
      one := one V
      mul_assoc := fun x y z ↦ ht V _ _ (fun a ↦ by
        change t V a (mul V (mul V x y) z) = t V a (mul V x (mul V y z))
        rw [htmul, htmul, htmul, htmul]
        exact mul_assoc _ _ _)
      one_mul := fun x ↦ ht V _ _ (fun a ↦ by
        change t V a (mul V (one V) x) = t V a x
        rw [htmul, htone, one_mul])
      mul_one := fun x ↦ ht V _ _ (fun a ↦ by
        change t V a (mul V x (one V)) = t V a x
        rw [htmul, htone, mul_one])
      mul_comm := fun x y ↦ ht V _ _ (fun a ↦ by
        change t V a (mul V x y) = t V a (mul V y x)
        rw [htmul, htmul]
        exact mul_comm _ _) }
  refine ⟨M, ?_, ?_⟩
  · intro M'
    constructor
    · rintro ⟨⟨hmul', hone'⟩, ⟨hemul', heone'⟩⟩
      funext V
      apply CommMonoid.ext
      funext x y
      apply ht V
      intro a
      change t V a ((M' V).mul x y) = t V a (mul V x y)
      dsimp [t]
      rw [hmul']
      erw [hemul']
      exact (htmul V a x y).symm
    · rintro rfl
      exact ⟨⟨hmul, hone⟩, ⟨hemul, heone⟩⟩
  · let G := (sheafCompose (J.over U) (forget CommMonCat)).obj R
    let s (a : I) : (Over.map (f a)).op ⋙ F.obj ⟶
        (Over.map (f a)).op ⋙ G.obj :=
      (e a).hom ≫ Functor.whiskerRight (alpha a).hom (forget CommMonCat)
    obtain ⟨beta, hbeta, huniq⟩ := overSheafMapGluing J U X f hcov F G s (by
      intro a b V x
      change R.obj.map ((monoidGluingOverlapIso (f a) (f b)).hom.app V).op
        ((alpha b).hom.app _ ((e b).hom.app _ x)) =
          (alpha a).hom.app _ ((e a).hom.app _
            (F.obj.map ((monoidGluingOverlapIso (f a) (f b)).hom.app V).op x))
      rw [he, hphi]
      rfl)
    change F.obj ⟶ R.obj ⋙ forget CommMonCat at beta
    have hbeta' : ∀ (a : I) (V : (Over (X a))ᵒᵖ)
        (x : F.obj.obj ((Over.map (f a)).op.obj V)),
        beta.app _ x = (alpha a).hom.app V ((e a).hom.app V x) := hbeta
    have hbmul (V : (Over U)ᵒᵖ) (x y : F.obj.obj V) :
        beta.app V (mul V x y) = beta.app V x * beta.app V y := by
      apply gluingCover_ext J f hcov G V.unop
      intro a
      have hn (z : F.obj.obj V) :
          beta.app _ (F.obj.map (gluingCoverArrow (f a) V.unop).op z) =
            R.obj.map (gluingCoverArrow (f a) V.unop).op (beta.app V z) := by
        exact ConcreteCategory.congr_hom
          (beta.naturality (gluingCoverArrow (f a) V.unop).op) z
      change R.obj.map _ (beta.app V (mul V x y)) =
        R.obj.map _ (beta.app V x * beta.app V y)
      rw [map_mul (R.obj.map _).hom, ← hn, ← hn, ← hn, hmul]
      erw [hbeta', hbeta', hbeta']
      change (alpha a).hom.app _ ((e a).hom.app _ (mul _ _ _)) = _
      rw [hemul, map_mul ((alpha a).hom.app _).hom]
    have hbone (V : (Over U)ᵒᵖ) : beta.app V (one V) = 1 := by
      apply gluingCover_ext J f hcov G V.unop
      intro a
      have hn := ConcreteCategory.congr_hom
        (beta.naturality (gluingCoverArrow (f a) V.unop).op) (one V)
      change beta.app _ (F.obj.map _ (one V)) =
        R.obj.map _ (beta.app V (one V)) at hn
      change R.obj.map _ (beta.app V (one V)) = R.obj.map _ 1
      rw [map_one (R.obj.map _).hom, ← hn, hone]
      erw [hbeta']
      change (alpha a).hom.app _ ((e a).hom.app _ (one _)) = 1
      rw [heone, map_one ((alpha a).hom.app _).hom]
    refine ⟨beta, ⟨⟨hbmul, hbone⟩, hbeta'⟩, ?_⟩
    intro beta' hbeta'
    exact huniq beta' hbeta'.2

end CategoryTheory
