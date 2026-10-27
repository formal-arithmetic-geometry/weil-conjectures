module

public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Sheaf.CategoryTheory.SiteCoveringAxioms

import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Gluing monoid-sheaf morphisms over a fixed sheaf

Source: Stacks Project, Sites, Tag 04TQ, lemma-glue-maps, and Tag 03EH,
lemma-relocalize (blueprint: lem-trf-monoid-sheaf-morphism-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The Hom equivalence induced by the inverse iterated-slice equivalence. -/
private noncomputable def monoidSheafHomEquiv {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C}
    (M N : Sheaf (J.over U) CommMonCat.{max u v w}) (T : Over U) :
    (sheafHom' M N).obj (Opposite.op T) ≃
      ((J.pseudofunctorOver CommMonCat.{max u v w}).presheafHom M N).obj (Opposite.op T) := by
  letI : T.iteratedSliceBackward.IsEquivalence := T.iteratedSliceEquiv.isEquivalence_inverse
  let W := (Functor.whiskeringLeft (Over T.left)ᵒᵖ (Over T)ᵒᵖ
    CommMonCat.{max u v w}).obj T.iteratedSliceBackward.op
  exact (Sheaf.homEquiv
    (X := ((J.over U).overPullback CommMonCat.{max u v w} T).obj M)
    (Y := ((J.over U).overPullback CommMonCat.{max u v w} T).obj N)).trans
    ((Functor.FullyFaithful.ofFullyFaithful W).homEquiv
      (X := (((J.over U).overPullback CommMonCat.{max u v w} T).obj M).obj)
      (Y := (((J.over U).overPullback CommMonCat.{max u v w} T).obj N).obj) |>.trans
        (Sheaf.homEquiv
          (X := (J.overMapPullback CommMonCat.{max u v w} T.hom).obj M)
          (Y := (J.overMapPullback CommMonCat.{max u v w} T.hom).obj N)).symm)


/-- Naturality of the canonical slice-sheaf Hom equivalence.

Source: Stacks Project, sites.tex, Tag 04TQ, restriction of sheaf morphisms

Proof: the component at T precomposes a natural transformation on (C/U)/T
with the inverse slice equivalence C/T -> (C/U)/T. For a morphism S -> T,
the two composites evaluate a local transformation on the same object,
up to the canonical isomorphism with identity underlying arrow. The
pseudofunctor composition constraints are exactly the restriction maps
along this isomorphism and its inverse. Naturality of the transformation
along that isomorphism gives equality of the component maps. Extensionality
first for sheaf morphisms, then for natural transformations, then for
functions proves the displayed equality. The inverse slice equivalence
is valid for every object, including empty section sets; no cover or
nonempty index set is used. -/
private theorem monoidSheafHomEquiv_naturality
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U : C}
    (M N : Sheaf (J.over U) CommMonCat.{max u v w})
    {T S : (Over U)ᵒᵖ} (f : T ⟶ S) :
    (sheafHom' M N).map f ≫ (monoidSheafHomEquiv J M N S.unop).toIso.hom =
      (monoidSheafHomEquiv J M N T.unop).toIso.hom ≫
        ((J.pseudofunctorOver CommMonCat.{max u v w}).presheafHom M N).map f := by
  rcases T with ⟨⟨T, rT, t⟩⟩
  rcases S with ⟨⟨S, rS, s⟩⟩
  rcases f with ⟨⟨h, r, w⟩⟩
  change S ⟶ T at h
  change rS ⟶ rT at r
  change S ⟶ U at s
  change T ⟶ U at t
  change h ≫ t = s ≫ 𝟙 U at w
  have hw : h ≫ t = s := by simpa using w
  subst s
  apply ConcreteCategory.hom_ext
  intro α
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  simp only [Pseudofunctor.presheafHom_obj, comp_apply, Equiv.toIso_hom_hom_apply,
    Pseudofunctor.presheafHom_map, Quiver.Hom.unop_op', TypeCat.hom_ofHom,
    TypeCat.Fun.coe_mk]
  dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Pseudofunctor.mapComp']
  simp only [Functor.map_id]
  change α.hom.app (Opposite.op ((Over.map
    ({ left := h, right := r, w := w } :
      ({ left := S, right := rS, hom := h ≫ t } : Over U) ⟶
        ({ left := T, right := rT, hom := t } : Over U))).obj
      ((Over.iteratedSliceBackward
        ({ left := S, right := rS, hom := h ≫ t } : Over U)).obj V.unop))) =
    M.obj.map ((Over.mapComp h t).inv.app V.unop).op ≫
      α.hom.app (Opposite.op ((Over.iteratedSliceBackward
        ({ left := T, right := rT, hom := t } : Over U)).obj
          ((Over.map h).obj V.unop))) ≫ N.obj.map ((Over.mapComp h t).hom.app V.unop).op
  let A : Over ({ left := T, right := rT, hom := t } : Over U) :=
    (Over.map
      ({ left := h, right := r, w := w } :
        ({ left := S, right := rS, hom := h ≫ t } : Over U) ⟶
          ({ left := T, right := rT, hom := t } : Over U))).obj
      ((Over.iteratedSliceBackward
        ({ left := S, right := rS, hom := h ≫ t } : Over U)).obj V.unop)
  let B := (Over.iteratedSliceBackward
    ({ left := T, right := rT, hom := t } : Over U)).obj ((Over.map h).obj V.unop)
  let e : A ≅ B := Over.isoMk ((Over.mapComp h t).app V.unop) (by
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ (V.unop.hom ≫ h) = V.unop.hom ≫ h
    exact Category.id_comp _)
  have hn : M.obj.map ((Over.mapComp h t).inv.app V.unop).op ≫ α.hom.app (Opposite.op B) =
      α.hom.app (Opposite.op A) ≫ N.obj.map ((Over.mapComp h t).inv.app V.unop).op := by
    exact α.hom.naturality e.inv.op
  rw [← Category.assoc, hn, Category.assoc, ← N.obj.map_comp, ← op_comp]
  simp only [Iso.hom_inv_id_app, op_id]
  exact ((congrArg (fun g ↦ α.hom.app (Opposite.op A) ≫ g)
    (N.obj.map_id (Opposite.op ((Over.map (h ≫ t)).obj V.unop)))).trans
      (Category.comp_id _)).symm


private noncomputable def monoidHomIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {U : C}
    (M N : Sheaf (J.over U) CommMonCat.{max u v w}) :
    sheafHom' M N ≅ (J.pseudofunctorOver CommMonCat.{max u v w}).presheafHom M N :=
  NatIso.ofComponents (fun T ↦ (monoidSheafHomEquiv J M N T.unop).toIso)
    (monoidSheafHomEquiv_naturality J M N)

/-- Compatible local monoid-sheaf maps over `R` glue uniquely, and local
isomorphisms glue with their specified inverses.

Source: Stacks Project, Sites, Tag 04TQ, lemma-glue-maps, and Tag 03EH,
lemma-relocalize (blueprint: lem-trf-monoid-sheaf-morphism-gluing).

`localMap.hom i` is the given map on `C / X i`. The `comm` field of this
morphism of the canonical descent data expresses agreement on overlaps,
using the canonical repeated-restriction identifications. With fibre products,
its tests on arbitrary common refinements are equivalent to the tests on
`X i ×_U X j`. The coefficient universe contains the site and the index set.
`CommMonCat`-valued sheaves are precisely presheaves of commutative monoids
whose underlying set presheaves are sheaves: the forgetful functor preserves
and reflects the relevant limits. No log or finiteness conditions occur.

Proof:
1. Forget monoid operations and apply the morphism clause of
   `setSheafCoverDescent` (lem-pe-set-sheaf-cover-descent) to obtain the unique
   underlying natural map. By def-pur-localized-ringed-site, restriction means
   evaluation on the composite arrow into `U`.
2. For `V → U`, base-change the given cover to `V`. The restrictions of the
   image of a product and of the product of the images coincide, since every
   local map is a monoid homomorphism. The same holds for the identity.
   Separatedness of `B` gives the monoid equations globally. This uses the
   site axioms and sheaf equalizer of def-weil-pbc-sites-and-cohomology.
3. Naturality and the local structural-map equations show that `u ≫ β` and
   `α` agree after this covering. Separatedness of `R` proves their equality.
   Uniqueness follows from uniqueness of the underlying glued map in step 1.
4. If the local maps are invertible, their inverses agree on overlaps by
   uniqueness of inverses and satisfy the reversed structural-map equation.
   Apply lem-pe-set-sheaf-cover-descent again, now to these inverse maps;
   steps 2 and 3 show that their gluing is a monoid-sheaf map over `R`.
5. Both composites with `u` are identities locally, hence globally by
   separatedness of `A` and `B`. Thus the gluing is an isomorphism, and its
   inverse restricts to each specified local inverse. Empty covers, repeated
   indices, and noncancellative monoids require no change in the argument. -/
theorem monoidSheafMorphism_gluing
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) {I : Type w} (U : C)
    (X : I → C) (f : ∀ i, X i ⟶ U)
    (hcov : Sieve.ofArrows X f ∈ J U)
    (R A B : Sheaf (J.over U) CommMonCat.{max u v w})
    (α : A ⟶ R) (β : B ⟶ R)
    (localMap :
      ((J.pseudofunctorOver CommMonCat.{max u v w}).toDescentData f).obj A ⟶
        ((J.pseudofunctorOver CommMonCat.{max u v w}).toDescentData f).obj B)
    (hbase : ∀ i, localMap.hom i ≫
      (J.overMapPullback CommMonCat.{max u v w} (f i)).map β =
        (J.overMapPullback CommMonCat.{max u v w} (f i)).map α) :
    ∃ u : A ⟶ B,
      (u ≫ β = α ∧
        ((J.pseudofunctorOver CommMonCat.{max u v w}).toDescentData f).map u =
          localMap) ∧
      (∀ u' : A ⟶ B, u' ≫ β = α →
        ((J.pseudofunctorOver CommMonCat.{max u v w}).toDescentData f).map u' =
          localMap → u' = u) ∧
      (∀ hiso : ∀ i, IsIso (localMap.hom i),
        ∃ e : A ≅ B, e.hom = u ∧ e.inv ≫ α = β ∧
          ∀ i, (J.overMapPullback CommMonCat.{max u v w} (f i)).map e.inv =
            @CategoryTheory.inv _ _ _ _ (localMap.hom i) (hiso i)) := by
  let : (J.pseudofunctorOver CommMonCat.{max u v w}).IsPrestack J :=
    { isSheaf := fun M N ↦
        (Presheaf.isSheaf_of_iso_iff (monoidHomIso J M N)).1 (sheafHom M N).property }
  let D := (J.pseudofunctorOver CommMonCat.{max u v w}).toDescentData f
  let ff := (J.pseudofunctorOver CommMonCat.{max u v w}).fullyFaithfulToDescentData f hcov
  let u := ff.preimage localMap
  have hu : D.map u = localMap := ff.map_preimage localMap
  have hbase' : u ≫ β = α := by
    apply ff.map_injective
    rw [D.map_comp, hu]
    exact Pseudofunctor.DescentData.hom_ext hbase
  refine ⟨u, ⟨hbase', hu⟩, ?_, ?_⟩
  · intro u' _ hu'
    exact ff.map_injective (hu'.trans hu.symm)
  · intro hiso
    let := hiso
    let eD : D.obj A ≅ D.obj B :=
      Pseudofunctor.DescentData.isoMk (fun i ↦ asIso (localMap.hom i))
        (fun {_} q {_ _} f₁ f₂ hf₁ hf₂ ↦ localMap.comm q f₁ f₂ hf₁ hf₂)
    let e := ff.preimageIso eD
    have he : e.hom = u := rfl
    refine ⟨e, he, ?_, ?_⟩
    · rw [← hbase', ← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    · intro i
      have hi := congrArg (fun g ↦ g.hom i) (ff.map_preimage eD.inv)
      exact hi

end CategoryTheory
