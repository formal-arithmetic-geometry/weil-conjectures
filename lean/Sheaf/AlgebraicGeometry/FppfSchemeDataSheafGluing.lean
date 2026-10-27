/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NO, P1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-! # Functorial gluing of scheme descent data to fppf sheaves

Source: Stacks Project, Descent, Tag 02W5, left-to-right construction and the
quasi-inverse comparison; Sites, Tags 04TR and 04TQ
(blueprint: lem-trf-fppf-scheme-data-sheaf-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private noncomputable def slicePairEquiv
    {T U : Scheme.{u}} (f : U ⟶ T)
    (H : (Over T)ᵒᵖ ⥤ Type (u + 1)) (X : Over U)
    (r : ((Over.map f).op ⋙ H).RepresentableBy X) (V : Over T) :
    (V ⟶ (Over.map f).obj X) ≃
      (ULift.{u + 1} (V ⟶ Over.mk f) × H.obj (op V)) where
  toFun x := by
    let W : Over U := Over.mk (x.left ≫ X.hom)
    let a : V ⟶ (Over.map f).obj W := Over.homMk (𝟙 V.left) (by
      simpa [W, Category.assoc] using (Over.w x))
    exact ⟨ULift.up (Over.homMk (x.left ≫ X.hom) (by
      simpa [Category.assoc] using Over.w x)),
      H.map a.op (r.homEquiv (Over.homMk x.left (by rfl)))⟩
  invFun p := by
    let W : Over U := Over.mk p.1.down.left
    let a : (Over.map f).obj W ⟶ V := Over.homMk (𝟙 V.left) (by
      simpa [W] using (Over.w p.1.down).symm)
    let x : W ⟶ X := r.homEquiv.symm (H.map a.op p.2)
    exact Over.homMk x.left (by
      calc
        x.left ≫ (X.hom ≫ f) = (x.left ≫ X.hom) ≫ f := (Category.assoc ..).symm
        _ = p.1.down.left ≫ f := congrArg (fun g ↦ g ≫ f) (Over.w x)
        _ = V.hom := Over.w p.1.down)
  left_inv x := by
    let W : Over U := Over.mk (x.left ≫ X.hom)
    let a : V ⟶ (Over.map f).obj W := Over.homMk (𝟙 V.left) (by
      simpa [W, Category.assoc] using Over.w x)
    let b : (Over.map f).obj W ⟶ V := Over.homMk (𝟙 V.left) (by
      simpa [W, Category.assoc] using (Over.w x).symm)
    let y : W ⟶ X := Over.homMk x.left (by rfl)
    apply Over.OverMorphism.ext
    change (r.homEquiv.symm (H.map b.op (H.map a.op (r.homEquiv y)))).left = x.left
    have hid : b ≫ a = 𝟙 _ := by
      ext
      simp [a, b, W]
    have hs : H.map b.op (H.map a.op (r.homEquiv y)) = r.homEquiv y := by
      erw [← comp_apply, ← H.map_comp, ← op_comp, hid, op_id, H.map_id, id_apply]
    erw [hs, Equiv.symm_apply_apply]
    rfl
  right_inv p := by
    let W : Over U := Over.mk p.1.down.left
    let a : (Over.map f).obj W ⟶ V := Over.homMk (𝟙 V.left) (by
      simpa [W] using (Over.w p.1.down).symm)
    let x : W ⟶ X := r.homEquiv.symm (H.map a.op p.2)
    let W' : Over U := Over.mk (x.left ≫ X.hom)
    let k : W' ⟶ W := Over.homMk (𝟙 V.left) (by
      change 𝟙 _ ≫ p.1.down.left = x.left ≫ X.hom
      erw [Category.id_comp]
      exact (Over.w x).symm)
    let b : V ⟶ (Over.map f).obj W' := Over.homMk (𝟙 V.left) (by
      change 𝟙 _ ≫ ((x.left ≫ X.hom) ≫ f) = V.hom
      erw [Category.id_comp, Over.w x]
      exact Over.w p.1.down)
    apply Prod.ext
    · apply ULift.ext
      apply Over.OverMorphism.ext
      change x.left ≫ X.hom = p.1.down.left
      exact Over.w x
    · have hx : (Over.homMk x.left (by rfl) : W' ⟶ X) = k ≫ x := by
        ext
        change x.left = 𝟙 _ ≫ x.left
        exact (Category.id_comp _).symm
      change H.map b.op (r.homEquiv (X := W') (Over.homMk x.left (by rfl))) = p.2
      erw [hx, r.homEquiv_comp]
      change H.map b.op (H.map ((Over.map f).map k).op (r.homEquiv x)) = p.2
      erw [show r.homEquiv x = H.map a.op p.2 from r.homEquiv.apply_symm_apply _]
      erw [← comp_apply, ← H.map_comp, ← op_comp,
        ← comp_apply, ← H.map_comp, ← op_comp]
      have hid : b ≫ (Over.map f).map k ≫ a = 𝟙 V := by
        ext
        change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 V.left
        simp
      erw [hid, op_id, H.map_id, id_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem slicePairEquiv_naturality
    {T U : Scheme.{u}} (f : U ⟶ T)
    (H : (Over T)ᵒᵖ ⥤ Type (u + 1)) (X : Over U)
    (r : ((Over.map f).op ⋙ H).RepresentableBy X)
    {V V' : Over T} (g : V ⟶ V') (x : V' ⟶ (Over.map f).obj X) :
    slicePairEquiv f H X r V (g ≫ x) =
      (ULift.up (g ≫ (slicePairEquiv f H X r V' x).1.down),
        H.map g.op (slicePairEquiv f H X r V' x).2) := by
  apply Prod.ext
  · apply ULift.ext
    apply Over.OverMorphism.ext
    change (g.left ≫ x.left) ≫ X.hom = g.left ≫ (x.left ≫ X.hom)
    exact Category.assoc ..
  · let W : Over U := Over.mk (x.left ≫ X.hom)
    let W' : Over U := Over.mk ((g.left ≫ x.left) ≫ X.hom)
    let k : W' ⟶ W := Over.homMk g.left (by
      change g.left ≫ (x.left ≫ X.hom) = (g.left ≫ x.left) ≫ X.hom
      exact (Category.assoc ..).symm)
    let a : V' ⟶ (Over.map f).obj W := Over.homMk (𝟙 V'.left) (by
      simpa [W, Category.assoc] using Over.w x)
    let b : V ⟶ (Over.map f).obj W' := Over.homMk (𝟙 V.left) (by
      simpa [W', Category.assoc] using Over.w (g ≫ x))
    let y : W ⟶ X := Over.homMk x.left (by rfl)
    have hy : (Over.homMk (g.left ≫ x.left) (by rfl) : W' ⟶ X) = k ≫ y := by
      ext
      rfl
    change H.map b.op (r.homEquiv (X := W') (Over.homMk _ (by rfl))) =
      H.map g.op (H.map a.op (r.homEquiv y))
    erw [hy, r.homEquiv_comp]
    change H.map b.op (H.map ((Over.map f).map k).op (r.homEquiv y)) = _
    erw [← comp_apply, ← H.map_comp, ← op_comp,
      ← comp_apply, ← H.map_comp, ← op_comp]
    have h : b ≫ (Over.map f).map k = g ≫ a := by
      ext
      change 𝟙 _ ≫ g.left = g.left ≫ 𝟙 _
      simp
    erw [h]

set_option backward.isDefEq.respectTransparency false in
private theorem slicePairEquiv_map
    {T U : Scheme.{u}} (f : U ⟶ T)
    (H : (Over T)ᵒᵖ ⥤ Type (u + 1)) (X : Over U)
    (r : ((Over.map f).op ⋙ H).RepresentableBy X) (W : Over U) (x : W ⟶ X) :
    slicePairEquiv f H X r ((Over.map f).obj W) ((Over.map f).map x) =
      (ULift.up (Over.homMk W.hom), r.homEquiv x) := by
  apply Prod.ext
  · apply ULift.ext
    apply Over.OverMorphism.ext
    exact Over.w x
  · let W' : Over U := Over.mk (x.left ≫ X.hom)
    let k : W' ⟶ W := Over.homMk (𝟙 W.left) (by
      change 𝟙 _ ≫ W.hom = x.left ≫ X.hom
      rw [Category.id_comp]
      exact (Over.w x).symm)
    let a : (Over.map f).obj W ⟶ (Over.map f).obj W' :=
      Over.homMk (𝟙 W.left) (by
        change 𝟙 _ ≫ ((x.left ≫ X.hom) ≫ f) = W.hom ≫ f
        rw [Category.id_comp, Over.w x])
    have hx : (Over.homMk x.left (by rfl) : W' ⟶ X) = k ≫ x := by
      ext
      change x.left = 𝟙 _ ≫ x.left
      exact (Category.id_comp _).symm
    change H.map a.op (r.homEquiv (X := W') (Over.homMk _ (by rfl))) = r.homEquiv x
    erw [hx, r.homEquiv_comp]
    change H.map a.op (H.map ((Over.map f).map k).op (r.homEquiv x)) = _
    erw [← comp_apply, ← H.map_comp, ← op_comp]
    have hid : a ≫ (Over.map f).map k = 𝟙 _ := by
      ext
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 W.left
      simp
    erw [hid, op_id, H.map_id, id_apply]

private noncomputable def productRepresentation
    {T U : Scheme.{u}} (f : U ⟶ T)
    (H : (Over T)ᵒᵖ ⥤ Type (u + 1)) (X : Over U)
    (r : ((Over.map f).op ⋙ H).RepresentableBy X) :
    (Limits.prod (uliftYoneda.{u + 1}.obj (Over.mk f)) H).RepresentableBy
      ((Over.map f).obj X) :=
  let r' : (FunctorToTypes.prod (uliftYoneda.{u + 1}.obj (Over.mk f)) H).RepresentableBy
      ((Over.map f).obj X) :=
    { homEquiv {V} := slicePairEquiv f H X r V
      homEquiv_comp := slicePairEquiv_naturality f H X r }
  r'.ofIso (FunctorToTypes.binaryProductIso _ _).symm

private theorem productRepresentation_coordinates
    {T U : Scheme.{u}} (f : U ⟶ T)
    (H : (Over T)ᵒᵖ ⥤ Type (u + 1)) (X : Over U)
    (r : ((Over.map f).op ⋙ H).RepresentableBy X) (W : Over U) (x : W ⟶ X) :
    (prod.fst (X := uliftYoneda.{u + 1}.obj (Over.mk f)) (Y := H)).app
        (op ((Over.map f).obj W))
        ((productRepresentation f H X r).homEquiv ((Over.map f).map x)) =
      ULift.up (Over.homMk W.hom) ∧
    (prod.snd (X := uliftYoneda.{u + 1}.obj (Over.mk f)) (Y := H)).app
        (op ((Over.map f).obj W))
        ((productRepresentation f H X r).homEquiv ((Over.map f).map x)) =
      r.homEquiv x := by
  have h := slicePairEquiv_map f H X r W x
  constructor
  · change (prod.fst (X := uliftYoneda.{u + 1}.obj (Over.mk f)) (Y := H)).app _
      ((FunctorToTypes.binaryProductIso _ _).inv.app _
        (slicePairEquiv f H X r _ ((Over.map f).map x))) = _
    rw [FunctorToTypes.binaryProductIso_inv_comp_fst_apply]
    exact congrArg Prod.fst h
  · change (prod.snd (X := uliftYoneda.{u + 1}.obj (Over.mk f)) (Y := H)).app _
      ((FunctorToTypes.binaryProductIso _ _).inv.app _
        (slicePairEquiv f H X r _ ((Over.map f).map x))) = _
    rw [FunctorToTypes.binaryProductIso_inv_comp_snd_apply]
    exact congrArg Prod.snd h

private def localSheafFunctor
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    (f : ∀ i, U i ⟶ T) (i : I) :
    (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).DescentData f ⥤
      Sheaf (Scheme.fppfTopology.over (U i)) (Type (u + 1)) where
  obj D := D.obj i
  map g := g.hom i
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem liftAlongFullyFaithful
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ E) (A : D ⥤ E) [A.Full] [A.Faithful]
    (hF : ∀ X, A.essImage (F.obj X)) :
    ∃ G : C ⥤ D, Nonempty (G ⋙ A ≅ F) := by
  exact ⟨Functor.essImage.liftFunctor F A hF,
    ⟨Functor.essImage.liftFunctorCompIso F A hF⟩⟩

private theorem liftToFullSubcategory
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ E) (A : D ⥤ E) (G₀ : C ⥤ D) (e₀ : G₀ ⋙ A ≅ F)
    (P : ObjectProperty D) (h : ∀ X, P (G₀.obj X)) :
    ∃ G : C ⥤ P.FullSubcategory, Nonempty (G ⋙ P.ι ⋙ A ≅ F) := by
  refine ⟨P.lift G₀ h, ⟨?_⟩⟩
  exact (Functor.associator (P.lift G₀ h) P.ι A).symm ≪≫
    Functor.isoWhiskerRight (P.liftCompιIso G₀ h) A ≪≫ e₀

private theorem comparisonAlongFullyFaithful
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ E) [F.Full] [F.Faithful]
    (A : D ⥤ E) (G : C ⥤ D) (e : G ⋙ A ≅ F)
    (R : D ⥤ C) (r : R ⋙ F ≅ A) :
    ∃ ε : G ⋙ R ≅ 𝟭 C, ∀ X,
      F.map (ε.hom.app X) = r.hom.app (G.obj X) ≫ e.hom.app X := by
  let c : (G ⋙ R) ⋙ F ≅ (𝟭 C) ⋙ F :=
    Functor.associator G R F ≪≫ Functor.isoWhiskerLeft G r ≪≫ e ≪≫ F.leftUnitor.symm
  let ε : G ⋙ R ≅ 𝟭 C := Functor.fullyFaithfulCancelRight F c
  refine ⟨ε, ?_⟩
  intro X
  change F.map (F.preimage (c.hom.app X)) = _
  rw [F.map_preimage]
  simp [c, CategoryTheory.Functor.associator]

/-- Gluing scheme descent data gives a locally representable sheaf, with its specified
local comparisons, product representations, and natural comparison with any functor
obtained by choosing local representatives.

Source: Stacks Project, Descent, Tag 02W5; Sites, Tags 04TR and 04TQ
(blueprint: lem-trf-fppf-scheme-data-sheaf-gluing).

The components of `e` are the slice isomorphisms. Since they form an isomorphism of
sheaf descent data, they intertwine every transition, including repeated indices.
Naturality in the descent datum is precisely compatibility with local scheme maps.
The two projection equations specify the product representation `β`: its first
coordinate is the structure map and its second is the inverse slice comparison.
Every map over `T` is of the displayed form by taking its composite to `U i`.
Together with the transition compatibility of `e`, these equations identify the
coordinate-preserving overlap comparison with the given scheme transition by Yoneda.

For a representative-choosing functor `R`, `r` records its slice representations.
Its descent-morphism compatibility says that its overlaps preserve the sheaf coordinate;
its naturality says that its morphisms represent `id × v`. Conversely these conditions
on chosen product representations supply exactly such an `r` by taking fibres over
maps to `U i`. The last equation specifies the local components of `ε` as the
comparisons of these representations with `β`, rather than asserting an arbitrary
natural isomorphism.

Proof, following the eight steps of the node:
1. An fppf cover is fpqc: after base change to an affine open, use
   lem-pc-fppf-affine-refinement to get the finite affine refinement in
   def-weil-pbc-fpqc-covering. By lem-weil-pbc-fpqc-representable-descent,
   representables are sheaves. Uniqueness with target the base shows that glued maps
   remain over that base (def-weil-pbc-sites-and-cohomology).
2. On an overlap test scheme, send `x` to the second projection of the given scheme
   transition applied to `(x,a_j)`. The fibre-product universal property gives
   naturality and the base coordinate. The inverse transition gives the inverse map;
   the scheme cocycle gives the sheaf cocycle. Local datum morphisms commute with it
   (def-trf-scheme-cover-descent-datum and def-pc-fibre-product).
3. Apply lem-pe-set-sheaf-cover-descent on slices, using relocalization from
   def-pur-localized-ringed-site and the universes of def-weil-size-convention.
   This gives `G(D)` and the compatible local comparisons `e`.
4. Separate maps to the local scheme according to their composite to `U i`.
   Pair that composite with the inverse local comparison. Its inverse evaluates the
   local comparison on the sheaf coordinate. Naturality gives `β`, and each product
   is represented, so `G(D)` lies in the indicated full subcategory.
5. Conjugate the local maps by `e`. They agree on overlaps by step 2, hence glue
   uniquely by lem-pe-set-sheaf-cover-descent. Uniqueness proves identities and
   composition and gives the naturality of `e`.
6. On `(a_i,s,a_j)`, compatibility of `e` identifies the two local points by exactly
   the original transition. Yoneda (lem-pc-yoneda) makes this equality an equality of
   scheme maps, so the overlap comparison for `β` is the prescribed one.
7. For any `R,r`, compare its chosen representations with `β` using
   lem-pc-representable-unique. The comparisons are over `U i` since they preserve
   the first coordinate; they commute with transitions since both preserve the
   sheaf coordinate. They and their inverses give isomorphisms of scheme data.
8. The morphism formula of step 5 and the corresponding defining formula for `R`
   give naturality after cancelling the product representation and applying Yoneda.
   These are `ε` and the stated component equation. Empty schemes and the empty
   covering cause no exception: the latter forces an empty base, and the empty
   sheaf covering axiom forces the singleton section set. -/
theorem fppfSchemeDataSheafGluing
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u})
    (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T) :
    ∃ (G : SchemeCoverDescent f ⥤ (IsLocallyRepresentableFppfSheaf f).FullSubcategory)
      (e : G ⋙ (IsLocallyRepresentableFppfSheaf f).ι ⋙
          (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f ≅
        schemeCoverDescentForget f)
      (β : ∀ (D : SchemeCoverDescent f) (i : I),
        (Limits.prod (uliftYoneda.{u + 1}.obj (Over.mk (f i)))
          (G.obj D).obj.obj).RepresentableBy ((Over.map (f i)).obj (D.localScheme i))),
      (∀ (D : SchemeCoverDescent f) (i : I) (W : Over (U i))
        (x : W ⟶ D.localScheme i),
        (Limits.prod.fst (X := uliftYoneda.{u + 1}.obj (Over.mk (f i)))
          (Y := (G.obj D).obj.obj)).app (op ((Over.map (f i)).obj W))
            ((β D i).homEquiv ((Over.map (f i)).map x)) =
          ULift.up (Over.homMk W.hom) ∧
        (Limits.prod.snd (X := uliftYoneda.{u + 1}.obj (Over.mk (f i)))
          (Y := (G.obj D).obj.obj)).app (op ((Over.map (f i)).obj W))
            ((β D i).homEquiv ((Over.map (f i)).map x)) =
          ((e.inv.app D).hom i).hom.app (op W) ((D.representation i).homEquiv x)) ∧
      ∀ (R : (IsLocallyRepresentableFppfSheaf f).FullSubcategory ⥤ SchemeCoverDescent f)
        (r : R ⋙ schemeCoverDescentForget f ≅
          (IsLocallyRepresentableFppfSheaf f).ι ⋙
            (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f),
        ∃ ε : G ⋙ R ≅ 𝟭 (SchemeCoverDescent f),
          ∀ (D : SchemeCoverDescent f) (i : I),
            ((schemeCoverDescentForget f).map (ε.hom.app D)).hom i =
              (r.hom.app (G.obj D)).hom i ≫ (e.hom.app D).hom i := by
  classical
  let A := (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f
  obtain ⟨hobj, ⟨hA⟩⟩ := setSheafCoverDescent Scheme.fppfTopology T U f
    (Scheme.fppfPrecoverage.generate_mem_toGrothendieck hcov)
  have : A.Full := hA.full
  have : A.Faithful := hA.faithful
  let F := schemeCoverDescentForget f
  have : F.Full := (fullyFaithfulInducedFunctor
    (SchemeCoverDescentDatum.data (f := f))).full
  have : F.Faithful := (fullyFaithfulInducedFunctor
    (SchemeCoverDescentDatum.data (f := f))).faithful
  have hF : ∀ D, A.essImage (F.obj D) := by
    intro D
    obtain ⟨H, ⟨e⟩⟩ := hobj (F.obj D)
    exact ⟨H, ⟨e.symm⟩⟩
  obtain ⟨G₀, ⟨e₀⟩⟩ := liftAlongFullyFaithful F A hF
  let r : ∀ (D : SchemeCoverDescent f) (i : I),
      (((Over.map (f i)).op) ⋙ (G₀.obj D).obj).RepresentableBy (D.localScheme i) :=
    fun D i ↦ (D.representation i).ofIso
      ((sheafToPresheaf _ _).mapIso ((localSheafFunctor f i).mapIso (e₀.app D)).symm)
  have hloc : ∀ D, IsLocallyRepresentableFppfSheaf f (G₀.obj D) := by
    intro D i
    change (((Over.map (f i)).op) ⋙ (G₀.obj D).obj).IsRepresentable
    exact (r D i).isRepresentable
  obtain ⟨G, ⟨e⟩⟩ := liftToFullSubcategory F A G₀ e₀
    (IsLocallyRepresentableFppfSheaf f) hloc
  let rG : ∀ (D : SchemeCoverDescent f) (i : I),
      (((Over.map (f i)).op) ⋙ (G.obj D).obj.obj).RepresentableBy (D.localScheme i) :=
    fun D i ↦ (D.representation i).ofIso
      ((sheafToPresheaf _ _).mapIso ((localSheafFunctor f i).mapIso (e.app D)).symm)
  refine ⟨G, e, fun D i ↦ productRepresentation (f i) (G.obj D).obj.obj
    (D.localScheme i) (rG D i), ?_, ?_⟩
  · intro D i W x
    have h := productRepresentation_coordinates (f i) (G.obj D).obj.obj
      (D.localScheme i) (rG D i) W x
    refine ⟨h.1, h.2.trans ?_⟩
    rfl
  · intro R rR
    obtain ⟨ε, hε⟩ := comparisonAlongFullyFaithful F
      ((IsLocallyRepresentableFppfSheaf f).ι ⋙ A) G e R rR
    refine ⟨ε, ?_⟩
    intro D i
    exact congrArg (fun z ↦ z.hom i) (hε D)

end AlgebraicGeometry
