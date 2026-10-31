/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.CategoryTheory.SetSheafCoverDescent
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Products

/-! # The fully faithful functor of local representing schemes

Source: Stacks Project, Descent, Tag 02W5, the right-to-left construction and the
following remark; Sites, Tag 04TQ, gluing morphisms
(blueprint: lem-trf-fppf-local-representations-fully-faithful).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def productCoordinates
    {C : Type v} [Category.{w} C] (F G : C ⥤ Type u) (W : C) :
    (prod F G).obj W ≃ F.obj W × G.obj W :=
  ((PreservesLimitPair.iso ((evaluation C _).obj W) F G) ≪≫
    Types.binaryProductIso _ _).toEquiv

private theorem productCoordinates_fst
    {C : Type v} [Category.{w} C] (F G : C ⥤ Type u) (W : C) (x : (prod F G).obj W) :
    (productCoordinates F G W x).1 = (prod.fst (X := F) (Y := G)).app W x := by
  simp only [productCoordinates, Iso.toEquiv, Iso.trans_hom]
  simpa using ConcreteCategory.congr_hom
    (prodComparison_fst ((evaluation C _).obj W) F G) x

private theorem productCoordinates_snd
    {C : Type v} [Category.{w} C] (F G : C ⥤ Type u) (W : C) (x : (prod F G).obj W) :
    (productCoordinates F G W x).2 = (prod.snd (X := F) (Y := G)).app W x := by
  simp only [productCoordinates, Iso.toEquiv, Iso.trans_hom]
  simpa using ConcreteCategory.congr_hom
    (prodComparison_snd ((evaluation C _).obj W) F G) x

private theorem sliceRepresentation
    {T V : Scheme.{u}} (f : V ⟶ T) (F : (Over T)ᵒᵖ ⥤ Type (u + 1))
    (X : Over T) (a : (prod (uliftYoneda.{u + 1}.obj (Over.mk f)) F).RepresentableBy X) :
    ∃ (p : X.left ⟶ V) (q : (Over.map f).obj (Over.mk p) ≅ X)
      (b : ((Over.map f).op ⋙ F).RepresentableBy (Over.mk p)),
      q.hom.left = 𝟙 X.left ∧
      (∀ (W : Over T) (x : W ⟶ X),
        ((prod.fst (X := uliftYoneda.{u + 1}.obj (Over.mk f)) (Y := F)).app (op W)
          (a.homEquiv x)).down.left = x.left ≫ p) ∧
      (∀ (W : Over V) (x : W ⟶ Over.mk p),
        (prod.snd (X := uliftYoneda.{u + 1}.obj (Over.mk f)) (Y := F)).app
          (op ((Over.map f).obj W))
          (a.homEquiv ((Over.map f).map x ≫ q.hom)) = b.homEquiv x) := by
  let A := uliftYoneda.{u + 1}.obj (Over.mk f)
  let d : ∀ W : Over T, (W ⟶ X) ≃ ULift.{u + 1} (W ⟶ Over.mk f) × F.obj (op W) :=
    fun W ↦ a.homEquiv.trans (productCoordinates A F (op W))
  have dfst (W : Over T) (x : W ⟶ X) :
      (d W x).1 = (prod.fst (X := A) (Y := F)).app (op W) (a.homEquiv x) :=
    productCoordinates_fst A F (op W) _
  have dsnd (W : Over T) (x : W ⟶ X) :
      (d W x).2 = (prod.snd (X := A) (Y := F)).app (op W) (a.homEquiv x) :=
    productCoordinates_snd A F (op W) _
  have dn₁ {W Z : Over T} (x : W ⟶ Z) (y : Z ⟶ X) :
      (d W (x ≫ y)).1.down = x ≫ (d Z y).1.down := by
    rw [dfst, dfst, a.homEquiv_comp]
    exact congrArg ULift.down
      (ConcreteCategory.congr_hom ((prod.fst (X := A) (Y := F)).naturality x.op)
        (a.homEquiv y))
  have dn₂ {W Z : Over T} (x : W ⟶ Z) (y : Z ⟶ X) :
      (d W (x ≫ y)).2 = F.map x.op (d Z y).2 := by
    rw [dsnd, dsnd, a.homEquiv_comp]
    exact (ConcreteCategory.congr_hom
      ((prod.snd (X := A) (Y := F)).naturality x.op) (a.homEquiv y))
  -- Evaluate the first coordinate on the identity, as in the Yoneda inverse.
  let p₀ : X ⟶ Over.mk f := (d X (𝟙 X)).1.down
  let p := p₀.left
  have first (W : Over T) (x : W ⟶ X) : (d W x).1.down = x ≫ p₀ := by
    simpa only [Category.comp_id] using dn₁ x (𝟙 X)
  let q : (Over.map f).obj (Over.mk p) ≅ X :=
    Over.isoMk (Iso.refl _) (by simpa [p] using (Over.w p₀).symm)
  let liftMap (W : Over V) (x : W ⟶ Over.mk p) : (Over.map f).obj W ⟶ X :=
    (Over.map f).map x ≫ q.hom
  have lift_first (W : Over V) (x : W ⟶ Over.mk p) :
      (d _ (liftMap W x)).1.down = Over.homMk W.hom := by
    rw [first]
    apply Over.OverMorphism.ext
    simpa [liftMap, q, p] using Over.w x
  -- Invert the product representation at the prescribed base coordinate.
  let invMap (W : Over V) (y : F.obj (op ((Over.map f).obj W))) : W ⟶ Over.mk p :=
    Over.homMk (d _ |>.symm (⟨Over.homMk W.hom⟩, y)).left (by
      have h := first _ ((d _).symm (⟨Over.homMk W.hom⟩, y))
      rw [Equiv.apply_symm_apply] at h
      exact congrArg Over.Hom.left h.symm)
  have lift_inv (W : Over V) (y : F.obj (op ((Over.map f).obj W))) :
      liftMap W (invMap W y) = (d _).symm (⟨Over.homMk W.hom⟩, y) := by
    apply Over.OverMorphism.ext
    simp [liftMap, invMap, q]
  let b : ((Over.map f).op ⋙ F).RepresentableBy (Over.mk p) :=
    { homEquiv := fun {W} ↦
        { toFun := fun x ↦ (d _ (liftMap W x)).2
          invFun := invMap W
          left_inv := fun x ↦ by
            apply Over.OverMorphism.ext
            have h : (⟨Over.homMk W.hom⟩, (d _ (liftMap W x)).2) =
                d _ (liftMap W x) := by
              apply Prod.ext
              · exact congrArg ULift.up (lift_first W x).symm
              · rfl
            change ((d ((Over.map f).obj W)).symm _).left = x.left
            rw [h, Equiv.symm_apply_apply]
            simp [liftMap, q]
          right_inv := fun y ↦ by
            change (d _ (liftMap W (invMap W y))).2 = y
            rw [lift_inv, Equiv.apply_symm_apply] }
      homEquiv_comp := fun {W Z} x y ↦ by
        change (d _ (liftMap W (x ≫ y))).2 = F.map _ (d _ (liftMap Z y)).2
        have h : liftMap W (x ≫ y) = (Over.map f).map x ≫ liftMap Z y := by
          simp [liftMap]
        rw [h, dn₂]
        rfl }
  refine ⟨p, q, b, rfl, ?_, ?_⟩
  · intro W x
    rw [← dfst]
    exact congrArg Over.Hom.left (first W x)
  · intro W x
    exact (dsnd _ (liftMap W x)).symm

/-- Chosen product representations give the fully faithful scheme-descent functor.
Source: Stacks Project, Descent, Tag 02W5 and its following remark; Sites, Tag 04TQ
(blueprint: lem-trf-fppf-local-representations-fully-faithful).

The `p` are the first projections. The identity-on-schemes comparisons `q` retain
exactly the chosen representing schemes `X`. The representations `b` are the slice
bijections, including naturality and both inverse identities. The two product-projection
formulas identify them with the fibres of `alpha`; conversely they reconstruct `alpha`
by taking the disjoint union over maps into `U i`.

The comparison `e` identifies the underlying descent functor, including transitions and
maps, with sectionwise restriction. Its compatibility with `b` specifies the coordinates:
on overlaps the transition fixes both base maps and the middle sheaf section; on maps
it acts by the given sheaf map on that middle coordinate. Finally, bijectivity on Hom,
unique lifting of compatible local isomorphisms, and unique lifting of natural families
are stated explicitly.

Proof:
1. Apply Yoneda to the first projection of each product representation to obtain `p`.
   Its fibre at a map into `U i` is the bijection `b`. Naturality follows from that of
   `alpha`. Conversely send a map `x` to `(p x, b x)`; the inverse sends `(a,s)` to
   the inverse of the fibre bijection over `a`. These formulas are inverse and natural.
2. On a double overlap both products represent triples `(a_i,s,a_j)`. Yoneda supplies
   the comparison preserving these coordinates. On triple overlaps both composites
   fix `(a_i,s,a_j,a_k)`, so Yoneda gives the cocycle and the repeated-index identities.
3. Conjugate `id × z` by the chosen representations to define each local scheme map.
   Its coordinates are `(a_i,s,a_j) ↦ (a_i,z(s),a_j)`. Thus it respects transitions;
   Yoneda injectivity gives the identity and composition laws. This constructs `R`
   and the compatible natural comparison `e` with ordinary sheaf restriction.
4. Conversely a compatible family of local scheme maps gives maps of the restricted
   sheaves using `b`. The descent square says their middle coordinates agree on each
   double slice. Apply Sites Tag 04TQ to glue them uniquely to a global sheaf map.
   Its image under `R` is the given family by Yoneda. Uniqueness also gives faithfulness.
5. Glue inverse local isomorphisms as well. Faithfulness and functoriality show that
   the two global maps are inverse and unique. For diagrams glue each component;
   each naturality square holds because its restrictions agree and gluing is unique.
No effectivity, separatedness, or nonempty-cover hypothesis is needed. -/
theorem fppfLocalRepresentationsFullyFaithful
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u})
    (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T)
    (X : (IsLocallyRepresentableFppfSheaf f).FullSubcategory → I → Over T)
    (alpha : ∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I),
      (prod (uliftYoneda.{u + 1}.obj (Over.mk (f i))) H.obj.obj).RepresentableBy (X H i)) :
    ∃ (p : ∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I),
        (X H i).left ⟶ U i)
      (q : ∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I),
        (Over.map (f i)).obj (Over.mk (p H i)) ≅ X H i)
      (b : ∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I),
        Functor.RepresentableBy
          (((Scheme.fppfTopology.overMapPullback (Type (u + 1)) (f i)).obj H.obj).obj)
          (Over.mk (p H i)))
      (R : (IsLocallyRepresentableFppfSheaf f).FullSubcategory ⥤ SchemeCoverDescent f)
      (localEq : ∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I),
        (R.obj H).localScheme i = Over.mk (p H i))
      (e : R ⋙ schemeCoverDescentForget f ≅
        (IsLocallyRepresentableFppfSheaf f).ι ⋙
          (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f),
      (∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I),
        (q H i).hom.left = 𝟙 (X H i).left) ∧
      (∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I)
        (W : Over T) (x : W ⟶ X H i),
        ((prod.fst (X := uliftYoneda.{u + 1}.obj (Over.mk (f i))) (Y := H.obj.obj)).app (op W)
          ((alpha H i).homEquiv x)).down.left = x.left ≫ p H i) ∧
      (∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I)
        (W : Over (U i)) (x : W ⟶ Over.mk (p H i)),
        (prod.snd (X := uliftYoneda.{u + 1}.obj (Over.mk (f i))) (Y := H.obj.obj)).app
          (op ((Over.map (f i)).obj W))
          ((alpha H i).homEquiv ((Over.map (f i)).map x ≫ (q H i).hom)) =
            (b H i).homEquiv x) ∧
      (∀ (H : (IsLocallyRepresentableFppfSheaf f).FullSubcategory) (i : I)
        (W : Over (U i)) (x : W ⟶ (R.obj H).localScheme i),
        (((e.hom.app H).hom i).hom.app (op W))
          (((R.obj H).representation i).homEquiv x) =
            (b H i).homEquiv (x ≫ eqToHom (localEq H i))) ∧
      (∀ H K : (IsLocallyRepresentableFppfSheaf f).FullSubcategory,
        Function.Bijective (R.map : (H ⟶ K) → (R.obj H ⟶ R.obj K))) ∧
      (∀ (H K : (IsLocallyRepresentableFppfSheaf f).FullSubcategory)
        (c : R.obj H ≅ R.obj K), ∃! z : H ≅ K, R.mapIso z = c) ∧
      (∀ (J : Type v) [Category.{w} J]
        (A B : J ⥤ (IsLocallyRepresentableFppfSheaf f).FullSubcategory)
        (c : A ⋙ R ≅ B ⋙ R), ∃! z : A ≅ B, Functor.isoWhiskerRight z R = c) := by
  classical
  choose p q b hq hp hb using fun H i ↦
    sliceRepresentation (f i) H.obj.obj (X H i) (alpha H i)
  let D := (IsLocallyRepresentableFppfSheaf f).ι ⋙
    (Scheme.fppfTopology.pseudofunctorOver (Type (u + 1))).toDescentData f
  -- The existing sheaf descent datum retains the transitions and their cocycle.
  let R : (IsLocallyRepresentableFppfSheaf f).FullSubcategory ⥤ SchemeCoverDescent f :=
    { obj := fun H ↦
        { data := D.obj H
          localScheme := fun i ↦ Over.mk (p H i)
          representation := b H }
      map := fun z ↦ InducedCategory.homMk (D.map z) }
  have hcov' : Sieve.ofArrows U f ∈ Scheme.fppfTopology T :=
    Scheme.fppfPrecoverage.generate_mem_toGrothendieck hcov
  obtain ⟨hD⟩ := (setSheafCoverDescent Scheme.fppfTopology T U f hcov').2
  have hL : D.FullyFaithful := (IsLocallyRepresentableFppfSheaf f).fullyFaithfulι.comp hD
  let : (schemeCoverDescentForget f).Faithful :=
    (fullyFaithfulInducedFunctor (SchemeCoverDescentDatum.data (f := f))).faithful
  have hR : R.FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    (G := schemeCoverDescentForget f) hL
  refine ⟨p, q, b, R, (fun _ _ ↦ rfl), Iso.refl D, hq, hp, hb, ?_,
    hR.map_bijective, ?_, ?_⟩
  · intro H i W x
    rfl
  · intro H K c
    exact ⟨hR.isoEquiv.symm c, hR.isoEquiv.apply_symm_apply c,
      fun z hz ↦ hR.isoEquiv.injective (hz.trans (hR.isoEquiv.apply_symm_apply c).symm)⟩
  · intro J _ A B c
    let hW := hR.whiskeringRight J
    exact ⟨hW.isoEquiv.symm c, hW.isoEquiv.apply_symm_apply c,
      fun z hz ↦ hW.isoEquiv.injective (hz.trans (hW.isoEquiv.apply_symm_apply c).symm)⟩

end AlgebraicGeometry
