/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.UnramifiedMorphism

/-! # Open substacks and unramified relative diagonals

Source: Stacks Project, stacks-morphisms.tex, Tags 0DSM and 06N3; stacks-properties.tex,
Tag 04YM (open substacks); spaces-morphisms.tex, unramified morphisms
(blueprint: def-sfb-open-moduli-substack).

The subcategory is full and closed under pullback. Every scheme test is represented
by an actual open immersion, compatible with the test projection. The diagonal test
retains both projections to the product over the original base scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ v₂ v₃ w₁ w₂ w₃

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The full category selected by a predicate, with its original projection.
Source: Stacks, open substacks (blueprint: def-sfb-open-moduli-substack). -/
def fullModuliSubcategory {S : Scheme.{u}} (F : BasedCategory.{v₁, w₁} (Over S))
    (P : F.obj → Prop) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (ObjectProperty.ι P ⋙ F.p)

/-- The actual full inclusion over the base category of schemes.
Source: Stacks, open substacks (blueprint: def-sfb-open-moduli-substack). -/
def fullModuliInclusion {S : Scheme.{u}} (F : BasedCategory.{v₁, w₁} (Over S))
    (P : F.obj → Prop) : BasedFunctor (fullModuliSubcategory F P) F where
  toFunctor := ObjectProperty.ι P
  w := rfl

/-- Open substacks as full subcategories stable under every cartesian pullback;
every scheme test is an open subscheme, including compatibility of its projection.
Source: Stacks, stacks-properties.tex, Tag 04YM; stacks-morphisms.tex, Tag 0DSM
(blueprint: def-sfb-open-moduli-substack). -/
structure OpenModuliSubstack {S : Scheme.{u}} (F : BasedCategory.{v₁, w₁} (Over S)) where
  fibred : IsFibredInGroupoids F
  property : F.obj → Prop
  pullback : ∀ {x y : F.obj} (_f : x ⟶ y), property y → property x
  open_pullback : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
    ∃ (W : Over S) (j : W ⟶ T), IsOpenImmersion j.left ∧
      ∃ e : BasedFunctor (discreteModuli (yoneda.obj W))
          (moduliTwoFiberProduct t (fullModuliInclusion F property)),
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso
            (e.comp (moduliTwoFiberFst t (fullModuliInclusion F property)))
            (discreteModuliMap (yoneda.map j)))

/-- The full substack with its projection to schemes.
Source: Stacks, open substacks (blueprint: def-sfb-open-moduli-substack). -/
def OpenModuliSubstack.category {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} (U : OpenModuliSubstack F) :
    BasedCategory (Over S) :=
  fullModuliSubcategory F U.property

/-- Containment is membership implication for the two full substacks.
Source: Stacks, open substacks (blueprint: def-sfb-open-moduli-substack). -/
def OpenModuliSubstack.IsContainedIn {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} (U V : OpenModuliSubstack F) : Prop :=
  ∀ x : F.obj, U.property x → V.property x

/-- The second comma projection also lies over the original base.
Source: Stacks 003R, 2-fibre products (blueprint: def-sfb-open-moduli-substack).
Proof: the comparison arrow in every comma object lies over an identity. Its source
and target therefore have equal base objects, and its naturality square gives equality
of the two base arrows. These equalities are exactly equality of the projection functors. -/
theorem moduliTwoFiberSnd_projection {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} (f : BasedFunctor F H) (g : BasedFunctor G H) :
    (ObjectProperty.ι (fun x : Comma f.toFunctor g.toFunctor ↦
      IsIso x.hom ∧ H.p.IsHomLift (𝟙 (F.p.obj x.left)) x.hom) ⋙
        Comma.snd f.toFunctor g.toFunctor) ⋙ G.p = (moduliTwoFiberProduct f g).p := by
  let P : ObjectProperty (Comma f.toFunctor g.toFunctor) := fun x ↦
    IsIso x.hom ∧ H.p.IsHomLift (𝟙 (F.p.obj x.left)) x.hom
  let α := Functor.whiskerRight
    (Functor.whiskerLeft (ObjectProperty.ι P) (Comma.natTrans f.toFunctor g.toFunctor)) H.p
  have hobj (x : P.FullSubcategory) :
      H.p.obj (f.obj x.obj.left) = H.p.obj (g.obj x.obj.right) := by
    have := x.property.2
    exact (IsHomLift.domain_eq H.p (𝟙 (F.p.obj x.obj.left)) x.obj.hom).trans
      (IsHomLift.codomain_eq H.p (𝟙 (F.p.obj x.obj.left)) x.obj.hom).symm
  have happ (x : P.FullSubcategory) : α.app x = eqToHom (hobj x) := by
    have := x.property.2
    simpa [α, Category.assoc] using
      (IsHomLift.fac' H.p (𝟙 (F.p.obj x.obj.left)) x.obj.hom)
  have (x : P.FullSubcategory) : IsIso (α.app x) := by
    rw [happ]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have heq := Functor.ext_of_iso (asIso α) hobj happ
  simpa only [Functor.assoc, f.w, g.w, moduliTwoFiberProduct,
    BasedCategory.ofFunctor] using heq.symm

/-- The second projection from the actual 2-fibre product.
Source: Stacks 003R (blueprint: def-sfb-open-moduli-substack). -/
def moduliTwoFiberSnd {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)} (f : BasedFunctor F H) (g : BasedFunctor G H) :
    BasedFunctor (moduliTwoFiberProduct f g) G where
  toFunctor := ObjectProperty.ι _ ⋙ Comma.snd f.toFunctor g.toFunctor
  w := moduliTwoFiberSnd_projection f g

/-- Unramifiedness on all etale scheme charts of a map from a space to a scheme.
Source: Stacks, Morphisms of Spaces, unramified morphisms
(blueprint: def-sfb-open-moduli-substack). -/
def SpaceMapIsUnramified {S : Scheme.{u}} (Z : AlgebraicSpace S) (T : Over S)
    (a : Z.obj.obj ⟶ yoneda.obj T) : Prop :=
  ∀ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
    IsUnramified ((yoneda.preimage (b ≫ a)).left)

/-- The relative diagonal is unramified: both scheme tests are retained, and the
representing space maps to their product over `S` with the specified two projections.
Source: Stacks, stacks-morphisms.tex, Tags 0DSM and 06N3
(blueprint: def-sfb-open-moduli-substack). -/
def HasUnramifiedModuliDiagonal {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  ∀ (T U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
      (b : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj (T ⨯ U)),
      SpaceMapIsUnramified Z (T ⨯ U) p ∧
      ∃ e : BasedFunctor (discreteModuli Z.obj.obj) (moduliTwoFiberProduct a b),
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst a b))
            (discreteModuliMap (p ≫ yoneda.map (Limits.prod.fst : T ⨯ U ⟶ T)))) ∧
          Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberSnd a b))
            (discreteModuliMap (p ≫ yoneda.map (Limits.prod.snd : T ⨯ U ⟶ U))))

end CategoryTheory
