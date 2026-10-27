/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.FiniteTypeQuasiCoherentSubalgebras
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ModuleDirectedColimitFinitePresentation
import Sheaf.AlgebraicGeometry.FiniteTypeSubalgebraMultiplicationImage
import Sheaf.AlgebraicGeometry.SymmetricImagesModuleColimit

/-! # Quasi-coherent algebras as directed colimits of finite type subalgebras

Source: Stacks Project, Properties, Lemma 05JT
(blueprint: lem-weil-pbc-algebra-directed-colimit-finite-type).
-/

@[expose] public section

universe uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- A directed union of subrings is a colimit, even for a large indexing preorder.
private noncomputable def ringUnionIsColimit
    {I : Type*} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {F : I ⥤ CommRingCat.{uC}} (c : Cocone F)
    (hsurj : ∀ a : c.pt, ∃ i x, c.ι.app i x = a)
    (hinj : ∀ i, Function.Injective (c.ι.app i)) : IsColimit c := by
  classical
  let hc := Types.FilteredColimit.isColimitOf' (F ⋙ CategoryTheory.forget CommRingCat)
    ((CategoryTheory.forget CommRingCat).mapCocone c)
    (fun a ↦ by obtain ⟨i, x, hx⟩ := hsurj a; exact ⟨i, x, hx.symm⟩)
    (fun i x y h ↦ ⟨i, 𝟙 i, by simpa using hinj i h⟩)
  let g (t : Cocone F) : c.pt → t.pt :=
    hc.desc ((CategoryTheory.forget CommRingCat).mapCocone t)
  have hg (t : Cocone F) (i : I) (x : F.obj i) :
      g t (c.ι.app i x) = t.ι.app i x :=
    ConcreteCategory.congr_hom (hc.fac ((CategoryTheory.forget CommRingCat).mapCocone t) i) x
  let lift (t : Cocone F) : c.pt ⟶ t.pt := CommRingCat.ofHom
    { toFun := g t
      map_one' := by
        let i : I := Classical.arbitrary I
        have h := hg t i 1
        change g t ((c.ι.app i).hom 1) = (t.ι.app i).hom 1 at h
        simpa only [map_one] using h
      map_zero' := by
        let i : I := Classical.arbitrary I
        have h := hg t i 0
        change g t ((c.ι.app i).hom 0) = (t.ι.app i).hom 0 at h
        simpa only [map_zero] using h
      map_add' := by
        intro a b
        obtain ⟨i, x, rfl⟩ := hsurj a
        obtain ⟨j, y, rfl⟩ := hsurj b
        obtain ⟨k, hi, hj⟩ := directed_of (· ≤ ·) i j
        have hx := ConcreteCategory.congr_hom (c.w (homOfLE hi)) x
        have hy := ConcreteCategory.congr_hom (c.w (homOfLE hj)) y
        change c.ι.app k (F.map (homOfLE hi) x) = c.ι.app i x at hx
        change c.ι.app k (F.map (homOfLE hj) y) = c.ι.app j y at hy
        rw [← hx, ← hy]
        change g t ((c.ι.app k).hom _ + (c.ι.app k).hom _) = _
        rw [← map_add, hg]
        change (t.ι.app k).hom (_ + _) = _
        rw [map_add, hg, hg]
      map_mul' := by
        intro a b
        obtain ⟨i, x, rfl⟩ := hsurj a
        obtain ⟨j, y, rfl⟩ := hsurj b
        obtain ⟨k, hi, hj⟩ := directed_of (· ≤ ·) i j
        have hx := ConcreteCategory.congr_hom (c.w (homOfLE hi)) x
        have hy := ConcreteCategory.congr_hom (c.w (homOfLE hj)) y
        change c.ι.app k (F.map (homOfLE hi) x) = c.ι.app i x at hx
        change c.ι.app k (F.map (homOfLE hj) y) = c.ι.app j y at hy
        rw [← hx, ← hy]
        change g t ((c.ι.app k).hom _ * (c.ι.app k).hom _) = _
        rw [← map_mul, hg]
        change (t.ι.app k).hom (_ * _) = _
        rw [map_mul, hg, hg] }
  refine ⟨lift, ?_, ?_⟩
  · intro t i
    ext x
    exact hg t i x
  · intro t m hm
    ext a
    obtain ⟨i, x, rfl⟩ := hsurj a
    exact (ConcreteCategory.congr_hom (hm i) x).trans (hg t i x).symm

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-coherent algebra on a quasi-compact quasi-separated scheme is the directed
colimit, in all commutative algebra sheaves, of its finite type quasi-coherent subalgebras.
Every affine section belongs to one of these subalgebras.
Source: Stacks Project, Properties, Lemma 05JT
(blueprint: lem-weil-pbc-algebra-directed-colimit-finite-type).

Proof:
1. Apply the directed finite-presentation module theorem to the underlying module.
   The symmetric-images theorem supplies finite type quasi-coherent subalgebras covering
   every affine section. Its nonempty indexing set also supplies a subalgebra when X is empty.
2. The multiplication-image theorem supplies an upper bound for any pair of subalgebras.
3. Form the cocone with vertex A and the subobject arrows as legs. On every affine open,
   these arrows are injective and jointly surjective. The filtered-colimit criterion for
   types gives the underlying universal map. Moving two representatives to a common stage
   proves that this map preserves addition and multiplication; any stage gives 0 and 1.
   Hence this is a colimit of rings, without a smallness assumption on the subobject index.
4. The affine universal maps commute with restrictions: precompose with each inclusion,
   use the colimit factorization equations, and apply naturality of the given cocone legs.
   Extend this compatible family to a ring-sheaf map by restrictHomEquivHom on the affine
   basis. It respects the structure sheaf because it does so after factoring through any
   one subalgebra. The basis-extension equation proves factorization through every leg;
   affine ring-colimit uniqueness and basis hom_ext prove uniqueness of the algebra map.
   This constructs IsColimit directly for the inclusion cocone. -/
theorem CommAlgebraSheaf.directed_colimit_finiteType
    (X : Scheme.{uC}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : X.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent) :
    (Nonempty A.finiteTypeQuasiCoherentSubalgebras ∧
      Directed (· ≤ ·) (fun B : A.finiteTypeQuasiCoherentSubalgebras ↦ B)) ∧
    (∃ c : Cocone A.finiteTypeQuasiCoherentSubalgebraDiagram,
      ∃ h : c.pt = A, Nonempty (IsColimit c) ∧
        ∀ B : A.finiteTypeQuasiCoherentSubalgebras,
          c.ι.app B ≫ eqToHom h = Subobject.arrow B.val) ∧
    (∀ (U : X.Opens), IsAffineOpen U → ∀ a : A.right.obj.obj (op U),
      ∃ B : A.finiteTypeQuasiCoherentSubalgebras,
        ∃ b : (B.val : X.CommAlgebraSheaf).right.obj.obj (op U),
          (Subobject.arrow B.val).right.hom.app (op U) b = a) := by
  classical
  let : A.toModule.IsQuasicoherent := hA
  obtain ⟨I, hI, hne, hd, F, hF, φ, ⟨hc⟩⟩ :=
    Modules.exists_directedColimit_finitePresentation X A.toModule
  obtain ⟨_, ψ, C, hC, hcover⟩ :=
    CommAlgebraSheaf.symmetricImagesModuleColimit X A hA I F hF φ hc
  have hne' : Nonempty A.finiteTypeQuasiCoherentSubalgebras := ⟨C (Classical.choice hne)⟩
  have hd' : Directed (· ≤ ·) (fun B : A.finiteTypeQuasiCoherentSubalgebras ↦ B) := by
    intro B₁ B₂
    obtain ⟨μ, _, _, B, _, h₁, h₂, _⟩ :=
      CommAlgebraSheaf.finiteType_subalgebra_multiplication_image A B₁ B₂
    exact ⟨B, h₁, h₂⟩
  have hcover' : ∀ (U : X.Opens), IsAffineOpen U → ∀ a : A.right.obj.obj (op U),
      ∃ B : A.finiteTypeQuasiCoherentSubalgebras,
        ∃ b : (B.val : X.CommAlgebraSheaf).right.obj.obj (op U),
          (Subobject.arrow B.val).right.hom.app (op U) b = a := by
    intro U hU a
    obtain ⟨i, x, _, _, b, hb⟩ := hcover U hU a
    exact ⟨C i, b, hb⟩
  refine ⟨⟨hne', hd'⟩, ?_, hcover'⟩
  let : Nonempty A.finiteTypeQuasiCoherentSubalgebras := hne'
  let : IsDirected A.finiteTypeQuasiCoherentSubalgebras (· ≤ ·) := ⟨hd'⟩
  let D := A.finiteTypeQuasiCoherentSubalgebraDiagram
  let c : Cocone D :=
    { pt := A
      ι :=
        { app := fun B ↦ Subobject.arrow B.val
          naturality := by
            intro B B' f
            exact (Subobject.underlying_arrow
              ((show Monotone (fun B : A.finiteTypeQuasiCoherentSubalgebras ↦ B.val)
                from fun _ _ h ↦ h).functor.map f)).trans (Category.comp_id _).symm } }
  let E (U : X.Opens) := Under.forget X.sheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat ⋙
      (evaluation X.Opensᵒᵖ CommRingCat).obj (op U)
  have hinj (B : A.finiteTypeQuasiCoherentSubalgebras) (U : X.Opens) :
      Function.Injective ((Subobject.arrow B.val).right.hom.app (op U)) := by
    have : Mono (Subobject.arrow B.val).right := Under.mono_right_of_mono _
    have : Mono (Subobject.arrow B.val).right.hom :=
      inferInstanceAs (Mono ((sheafToPresheaf _ _).map (Subobject.arrow B.val).right))
    exact ConcreteCategory.injective_of_mono_of_preservesPullback _
  let hU (U : X.Opens) (h : IsAffineOpen U) : IsColimit ((E U).mapCocone c) :=
    ringUnionIsColimit _ (hcover' U h) (fun B ↦ hinj B U)
  let basis : X.affineOpens → X.Opens := Subtype.val
  have hb : TopologicalSpace.Opens.IsBasis (Set.range basis) := by
    simpa [basis, Subtype.range_coe_subtype] using X.isBasis_affineOpens
  let α (t : Cocone D) : (inducedFunctor basis).op ⋙ A.right.obj ⟶
      (inducedFunctor basis).op ⋙ t.pt.right.obj :=
    { app := fun U ↦ (hU U.unop.val U.unop.property).desc ((E U.unop.val).mapCocone t)
      naturality := by
        intro U V f
        apply (hU U.unop.val U.unop.property).hom_ext
        intro B
        change (Subobject.arrow B.val).right.hom.app (op U.unop.val) ≫
            A.right.obj.map (homOfLE f.unop.hom.le).op ≫
              (hU V.unop.val V.unop.property).desc ((E V.unop.val).mapCocone t) =
          (Subobject.arrow B.val).right.hom.app (op U.unop.val) ≫
            (hU U.unop.val U.unop.property).desc ((E U.unop.val).mapCocone t) ≫
              t.pt.right.obj.map (homOfLE f.unop.hom.le).op
        rw [← NatTrans.naturality_assoc]
        have hv := (hU V.unop.val V.unop.property).fac ((E V.unop.val).mapCocone t) B
        have hu := (hU U.unop.val U.unop.property).fac ((E U.unop.val).mapCocone t) B
        change (Subobject.arrow B.val).right.hom.app (op V.unop.val) ≫
          (hU V.unop.val V.unop.property).desc ((E V.unop.val).mapCocone t) =
            (t.ι.app B).right.hom.app (op V.unop.val) at hv
        change (Subobject.arrow B.val).right.hom.app (op U.unop.val) ≫
          (hU U.unop.val U.unop.property).desc ((E U.unop.val).mapCocone t) =
            (t.ι.app B).right.hom.app (op U.unop.val) at hu
        have hv' := congrArg
          (fun z ↦ (B.val : X.CommAlgebraSheaf).right.obj.map
            (homOfLE f.unop.hom.le).op ≫ z) hv
        have hu' := congrArg
          (fun z ↦ z ≫ t.pt.right.obj.map (homOfLE f.unop.hom.le).op) hu
        exact hv'.trans (((t.ι.app B).right.hom.naturality _).trans
          (hu'.symm.trans (Category.assoc _ _ _))) }
  let g (t : Cocone D) : A.right.obj ⟶ t.pt.right.obj :=
    TopCat.Sheaf.restrictHomEquivHom A.right.obj t.pt.right hb (α t)
  have hg (t : Cocone D) (U : X.affineOpens) :
      (g t).app (op U.val) =
        (hU U.val U.property).desc ((E U.val).mapCocone t) :=
    TopCat.Sheaf.extend_hom_app A.right.obj t.pt.right hb (α t) U
  let lift (t : Cocone D) : A ⟶ t.pt := by
    refine Under.homMk ⟨g t⟩ ?_
    apply ObjectProperty.hom_ext
    apply TopCat.Sheaf.hom_ext (B := basis) X.sheaf.obj t.pt.right hb
    intro U
    change A.hom.hom.app (op U.val) ≫ (g t).app (op U.val) =
      t.pt.hom.hom.app (op U.val)
    rw [hg]
    let B : A.finiteTypeQuasiCoherentSubalgebras := Classical.choice hne'
    have hw := congrArg (fun f ↦ f.hom.app (op U.val)) (Subobject.arrow B.val).w
    have ht := congrArg (fun f ↦ f.hom.app (op U.val)) (t.ι.app B).w
    change (B.val : X.CommAlgebraSheaf).hom.hom.app (op U.val) ≫
      (Subobject.arrow B.val).right.hom.app (op U.val) = A.hom.hom.app (op U.val) at hw
    change (B.val : X.CommAlgebraSheaf).hom.hom.app (op U.val) ≫
      (t.ι.app B).right.hom.app (op U.val) = t.pt.hom.hom.app (op U.val) at ht
    rw [← hw, Category.assoc]
    exact (congrArg
      (fun f ↦ (B.val : X.CommAlgebraSheaf).hom.hom.app (op U.val) ≫ f)
      ((hU U.val U.property).fac ((E U.val).mapCocone t) B)).trans ht
  have hlift (t : Cocone D) (B : A.finiteTypeQuasiCoherentSubalgebras) :
      c.ι.app B ≫ lift t = t.ι.app B := by
    apply Under.UnderMorphism.ext
    apply ObjectProperty.hom_ext
    apply TopCat.Sheaf.hom_ext (B := basis) _ t.pt.right hb
    intro U
    change (Subobject.arrow B.val).right.hom.app (op U.val) ≫
      (g t).app (op U.val) = _
    rw [hg]
    exact (hU U.val U.property).fac ((E U.val).mapCocone t) B
  refine ⟨c, rfl, ⟨⟨lift, hlift, ?_⟩⟩, fun B ↦ Category.comp_id _⟩
  intro t m hm
  apply Under.UnderMorphism.ext
  apply ObjectProperty.hom_ext
  apply TopCat.Sheaf.hom_ext (B := basis) _ t.pt.right hb
  intro U
  apply (hU U.val U.property).hom_ext
  intro B
  have h := congrArg (fun f ↦ f.right.hom.app (op U.val)) ((hm B).trans (hlift t B).symm)
  exact h

end AlgebraicGeometry.Scheme
