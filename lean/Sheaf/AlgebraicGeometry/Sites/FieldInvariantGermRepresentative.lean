/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import WeilConjectures.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import WeilConjectures.AlgebraicGeometry.Sites.FiniteGaloisSectionsDescent
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small

/-!
# A section representing an invariant geometric germ

Source: Stacks Project, Tag 04JM, direct proof, applied over a finite separable field.
(blueprint: lem-exc-field-invariant-germ-representative).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

-- Preserve the existing names of nondependent premises in the public signature.
set_option linter.unusedVariables false in
/-- Source: Stacks Project, [Tag 04JM](https://stacks.math.columbia.edu/tag/04JM),
the direct proof of Lemma 59.56.5, applied after restricting the sheaf to `Spec L`.
(blueprint: lem-exc-field-invariant-germ-representative).

An invariant germ has a section representative at the specified finite separable field.
The action is supplied as an argument and characterized on germs; this theorem neither
constructs an action nor asserts injectivity, naturality, or independence of embeddings.

Proof:
1. Restrict `F` to the small etale site of `Spec L` by etale composition. The stalk has
   the same pointed neighbourhoods cofinally, with the lift through `Spec L` specified by `x`.
2. Represent `m` in an etale neighbourhood, shrink to the component containing the lift,
   and identify it with a finite separable field by the etale fibre theorem. Embed that
   field in `Ks` using the chosen lift. Take the normal closure inside `Ks` of its
   compositum with `L`, using `FiniteGaloisIntermediateField.adjoin` on the images of
   finite bases. This is finite Galois over `K`, hence over `L`. Its inclusions preserve
   the chosen lifts. Pull the representative back to `Spec E`.
3. The germ map from `Spec E` is injective: equality of germs holds in a common pointed
   refinement; its map to the one-point `Spec E` is an etale surjection, hence a cover,
   and the separated sheaf condition makes restriction injective.
4. Every `L`-automorphism of `E` extends to an element of `L.fixingSubgroup`. Its pullback
   on the representative has the same germ by `haction` and `hm`, so injectivity makes
   the representative invariant under `Gal(E/L)`.
5. Finite Galois sections descent supplies a section over `Spec L`. Naturality of the
   colimit injections shows that its germ at `x` is `m`.

The case `L = K` is the source's global-sections argument. For separably closed `K`,
the finite separable fields are trivial and the assertion reduces to the terminal germ. -/
theorem exists_fieldSection_of_invariant_germ
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v)))
    (action : MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F))
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale s).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)),
      action.smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
        (pointSmallEtale s).toPresheafFiber X x' F.obj z)
    (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : (pointSmallEtale s).fiber.obj (etaleSpec K L))
    (hx : x.left = Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype)))
    (m : (pointSmallEtale s).sheafFiber.obj F)
    (hm : ∀ g ∈ L.fixingSubgroup, action.smul g m = m) :
    ∃ z : F.obj.obj (op (etaleSpec K L)),
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj z = m := by
  let U := uliftFunctor.{u + 1, max u v}
  let F' := (sheafCompose (Spec (.of K)).smallEtaleTopology U).obj F
  let e := ((pointSmallEtale s).presheafFiberCompIso U).app F.obj
  obtain ⟨E, hLE, y, hy, z', hz'⟩ :=
    exists_finiteGalois_germ_representative K Ks Ω s hs F' L
      (e.inv (ULift.up m))
  let z := z'.down
  have hz : (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z = m := by
    have h := congrArg e.hom hz'
    rw [e.inv_hom_id_apply] at h
    have hn := (pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app
      U (etaleSpec K E) y F.obj
    exact congrArg ULift.down ((ConcreteCategory.congr_hom hn z').symm.trans h)
  have hinj : Function.Injective
      ((pointSmallEtale s).toPresheafFiber (etaleSpec K E.toIntermediateField) y F.obj) := by
    intro z z' h
    obtain ⟨Y, f, y', _, hf⟩ :=
      ((pointSmallEtale s).toPresheafFiber_eq_iff' (P := F.obj)
        (etaleSpec K E.toIntermediateField) y z z').mp h
    have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ f) ∈
        (Spec (.of K)).smallEtaleTopology (etaleSpec K E.toIntermediateField) := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      ext a
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨(), y'.left (default : Spec (.of Ω)),
        @Subsingleton.elim (Spec (.of E.toIntermediateField)) _ _ _⟩
    have hsheaf : Presieve.IsSheafFor F.obj (Presieve.singleton f) := by
      rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_iff_generate]
      exact ((isSheaf_iff_isSheaf_of_type _ _).mp F.property) _ hcov
    exact (Presieve.isSeparatedFor_singleton.mp hsheaf.isSeparatedFor) hf
  have hfixed : ∀ g ∈ L.fixingSubgroup,
      action.smul g ((pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z) =
        (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z := by
    simpa only [hz] using hm
  classical
  let i : L →ₐ[K] E := IntermediateField.inclusion hLE
  let : Algebra L E := i.toAlgebra
  have : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq (fun a ↦ (i.commutes a).symm)
  have : IsScalarTower L E Ks := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : FiniteDimensional L E := FiniteDimensional.right K L E
  have : IsGalois L E := IsGalois.tower_top_of_isGalois K L E
  have : Algebra.Etale L E := inferInstance
  have hinv (q : E ≃ₐ[L] E) :
      F.obj.map (etaleSpecMap (q.restrictScalars K)).op z = z := by
    let qK := q.restrictScalars K
    let g := qK.liftNormal Ks
    have hg : g ∈ L.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro a ha
      have h := qK.liftNormal_commutes Ks (i ⟨a, ha⟩)
      have hq : q (i ⟨a, ha⟩) = i ⟨a, ha⟩ := q.commutes ⟨a, ha⟩
      change g a = (q (i ⟨a, ha⟩) : Ks) at h
      rw [hq] at h
      exact h
    obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_separableClosure K Ks Ω g
    let y' := (pointSmallEtale s).fiber.map (etaleSpecMap qK.toAlgHom) y
    have hy' : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left := by
      change y.left ≫ Spec.map (CommRingCat.ofHom qK.toRingHom) = _
      rw [hy, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      have h := congrArg (fun f : Ks →+* Ω ↦ f (a : Ks)) hτ
      change algebraMap Ks Ω (qK a : Ks) = τ (algebraMap Ks Ω (a : Ks))
      have he : g (a : Ks) = (qK a : Ks) := qK.liftNormal_commutes Ks a
      exact (congrArg (algebraMap Ks Ω) he).symm.trans h
    apply hinj
    exact ((pointSmallEtale s).toPresheafFiber_w_apply
      (etaleSpecMap qK.toAlgHom) y F.obj z).trans
        ((haction g τ hτ _ y y' hy' z).symm.trans (hfixed g hg))
  let p := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hp : AlgebraicGeometry.Etale p := (etaleSpec K L).prop
  let c := MorphismProperty.Over.map ⊤ hp
  have hc : c.IsContinuous (Spec (.of L)).smallEtaleTopology
      (Spec (.of K)).smallEtaleTopology := isContinuous_overMap hp le_rfl
  let P : (Spec (.of L)).Etaleᵒᵖ ⥤ Type (max u v) := c.op ⋙ F.obj
  let G : Sheaf (Spec (.of L)).smallEtaleTopology (Type (max u v)) :=
    ⟨P, c.op_comp_isSheaf _ _ F⟩
  let eE : c.obj (etaleSpec L E) ≅ etaleSpec K E :=
    MorphismProperty.Over.isoMk (Iso.refl (Spec (.of E))) (by
      change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        Spec.map (CommRingCat.ofHom (algebraMap L E)) ≫ p
      rw [Category.id_comp, ← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom
        (IsScalarTower.algebraMap_eq K L E)))
  let eL : c.obj (etaleSpec L L) ≅ etaleSpec K L :=
    MorphismProperty.Over.isoMk (Iso.refl (Spec (.of L))) (by
      change 𝟙 _ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ p
      rw [Category.id_comp]
      have hid : Spec.map (CommRingCat.ofHom (algebraMap L L)) = 𝟙 _ := by
        change Spec.map (𝟙 (CommRingCat.of L)) = 𝟙 _
        exact Spec.map_id _
      rw [hid, Category.id_comp])
  let zG : G.obj.obj (op (etaleSpec L E)) := F.obj.map eE.hom.op z
  have hzG (q : E ≃ₐ[L] E) : P.map (etaleSpecMap (K := L) q.toAlgHom).op zG = zG := by
    change F.obj.map (c.map (etaleSpecMap (K := L) q.toAlgHom)).op (F.obj.map eE.hom.op z) =
      F.obj.map eE.hom.op z
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    have heq : c.map (etaleSpecMap (K := L) q.toAlgHom) ≫ eE.hom =
        eE.hom ≫ etaleSpecMap (q.restrictScalars K) := by
      apply MorphismProperty.Over.Hom.ext
      change Spec.map _ ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map _
      simp only [Category.id_comp, Category.comp_id]
      rfl
    rw [heq, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hinv]
  obtain ⟨wG, _, hwG⟩ := (finiteGaloisSectionsDescent L E G).surjOn (show zG ∈ _ from hzG)
  let f : etaleSpec K E ⟶ etaleSpec K L := etaleSpecMap i
  let w := F.obj.map eL.inv.op wG
  have hw : F.obj.map f.op w = z := by
    have hf : f ≫ eL.inv = eE.inv ≫ c.map (etaleSpecMap (Algebra.ofId L E)) := by
      apply MorphismProperty.Over.Hom.ext
      change Spec.map _ ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map _
      simp only [Category.id_comp, Category.comp_id]
      rfl
    change F.obj.map f.op (F.obj.map eL.inv.op wG) = z
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hf,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    change F.obj.map eE.inv.op (G.obj.map (etaleSpecMap (Algebra.ofId L E)).op wG) = z
    rw [hwG]
    simp only [zG, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id, op_id]
    change F.obj.map (𝟙 _) z = z
    rw [CategoryTheory.Functor.map_id]
    rfl
  refine ⟨w, ?_⟩
  have hxy : (pointSmallEtale s).fiber.map f y = x := by
    apply Over.OverMorphism.ext
    change y.left ≫ Spec.map (CommRingCat.ofHom i.toRingHom) = x.left
    rw [hx, hy, ← Spec.map_comp]
    rfl
  have hnat := (pointSmallEtale s).toPresheafFiber_w_apply f y F.obj w
  rw [hw, hxy] at hnat
  exact hnat.symm.trans hz

end AlgebraicGeometry.Scheme
