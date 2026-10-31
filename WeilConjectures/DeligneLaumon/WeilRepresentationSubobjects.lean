/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedGenericWeilData
import WeilConjectures.RepresentationTheory.LAdicSubrepresentation
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Subobjects of allowed Weil representations
Source: Weil II (1.1.6), (1.1.12), invariant-subspace descent.
(blueprint: lem-dl-a1-weil-representation-subobjects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

private theorem range_subobject_mk {K : Type u} [Field K]
  {H : Type v} [_root_.Group H] (P : ObjectProperty (Rep.{w} K H))
  {X V : P.FullSubcategory} (f : X ⟶ V) [Mono f] :
    ((Subobject.mk f).arrow.hom.hom).range = f.hom.hom.range := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(Subobject.underlyingIso f).hom.hom.hom a, ?_⟩
    exact congrArg (fun b : (Subobject.mk f : P.FullSubcategory) ⟶ V ↦ b.hom.hom a)
      (Subobject.underlyingIso_hom_comp_eq_mk f)
  · rintro ⟨a, rfl⟩
    refine ⟨(Subobject.underlyingIso f).inv.hom.hom a, ?_⟩
    exact congrArg (fun b : X ⟶ V ↦ b.hom.hom a) (Subobject.underlyingIso_arrow f)

private theorem subobjects_of_subrepresentations {K : Type u} [Field K]
    {H : Type v} [_root_.Group H] (P : ObjectProperty (Rep.{w} K H))
    (hP : ∀ (V : P.FullSubcategory) (W : Subrepresentation V.obj.ρ),
      P (Rep.of W.toRepresentation)) (V : P.FullSubcategory) :
    ∃ k : Subobject V ≃o Subrepresentation V.obj.ρ,
      ∀ S : Subobject V, (k S : Set V.obj.V) = Set.range S.arrow.hom.hom := by
  classical
  let obj (X : P.FullSubcategory) (W : Subrepresentation X.obj.ρ) : P.FullSubcategory :=
    ⟨Rep.of W.toRepresentation, hP X W⟩
  let inc (X : P.FullSubcategory) (W : Subrepresentation X.obj.ρ) : obj X W ⟶ X :=
    ObjectProperty.homMk (Rep.ofHom ⟨W.toSubmodule.subtype, fun _ ↦ rfl⟩)
  have hinc (X : P.FullSubcategory) (W : Subrepresentation X.obj.ρ) : Mono (inc X W) := by
    have : Mono (inc X W).hom :=
      (Rep.mono_iff_injective _).mpr Subtype.val_injective
    exact (ObjectProperty.ι P).mono_of_mono_map
      (by change Mono (inc X W).hom; infer_instance)
  have hinj {X Y : P.FullSubcategory} (f : X ⟶ Y) [Mono f] :
      Function.Injective f.hom.hom := by
    let W := f.hom.hom.ker
    let i := inc X W
    have : Mono i := hinc X W
    have hi : i ≫ f = 0 := by
      apply ObjectProperty.hom_ext
      ext z
      exact z.property
    have hz : i = 0 := (cancel_mono f).mp (by simpa using hi)
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro z hz'
    change z = 0
    have hh := congrArg (fun a : obj X W ⟶ X ↦ a.hom.hom ⟨z, hz'⟩) hz
    exact hh
  let sub (W : Subrepresentation V.obj.ρ) : Subobject V :=
    let := hinc V W
    Subobject.mk (inc V W)
  have hleft (W : Subrepresentation V.obj.ρ) : (sub W).arrow.hom.hom.range = W := by
    let := hinc V W
    rw [range_subobject_mk P]
    ext z
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.property, fun hz ↦ ⟨⟨z, hz⟩, rfl⟩⟩
  have hright (S : Subobject V) : sub S.arrow.hom.hom.range = S := by
    let W := S.arrow.hom.hom.range
    let f := S.arrow.hom.hom.toLinearMap
    let e := LinearEquiv.ofInjective f (hinj S.arrow)
    let er : (S : P.FullSubcategory).obj.ρ.Equiv W.toRepresentation :=
      .mk e (fun g ↦ by
        ext z
        exact Representation.IntertwiningMap.isIntertwining _ _ S.arrow.hom.hom g z)
    let ei : (S : P.FullSubcategory) ≅ obj V W :=
      P.isoMk (Rep.mkIso er)
    have : Mono (inc V W) := hinc V W
    exact (Subobject.eq_mk_of_comm (inc V W) ei (by rfl)).symm
  let k : Subrepresentation V.obj.ρ ≃o Subobject V := {
    toFun := sub
    invFun := fun S ↦ S.arrow.hom.hom.range
    left_inv := hleft
    right_inv := hright
    map_rel_iff' := by
      intro W Z
      let := hinc V W
      let := hinc V Z
      constructor
      · intro h z hz
        let f := Subobject.ofMkLEMk (inc V W) (inc V Z) h
        have hf := congrArg (fun b : obj V W ⟶ V ↦ b.hom.hom ⟨z, hz⟩)
          (Subobject.ofMkLEMk_comp h)
        change (f.hom.hom ⟨z, hz⟩ : V.obj.V) = z at hf
        exact hf ▸ (f.hom.hom ⟨z, hz⟩).property
      · intro h
        apply Subobject.mk_le_mk_of_comm
          (ObjectProperty.homMk (Rep.ofHom ⟨Submodule.inclusion h, fun _ ↦ rfl⟩))
        rfl }
  exact ⟨k.symm, fun _ ↦ rfl⟩

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left) (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]
  (ell : ℕ) [Fact ell.Prime] (A : Geometry D U₀ t G)

/-- Every allowed representation has exactly its invariant vector subspaces as subobjects.
Source: Weil II (1.1.6), (1.1.12), generic-fibre proof step 9.
(blueprint: lem-dl-a1-weil-representation-subobjects).

Proof: the existing invariant-subspace descent theorem supplies a continuous finite coefficient
model for every subrepresentation of the geometric restriction. The canonical subspace object
therefore belongs to the allowed full subcategory. Monomorphisms there are injective: test
one against its kernel subrepresentation. Send a categorical subobject to the range of its
inclusion, and an invariant subspace to its canonical inclusion. The linear isomorphism onto
the range proves one inverse identity, and the chosen representative isomorphism for a
categorical subobject proves the other. Factorizations between inclusions are precisely the
subspace inclusions, proving the order law. -/
theorem representations_subobjects (V : Representations D U₀ t G ell A) :
    ∃ k : Subobject V ≃o Subrepresentation V.obj.ρ,
      ∀ S : Subobject V, (k S : Set V.obj.V) = Set.range S.arrow.hom.hom := by
  apply subobjects_of_subrepresentations
  intro X W
  apply Representation.isLAdic_subrepresentation ell (CondensedLisseMonodromy.Coeff ell)
    A.P X.obj.V _ X.property W.toSubmodule
  intro g z
  rfl

set_option maxHeartbeats 4000000 in
-- The original fibre interface requires additional elaboration of its dependent parameters.
/-- An equivalence with allowed Weil representations identifies subobjects by actual ranges.
Source: Weil II (1.1.12), generic-fibre proof step 9.
(blueprint: lem-dl-a1-weil-representation-subobjects).

Proof: transport categorical subobjects through the equivalence and compose with the
invariant-subspace order isomorphism. A representative isomorphism identifies the range of
the chosen representative with the range of the functor's image of the original inclusion. -/
theorem equivalence_subobjects
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A) :
    subobjectCompatibility D U₀ t G ell A e := by
  classical
  rw [subobjectCompatibility]
  intro F
  let k := (Subobject.lowerEquivalence (MonoOver.congr F e)).toOrderIso
  have hk (H : Subobject F) : k H = Subobject.mk (e.functor.map H.arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow H]
    rfl
  obtain ⟨l, hl⟩ := representations_subobjects D U₀ t G ell A (e.functor.obj F)
  refine ⟨k.trans l, fun H ↦ ?_⟩
  change (l (k H) : Set (e.functor.obj F).obj.V) = _
  rw [hl, hk]
  exact congrArg (fun W : Subrepresentation (e.functor.obj F).obj.ρ ↦
      (W : Set (e.functor.obj F).obj.V))
    (range_subobject_mk _ (e.functor.map H.arrow))

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
