/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Connected finite étale covers

Let `Y` be a connected scheme with a geometric point `s : Spec Ω ⟶ Y`. This file relates
connectedness of a finite étale `Y`-scheme `P` as a scheme with connectedness of `P` as an
object of the Galois category `FÉt(Y)`.

A geometric point of `Y` lifts along a finite étale morphism `f : P ⟶ Y` as soon as its image
lies in the image of `f` (`AlgebraicGeometry.Scheme.Hom.exists_lift_of_isSepClosed`), since the
fibre of `f` over it is a disjoint union of copies of `Spec Ω`. Hence the fibre of `P` at `s` is
nonempty as soon as `P` is (`AlgebraicGeometry.Scheme.FiniteEtale.nonempty_fiber_of_nonempty`):
the image of `P` is open and closed in the connected `Y`.

## Main statements

- `AlgebraicGeometry.Scheme.FiniteEtale.isConnected_of_connectedSpace`: a finite étale `Y`-scheme
  whose underlying scheme is connected is a connected object of `FÉt(Y)`.
- `AlgebraicGeometry.Scheme.FiniteEtale.connectedSpace_of_isConnected`: conversely, the
  underlying scheme of a connected object of `FÉt(Y)` is connected.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

/-- A geometric point `y : Spec Ω ⟶ Y`, `Ω` separably closed, whose image lies in the image of a
finite étale morphism `f : P ⟶ Y` lifts along `f`: the fibre `P ×_Y Spec Ω` is a nonempty
disjoint union of copies of `Spec Ω`, so it has a section. -/
lemma Scheme.Hom.exists_lift_of_isSepClosed {P Y : Scheme.{u}} (f : P ⟶ Y) [IsFinite f] [Etale f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (h : ∃ z, y z ∈ Set.range f) : ∃ x : Spec (.of Ω) ⟶ P, x ≫ f = y := by
  obtain ⟨z, w, hw⟩ := h
  obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w z hw
  obtain ⟨ι, _, -, ⟨e⟩⟩ := f.exists_overIso_sigma_of_isSepClosed y
  obtain ⟨i, -⟩ := (sigmaMk fun _ : ι ↦ Spec (.of Ω)).symm (e.hom.left t)
  have he : e.inv.left ≫ pullback.snd f y = Sigma.desc fun _ : ι ↦ 𝟙 (Spec (.of Ω)) :=
    Over.w e.inv
  refine ⟨Sigma.ι (fun _ : ι ↦ Spec (.of Ω)) i ≫ e.inv.left ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv.left, he,
    Sigma.ι_desc_assoc, Category.id_comp]

namespace Scheme.FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The geometric fibre of a nonempty finite étale scheme over a connected scheme is nonempty:
the image of `P` is open and closed, hence everything, so `s` lifts. -/
lemma nonempty_fiber_of_nonempty [ConnectedSpace Y] (P : Y.FiniteEtale)
    (h : Nonempty P.obj.left) : Nonempty ((fiber s).obj P) := by
  let f : P.obj.left ⟶ Y := P.obj.hom
  have : IsFinite f := P.property
  have : Etale f := P.obj.prop
  have hc : IsClopen (Set.range f) := ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  obtain ⟨x⟩ := h
  have hr : Set.range f = Set.univ := hc.eq_univ ⟨_, x, rfl⟩
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  obtain ⟨t, ht⟩ := f.exists_lift_of_isSepClosed s ⟨z, hr ▸ Set.mem_univ _⟩
  exact ⟨Over.homMk t ht⟩

/-- The fibre of a finite étale scheme is nonempty if and only if the scheme is, over a
connected base. -/
lemma nonempty_fiber_iff [ConnectedSpace Y] (P : Y.FiniteEtale) :
    Nonempty ((fiber s).obj P) ↔ Nonempty P.obj.left := by
  refine ⟨fun ⟨x⟩ ↦ ?_, nonempty_fiber_of_nonempty s P⟩
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  exact ⟨x.left z⟩

/-- A morphism of finite étale `Y`-schemes is finite. -/
instance isFinite_hom_left {P Q : Y.FiniteEtale} (φ : P ⟶ Q) : IsFinite φ.hom.left := by
  have : IsFinite P.obj.hom := P.property
  have : IsFinite Q.obj.hom := Q.property
  have : IsFinite (φ.hom.left ≫ Q.obj.hom) := by rw [hom_left_comp]; infer_instance
  exact IsFinite.of_comp φ.hom.left Q.obj.hom

/-- A morphism of finite étale `Y`-schemes is étale. -/
instance etale_hom_left {P Q : Y.FiniteEtale} (φ : P ⟶ Q) : Etale φ.hom.left := by
  have : Etale P.obj.hom := P.obj.prop
  have : Etale Q.obj.hom := Q.obj.prop
  have : Etale (φ.hom.left ≫ Q.obj.hom) := by rw [hom_left_comp]; infer_instance
  exact Etale.of_comp φ.hom.left Q.obj.hom

/-- A morphism of finite étale `Y`-schemes whose underlying morphism is surjective induces a
surjection on geometric fibres. -/
lemma surjective_fiber_map_of_surjective {P Q : Y.FiniteEtale} (φ : P ⟶ Q)
    (h : Function.Surjective φ.hom.left) : Function.Surjective ((fiber s).map φ) := by
  intro x
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  obtain ⟨t, ht⟩ := φ.hom.left.exists_lift_of_isSepClosed x.left ⟨z, h _⟩
  refine ⟨Over.homMk t ?_, fiber_ext s ?_⟩
  · change t ≫ P.obj.hom = s
    rw [← hom_left_comp φ, ← Category.assoc, ht, fiber_left_comp]
  · rw [fiber_map_left]
    exact ht

variable [ConnectedSpace Y]

/-- A finite étale `Y`-scheme whose underlying scheme is connected is a connected object of the
Galois category `FÉt(Y)`: a subobject `Z ↪ P` has open and closed image, so it is either empty,
hence initial, or surjective, and then it is bijective on geometric fibres. -/
theorem isConnected_of_connectedSpace (P : Y.FiniteEtale) [ConnectedSpace P.obj.left] :
    IsConnected P := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y
  refine ⟨fun h ↦ ?_, fun Z i _ hZ ↦ ?_⟩
  · have := (initial_iff_fiber_empty (fiber s) P).1 ⟨h⟩
    obtain ⟨x⟩ := nonempty_fiber_of_nonempty s P inferInstance
    exact IsEmpty.false x
  · have hne : Nonempty ((fiber s).obj Z) := (not_initial_iff_fiber_nonempty (fiber s) Z).1 hZ
    have hZne : Nonempty Z.obj.left := (nonempty_fiber_iff s Z).1 hne
    let φ := i.hom.left
    have hc : IsClopen (Set.range φ) := ⟨φ.isClosedMap.isClosed_range, φ.isOpenMap.isOpen_range⟩
    obtain ⟨z⟩ := hZne
    have hr : Set.range φ = Set.univ := hc.eq_univ ⟨_, z, rfl⟩
    have hs := surjective_fiber_map_of_surjective s i (Set.range_eq_univ.1 hr)
    by_contra hni
    have hlt := lt_card_fiber_of_mono_of_notIso (fiber s) i hni
    exact (Nat.card_le_card_of_surjective _ hs).not_gt hlt


/-- The open and closed subscheme `V` of a finite étale `Y`-scheme `P`, as a finite étale
`Y`-scheme. -/
noncomputable abbrev ofIsClopen (P : Y.FiniteEtale) (V : P.obj.left.Opens)
    (hV : IsClosed (V : Set P.obj.left)) : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (V.ι ≫ P.obj.hom) (by have : Etale P.obj.hom := P.obj.prop
                                                    infer_instance),
    by
      have : IsFinite P.obj.hom := P.property
      have : IsClosedImmersion V.ι := IsClosedImmersion.of_isOpenImmersion V.ι (by simpa using hV)
      exact inferInstanceAs (IsFinite (V.ι ≫ P.obj.hom))⟩

/-- The inclusion of an open and closed subscheme of a finite étale `Y`-scheme. -/
noncomputable abbrev ofIsClopenι (P : Y.FiniteEtale) (V : P.obj.left.Opens)
    (hV : IsClosed (V : Set P.obj.left)) : ofIsClopen P V hV ⟶ P :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk V.ι rfl)

instance (P : Y.FiniteEtale) (V : P.obj.left.Opens) (hV : IsClosed (V : Set P.obj.left)) :
    Mono (ofIsClopenι P V hV) :=
  ⟨fun _ _ h ↦ hom_ext ((cancel_mono V.ι).1 congr(($h).hom.left))⟩

/-- The underlying scheme of a connected object of `FÉt(Y)` is connected: an open and closed
subscheme is a subobject, which is either empty or everything. -/
theorem connectedSpace_of_isConnected (P : Y.FiniteEtale) [IsConnected P] :
    ConnectedSpace P.obj.left := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y
  rw [connectedSpace_iff_clopen]
  refine ⟨(nonempty_fiber_iff s P).1 ((not_initial_iff_fiber_nonempty (fiber s) P).1
    IsConnected.notInitial), fun V hV ↦ ?_⟩
  rw [or_iff_not_imp_left, ← ne_eq, ← Set.nonempty_iff_ne_empty]
  intro hne
  let V' : P.obj.left.Opens := ⟨V, hV.isOpen⟩
  have hni : IsInitial (ofIsClopen P V' hV.isClosed) → False := by
    rw [not_initial_iff_fiber_nonempty (fiber s), nonempty_fiber_iff s]
    exact hne.to_subtype
  have := IsConnected.noTrivialComponent _ (ofIsClopenι P V' hV.isClosed) hni
  have hiso : IsIso V'.ι := by
    refine ⟨(inv (ofIsClopenι P V' hV.isClosed)).hom.left, ?_, ?_⟩
    · exact congr(($(IsIso.hom_inv_id (ofIsClopenι P V' hV.isClosed))).hom.left)
    · exact congr(($(IsIso.inv_hom_id (ofIsClopenι P V' hV.isClosed))).hom.left)
  have := V'.ι.surjective
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨z, rfl⟩ := V'.ι.surjective x
  simp

end Scheme.FiniteEtale

end AlgebraicGeometry
