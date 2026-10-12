/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Order.Fin.Basic

/-!
# Finite filtrations with prescribed subquotients

Let `C` be an abelian category and `E` a property of objects of `C`. An object `F` has a *finite
filtration with subquotients in `E`* (`CategoryTheory.HasFiniteFiltrationWith E F`) if there is
a finite increasing chain of subobjects `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_m = F` such that each subquotient
`F_{r+1} / F_r` satisfies `E`.

## Main results

- `CategoryTheory.HasFiniteFiltrationWith.of_epi`: if `q : F ⟶ Q` is an epimorphism, the kernel
  of `q` satisfies `E` and `Q` has a finite filtration with subquotients in `E`, then so does
  `F` (for `E` closed under isomorphisms): pull the filtration of `Q` back along `q` and prepend
  the kernel of `q`.
- `CategoryTheory.HasFiniteFiltrationWith.map`: an exact functor `G` sends a finite filtration
  with subquotients in `E` to a finite filtration whose subquotients are isomorphic to images
  under `G` of objects in `E`.

The subquotients of pulled back subobjects are computed by
`CategoryTheory.Subobject.cokernelOfLEPullbackIso`: pulling back along an epimorphism does not
change the subquotients; those of images under an exact functor by
`CategoryTheory.Functor.cokernelOfLEMapSubobjectIso`.
-/

@[expose] public section

noncomputable section

universe v v' u u'

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Subobject

/-- The cokernel of `ofLE A B h` only depends on `A` and `B` up to equality. -/
def cokernelOfLEIsoOfEq {X : C} {A A' B B' : Subobject X} (hA : A = A') (hB : B = B')
    (h : A ≤ B) (h' : A' ≤ B') : cokernel (ofLE A B h) ≅ cokernel (ofLE A' B' h') := by
  subst hA hB
  exact Iso.refl _

/-- For subobjects `A ≤ B` of `Q` and a morphism `q : F ⟶ Q`, the square formed by the
inclusions `q⁻¹ A ⟶ q⁻¹ B`, `A ⟶ B` and the projections `q⁻¹ A ⟶ A`, `q⁻¹ B ⟶ B` is a
pullback square. -/
lemma isPullback_ofLE_pullback {F Q : C} (q : F ⟶ Q) {A B : Subobject Q} (h : A ≤ B) :
    IsPullback (ofLE _ _ ((pullback q).monotone h)) (pullbackπ q A) (pullbackπ q B)
      (ofLE A B h) := by
  refine IsPullback.of_right ?_ ?_ (isPullback q B).flip
  · rw [ofLE_arrow, ofLE_arrow]
    exact (isPullback q A).flip
  · rw [← cancel_mono B.arrow, Category.assoc, Category.assoc, (isPullback q B).w, ofLE_arrow,
      ofLE_arrow_assoc, (isPullback q A).w]

/-- **Pulling back along an epimorphism does not change subquotients**: for an epimorphism
`q : F ⟶ Q` and subobjects `A ≤ B` of `Q`, the subquotient `q⁻¹ B / q⁻¹ A` is isomorphic to
`B / A`. -/
noncomputable def cokernelOfLEPullbackIso {F Q : C} (q : F ⟶ Q) [Epi q] {A B : Subobject Q}
    (h : A ≤ B) :
    cokernel (ofLE _ _ ((pullback q).monotone h)) ≅ cokernel (ofLE A B h) :=
  have sq := isPullback_ofLE_pullback q h
  have : Mono (cokernel.map _ _ _ _ sq.w) := Abelian.mono_cokernel_map_of_isPullback sq
  have : Epi (pullbackπ q B) :=
    (MorphismProperty.epimorphisms C).of_isPullback (isPullback q B).flip
      (MorphismProperty.epimorphisms.infer_property q)
  have : Epi (cokernel.map _ _ _ _ sq.w) := epi_of_epi_fac (cokernel.π_desc _ _ _)
  have : IsIso (cokernel.map _ _ _ _ sq.w) := isIso_of_mono_of_epi _
  asIso (cokernel.map _ _ _ _ sq.w)

/-- The pullback of a zero subobject along `q` is the kernel of `q`. -/
lemma pullback_obj_eq_kernelSubobject {F Q : C} (q : F ⟶ Q) {S : Subobject Q}
    (hS : IsZero (S : C)) : (pullback q).obj S = kernelSubobject q := by
  refine le_antisymm (le_kernelSubobject _ _ ?_) (le_of_comm ((isPullback q S).lift 0
    (kernelSubobject q).arrow (by simp)) (by simp))
  rw [← (isPullback q S).w, hS.eq_of_src S.arrow 0, comp_zero]

end Subobject

namespace Functor

variable {D : Type u'} [Category.{v'} D] [Abelian D] (G : D ⥤ C) [G.PreservesMonomorphisms]

/-- The image of a subobject `S` of `P` under a functor preserving monomorphisms: the subobject
of `G P` given by `G (S ⟶ P)`. -/
noncomputable def mapSubobject {P : D} (S : Subobject P) : Subobject (G.obj P) :=
  Subobject.mk (G.map S.arrow)

omit [Abelian C] [Abelian D] in
lemma mapSubobject_mono {P : D} {S T : Subobject P} (h : S ≤ T) :
    G.mapSubobject S ≤ G.mapSubobject T :=
  Subobject.mk_le_mk_of_comm (G.map (Subobject.ofLE S T h))
    (by rw [← G.map_comp, Subobject.ofLE_arrow])

omit [Abelian C] [Abelian D] in
lemma mapSubobject_top {P : D} : G.mapSubobject (⊤ : Subobject P) = ⊤ :=
  Subobject.mk_eq_top_of_isIso _

/-- The underlying object of the image of a subobject `S` under `G` is `G S`. -/
noncomputable def mapSubobjectIso {P : D} (S : Subobject P) : (G.mapSubobject S : C) ≅ G.obj S :=
  Subobject.underlyingIso _

/-- **Subquotients of images under an exact functor**: for subobjects `S ≤ T` of `P`, the
subquotient `G T / G S` is isomorphic to `G (T / S)`. -/
noncomputable def cokernelOfLEMapSubobjectIso [PreservesFiniteColimits G] {P : D}
    {S T : Subobject P} (h : S ≤ T) :
    cokernel (Subobject.ofLE _ _ (G.mapSubobject_mono h)) ≅
      G.obj (cokernel (Subobject.ofLE S T h)) :=
  cokernelIsoOfEq (Subobject.ofLE_mk_le_mk_of_comm (G.map (Subobject.ofLE S T h))
      (by rw [← G.map_comp, Subobject.ofLE_arrow])) ≪≫
    cokernel.mapIso _ (G.map (Subobject.ofLE S T h)) (Subobject.underlyingIso _)
      (Subobject.underlyingIso _) (by simp) ≪≫
    (PreservesCokernel.iso G _).symm

end Functor

/-- An object `F` of an abelian category has a *finite filtration with subquotients in `E`* if
there is a finite chain of subobjects `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_m = F` all of whose subquotients
`F_{r+1} / F_r` satisfy `E`. -/
def HasFiniteFiltrationWith (E : C → Prop) (F : C) : Prop :=
  ∃ (m : ℕ) (Fil : Fin (m + 1) → Subobject F), Monotone Fil ∧
    IsZero (Subobject.underlying.obj (Fil 0)) ∧ Fil (Fin.last m) = ⊤ ∧
      ∀ (r : Fin m) (h : Fil r.castSucc ≤ Fil r.succ), E (cokernel (Subobject.ofLE _ _ h))

namespace HasFiniteFiltrationWith

variable {E E' : C → Prop}

/-- A zero object has the trivial filtration of length zero. -/
lemma of_isZero {F : C} (hF : IsZero F) : HasFiniteFiltrationWith E F :=
  ⟨0, fun _ ↦ ⊤, monotone_const, hF.of_iso (asIso (⊤ : Subobject F).arrow), rfl,
    fun r ↦ r.elim0⟩

lemma mono (hEE' : ∀ M, E M → E' M) {F : C} (hF : HasFiniteFiltrationWith E F) :
    HasFiniteFiltrationWith E' F := by
  obtain ⟨m, Fil, hmono, h0, hlast, hE⟩ := hF
  exact ⟨m, Fil, hmono, h0, hlast, fun r h ↦ hEE' _ (hE r h)⟩

/-- **Extension by a kernel.** Let `q : F ⟶ Q` be an epimorphism whose kernel satisfies `E`. If
`Q` has a finite filtration with subquotients in `E`, so has `F`, provided `E` is closed under
isomorphisms: the pullback along `q` of the filtration of `Q`, preceded by `0`. -/
lemma of_epi (hE : ∀ {M N : C}, (M ≅ N) → E M → E N) {F Q : C} (q : F ⟶ Q) [Epi q]
    (hK : E (kernel q)) (hQ : HasFiniteFiltrationWith E Q) : HasFiniteFiltrationWith E F := by
  obtain ⟨m, Fil, hmono, h0, hlast, hFil⟩ := hQ
  let Fil' : Fin (m + 1 + 1) → Subobject F :=
    Fin.cons ⊥ (fun r ↦ (Subobject.pullback q).obj (Fil r))
  have hsucc (r : Fin (m + 1)) : Fil' r.succ = (Subobject.pullback q).obj (Fil r) :=
    Fin.cons_succ _ _ _
  have hzero : Fil' 0 = ⊥ := Fin.cons_zero _ _
  refine ⟨m + 1, Fil', ?_, ?_, ?_, ?_⟩
  · refine Fin.monotone_iff_le_succ.mpr fun r ↦ ?_
    refine Fin.cases ?_ (fun r ↦ ?_) r
    · rw [Fin.castSucc_zero, hzero]
      exact bot_le
    · rw [← Fin.succ_castSucc, hsucc, hsucc]
      exact (Subobject.pullback q).monotone (hmono (Fin.castSucc_lt_succ (i := r)).le)
  · rw [hzero]
    exact IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero
  · rw [← Fin.succ_last, hsucc, hlast, Subobject.pullback_top]
  · intro r h
    induction r using Fin.cases with
    | zero =>
      have e₁ : Fil' (0 : Fin (m + 1)).castSucc = ⊥ := hzero
      have e₂ : Fil' (0 : Fin (m + 1)).succ = kernelSubobject q := by
        rw [hsucc, Subobject.pullback_obj_eq_kernelSubobject q h0]
      refine hE ((Subobject.cokernelOfLEIsoOfEq e₁ e₂ h bot_le) ≪≫ ?_ ≪≫
        kernelSubobjectIso q).symm hK
      exact cokernelIsoOfEq (IsZero.eq_of_src (IsZero.of_iso (isZero_zero C)
        Subobject.botCoeIsoZero) _ _) ≪≫ cokernelZeroIsoTarget
    | succ r =>
      have e₁ : Fil' r.succ.castSucc = (Subobject.pullback q).obj (Fil r.castSucc) := by
        rw [← Fin.succ_castSucc, hsucc]
      have e₂ : Fil' r.succ.succ = (Subobject.pullback q).obj (Fil r.succ) := hsucc _
      have hle := hmono (Fin.castSucc_lt_succ (i := r)).le
      exact hE ((Subobject.cokernelOfLEIsoOfEq e₁ e₂ h _) ≪≫
        Subobject.cokernelOfLEPullbackIso q hle).symm (hFil r hle)

variable {D : Type u'} [Category.{v'} D] [Abelian D] (G : D ⥤ C) [G.PreservesMonomorphisms]
  [PreservesFiniteColimits G] [G.PreservesZeroMorphisms]

/-- **Image under an exact functor.** If `P` has a finite filtration with subquotients in `E`,
then `G P` has a finite filtration whose subquotients are isomorphic to images under `G` of
objects satisfying `E`. -/
lemma map {E : D → Prop} {P : D} (hP : HasFiniteFiltrationWith E P) :
    HasFiniteFiltrationWith (fun M ↦ ∃ M', E M' ∧ Nonempty (M ≅ G.obj M')) (G.obj P) := by
  obtain ⟨m, Fil, hmono, h0, hlast, hFil⟩ := hP
  refine ⟨m, fun r ↦ G.mapSubobject (Fil r), fun r s hrs ↦ G.mapSubobject_mono (hmono hrs),
    (G.map_isZero h0).of_iso (G.mapSubobjectIso _), by dsimp only; rw [hlast, G.mapSubobject_top],
    fun r h ↦ ?_⟩
  have hle := hmono (Fin.castSucc_lt_succ (i := r)).le
  exact ⟨_, hFil r hle, ⟨G.cokernelOfLEMapSubobjectIso hle⟩⟩

end HasFiniteFiltrationWith

end CategoryTheory

end
