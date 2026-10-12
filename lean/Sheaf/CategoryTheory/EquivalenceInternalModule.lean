/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.InternalModule
public import Sheaf.CategoryTheory.FiniteContinuousModule

/-!
# Equivalences of module objects and finite continuous linear actions

Source: Stacks Project, Tag 0DV5, proof of (2)-(3)
(blueprint: lem-pod-equivalence-induces-module-objects).
-/

@[expose] public section

section

universe r v₁ v₂ u₁ u₂ g u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory

namespace InternalModule

private theorem map_pair
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [PreservesFiniteProducts F]
    {T X Y : C} (a : T ⟶ X) (b : T ⟶ Y) :
    prod.lift (F.map a) (F.map b) ≫ inv (prodComparison F X Y) =
      F.map (prod.lift a b) := by
  apply (cancel_mono (prodComparison F X Y)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext <;> simp [prodComparison, ← F.map_comp]

private theorem map_from
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (F : C ⥤ D) [PreservesFiniteProducts F]
    (T : C) : terminal.from (F.obj T) ≫ inv (terminalComparison F) =
      F.map (terminal.from T) := by
  apply (cancel_mono (terminalComparison F)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact terminal.hom_ext _ _

private theorem map_add
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (A : InternalModule R C)
    {T : C} (a b : T ⟶ A.X) :
    prod.lift (e.functor.map a) (e.functor.map b) ≫
      (inv (prodComparison e.functor A.X A.X) ≫ e.functor.map A.add) =
      e.functor.map (prod.lift a b ≫ A.add) := by
  rw [← Category.assoc, map_pair, e.functor.map_comp]

private theorem map_zero
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (A : InternalModule R C) (T : C) :
    terminal.from (e.functor.obj T) ≫
      (inv (terminalComparison e.functor) ≫ e.functor.map A.zero) =
      e.functor.map (terminal.from T ≫ A.zero) := by
  rw [← Category.assoc, map_from, e.functor.map_comp]

private noncomputable def transport
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (A : InternalModule R C) :
    InternalModule R D where
  X := e.functor.obj A.X
  add := inv (prodComparison e.functor A.X A.X) ≫ e.functor.map A.add
  zero := inv (terminalComparison e.functor) ≫ e.functor.map A.zero
  neg := e.functor.map A.neg
  smul a := e.functor.map (A.smul a)
  add_assoc T a b c := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    let b' := e.functor.preimage (h ≫ b)
    let c' := e.functor.preimage (h ≫ c)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    have hb : h ≫ b = e.functor.map b' := (e.functor.map_preimage _).symm
    have hc : h ≫ c = e.functor.map c' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha, hb, hc]
    simp only [Category.assoc, map_add, A.add_assoc]
  zero_add T a := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha]
    simp only [terminal.comp_from, Category.assoc, map_zero, map_add, A.zero_add]
  add_zero T a := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha]
    simp only [Category.assoc, terminal.comp_from_assoc, map_zero, map_add, A.add_zero]
  neg_add T a := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha]
    simp only [Category.assoc, terminal.comp_from_assoc, map_zero, map_add,
      ← e.functor.map_comp, A.neg_add]
  add_comm T a b := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let a' := e.functor.preimage (h ≫ a)
    have ha : h ≫ a = e.functor.map a' := (e.functor.map_preimage _).symm
    let b' := e.functor.preimage (h ≫ b)
    have hb : h ≫ b = e.functor.map b' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, ha, hb]
    simp only [Category.assoc, map_add, A.add_comm]
  one_smul := by simpa using congrArg e.functor.map A.one_smul
  mul_smul a b := by simpa using congrArg e.functor.map (A.mul_smul a b)
  smul_add a T b c := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let b' := e.functor.preimage (h ≫ b)
    have hb : h ≫ b = e.functor.map b' := (e.functor.map_preimage _).symm
    let c' := e.functor.preimage (h ≫ c)
    have hc : h ≫ c = e.functor.map c' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, hb, hc]
    simp only [Category.assoc, map_add, ← e.functor.map_comp, A.smul_add]
  add_smul a b T c := by
    let h : e.functor.obj (e.inverse.obj T) ⟶ T := e.counitIso.hom.app T
    let c' := e.functor.preimage (h ≫ c)
    have hc : h ≫ c = e.functor.map c' := (e.functor.map_preimage _).symm
    apply (cancel_epi h).1
    simp only [← Category.assoc, prod.comp_lift, hc]
    simp only [Category.assoc, map_add, ← e.functor.map_comp, A.add_smul]
  zero_smul := by
    rw [A.zero_smul, e.functor.map_comp, ← map_from, Category.assoc]
  smul_zero a := by
    rw [Category.assoc, ← e.functor.map_comp, A.smul_zero]

private theorem transport_isHom
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (A B : InternalModule R C)
    (f : A.X ⟶ B.X) :
    IsHom (transport e A) (transport e B) (e.functor.map f) ↔ IsHom A B f := by
  dsimp only [IsHom, transport]
  constructor
  · rintro ⟨ha, hz, hn, hs⟩
    refine ⟨e.functor.map_injective ?_, e.functor.map_injective ?_,
      e.functor.map_injective ?_, fun a ↦ e.functor.map_injective ?_⟩
    · apply (cancel_epi (inv (prodComparison e.functor A.X A.X))).1
      simpa only [e.functor.map_comp, ← Category.assoc, prodComparison_inv_natural] using ha
    · apply (cancel_epi (inv (terminalComparison e.functor))).1
      simpa only [e.functor.map_comp, Category.assoc] using hz
    · simpa only [e.functor.map_comp] using hn
    · simpa only [e.functor.map_comp] using hs a
  · rintro ⟨ha, hz, hn, hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (inv (prodComparison e.functor A.X A.X) ≫ e.functor.map A.add) ≫
        e.functor.map f = _
      rw [Category.assoc, ← e.functor.map_comp, ha, e.functor.map_comp,
        ← Category.assoc, prodComparison_inv_natural, Category.assoc]
    · change (inv (terminalComparison e.functor) ≫ e.functor.map A.zero) ≫
        e.functor.map f = inv (terminalComparison e.functor) ≫ e.functor.map B.zero
      rw [Category.assoc, ← e.functor.map_comp, hz]
    · simpa only [e.functor.map_comp] using congrArg e.functor.map hn
    · intro a
      simpa only [e.functor.map_comp] using congrArg e.functor.map (hs a)

private noncomputable def transportFunctor
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) :
    InternalModule R C ⥤ InternalModule R D where
  obj := transport e
  map f := ⟨e.functor.map f.val, (transport_isHom e _ _ _).2 f.property⟩
  map_id A := Subtype.ext (e.functor.map_id A.X)
  map_comp f g := Subtype.ext (e.functor.map_comp f.val g.val)

private noncomputable def transport_fullyFaithful
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) :
    (transportFunctor (R := R) e).FullyFaithful where
  preimage {A B} f :=
    ⟨e.functor.preimage f.val, (transport_isHom e A B _).1 (by
      simpa only [e.functor.map_preimage, transportFunctor] using f.property)⟩
  map_preimage f := Subtype.ext (e.functor.map_preimage f.val)
  preimage_map f := Subtype.ext (e.functor.preimage_map f.val)

private theorem double_prod
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (X Y : D) :
    inv (prodComparison e.functor (e.inverse.obj X) (e.inverse.obj Y)) ≫
      e.functor.map (inv (prodComparison e.inverse X Y)) ≫
        e.counitIso.hom.app (X ⨯ Y) =
      prod.map (e.counitIso.hom.app X) (e.counitIso.hom.app Y) := by
  apply prod.hom_ext
  · have hn := e.counitIso.hom.naturality (prod.fst : X ⨯ Y ⟶ X)
    change e.functor.map (e.inverse.map prod.fst) ≫ _ = _ ≫ prod.fst at hn
    simp only [Category.assoc]
    erw [← hn]
    simp only [← Category.assoc, ← e.functor.map_comp,
      inv_prodComparison_map_fst]
    exact (prod.map_fst _ _).symm
  · have hn := e.counitIso.hom.naturality (prod.snd : X ⨯ Y ⟶ Y)
    change e.functor.map (e.inverse.map prod.snd) ≫ _ = _ ≫ prod.snd at hn
    simp only [Category.assoc]
    erw [← hn]
    simp only [← Category.assoc, ← e.functor.map_comp,
      inv_prodComparison_map_snd]
    exact (prod.map_snd _ _).symm

private theorem counit_isHom
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (B : InternalModule R D) :
    IsHom (transport e (transport e.symm B)) B (e.counitIso.hom.app B.X) := by
  change (_ ≫ _) ≫ _ = _ ≫ B.add ∧ (_ ≫ _) ≫ _ = B.zero ∧
    e.functor.map (e.inverse.map B.neg) ≫ _ = _ ≫ B.neg ∧
    ∀ a, e.functor.map (e.inverse.map (B.smul a)) ≫ _ = _ ≫ B.smul a
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (inv (prodComparison e.functor (e.inverse.obj B.X) (e.inverse.obj B.X)) ≫
        e.functor.map (inv (prodComparison e.inverse B.X B.X) ≫ e.inverse.map B.add)) ≫
        e.counitIso.hom.app B.X =
          prod.map (e.counitIso.hom.app B.X) (e.counitIso.hom.app B.X) ≫ B.add
    simp only [e.functor.map_comp, Category.assoc]
    have hn := e.counitIso.hom.naturality B.add
    change e.functor.map (e.inverse.map B.add) ≫ _ = _ ≫ B.add at hn
    rw [hn]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ B.add) (double_prod e B.X B.X)
  · change (inv (terminalComparison e.functor) ≫
        e.functor.map (inv (terminalComparison e.inverse) ≫ e.inverse.map B.zero)) ≫
        e.counitIso.hom.app B.X = B.zero
    simp only [e.functor.map_comp, Category.assoc]
    have hn := e.counitIso.hom.naturality B.zero
    change e.functor.map (e.inverse.map B.zero) ≫ _ = _ ≫ B.zero at hn
    rw [hn]
    have h : inv (terminalComparison e.functor) ≫
        e.functor.map (inv (terminalComparison e.inverse)) ≫
          e.counitIso.hom.app (⊤_ D) = 𝟙 (⊤_ D) := terminal.hom_ext _ _
    simpa only [Category.assoc, Category.id_comp] using congrArg (fun f ↦ f ≫ B.zero) h
  · exact e.counitIso.hom.naturality B.neg
  · intro a
    exact e.counitIso.hom.naturality (B.smul a)

private theorem isHom_inv
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    (A B : InternalModule R C) (i : A.X ≅ B.X)
    (hi : IsHom A B i.hom) : IsHom B A i.inv := by
  rcases hi with ⟨ha, hz, hn, hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (cancel_mono i.hom).1
    simp only [Category.assoc, i.inv_hom_id, Category.comp_id]
    rw [ha, ← Category.assoc, prod.map_map]
    simp
  · apply (cancel_mono i.hom).1
    simpa using hz.symm
  · apply (cancel_epi i.hom).1
    simp only [← Category.assoc, i.hom_inv_id, Category.id_comp]
    rw [← hn, Category.assoc, i.hom_inv_id, Category.comp_id]
  · intro a
    apply (cancel_epi i.hom).1
    simp only [← Category.assoc, i.hom_inv_id, Category.id_comp]
    rw [← hs a, Category.assoc, i.hom_inv_id, Category.comp_id]

private noncomputable def counitIso
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) (B : InternalModule R D) :
    (transportFunctor (R := R) e).obj (transport e.symm B) ≅ B where
  hom := ⟨e.counitIso.hom.app B.X, counit_isHom e B⟩
  inv := ⟨e.counitIso.inv.app B.X, by
    change IsHom B (transport e (transport e.symm B)) (e.counitIso.inv.app B.X)
    exact isHom_inv (transport e (transport e.symm B)) B
      (e.counitIso.app B.X) (counit_isHom e B)⟩
  hom_inv_id := Subtype.ext (e.counitIso.hom_inv_id_app B.X)
  inv_hom_id := Subtype.ext (e.counitIso.inv_hom_id_app B.X)

private theorem transport_essSurj
    {R : Type r} [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (e : C ≌ D) :
    (transportFunctor (R := R) e).EssSurj where
  mem_essImage B := ⟨transport e.symm B, ⟨counitIso e B⟩⟩

end InternalModule

/-- Equivalences preserve finite products, terminal objects, and internal left modules,
with exactly the transported operations and the original underlying functor.
Source: Stacks Tag 0DV5, proof of (2)-(3)
(blueprint: lem-pod-equivalence-induces-module-objects).
Proof, step 1: an equivalence preserves limits. Apply its functor to each operation and
conjugate using the product and terminal comparison isomorphisms. Functoriality transports
all axiom diagrams. The inverse equivalence transports structures back; naturality of
unit and counit gives the lifted equivalence. Operation-preserving maps are transported
by the original functor. This step is elementary and has no proof dependencies. -/
theorem equivalence_induces_internalModules (R : Type r) [Ring R]
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D] (e : C ≌ D) :
    PreservesFiniteProducts e.functor ∧
    PreservesLimit (Functor.empty.{0} C) e.functor ∧
    ∃ E : InternalModule R C ≌ InternalModule R D,
      E.functor ⋙ InternalModule.forget R D = InternalModule.forget R C ⋙ e.functor ∧
      (∀ A : InternalModule R C,
        HEq (E.functor.obj A).add
          (inv (prodComparison e.functor A.X A.X) ≫ e.functor.map A.add) ∧
        HEq (E.functor.obj A).zero
          (inv (terminalComparison e.functor) ≫ e.functor.map A.zero) ∧
        HEq (E.functor.obj A).neg (e.functor.map A.neg) ∧
        ∀ a : R, HEq ((E.functor.obj A).smul a) (e.functor.map (A.smul a))) ∧
      ∀ (A B : InternalModule R C) (f : A ⟶ B),
        HEq (E.functor.map f).val (e.functor.map f.val) := by
  let F := InternalModule.transportFunctor (R := R) e
  let : F.Full := (InternalModule.transport_fullyFaithful e).full
  let : F.Faithful := (InternalModule.transport_fullyFaithful e).faithful
  let : F.EssSurj := InternalModule.transport_essSurj e
  let : F.IsEquivalence := {}
  refine ⟨inferInstance, inferInstance, F.asEquivalence, ?_, ?_, ?_⟩
  · rfl
  · intro A
    exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, fun _ ↦ HEq.rfl⟩
  · intro A B f
    exact HEq.rfl

/-- Internal modules in finite continuous group sets identify with finite continuous
linear representations, with the same operations and equivariant linear morphisms.
Source: Stacks Tag 0DV5, proof of (3)
(blueprint: lem-pod-equivalence-induces-module-objects).
Proof, step 2: the equivariant addition, zero, negation and scalar maps give the carrier
a left module structure. Their equivariance says every group element acts linearly;
inverses in the group give linear automorphisms. Conversely a continuous linear action
makes all four operations equivariant. These constructions are mutually inverse on
objects and maps, an isomorphism of categories and not only an equivalence.
The action retains its discrete topology and finite carrier.
This step is elementary and has no proof dependencies. -/
theorem internalModules_finiteContAction (R : Type r) [Ring R]
    (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ E : InternalModule R (ContAction FintypeCat.{u} G) ≌
        FiniteContinuousModule.{r, g, u} R G,
      E.functor ⋙ E.inverse = 𝟭 _ ∧
      E.inverse ⋙ E.functor = 𝟭 _ ∧
      ∃ i : InternalModule.forget R (ContAction FintypeCat.{u} G) ⋙
          finiteContActionForget G ≅ E.functor ⋙ FiniteContinuousModule.forget R G,
        ∀ (A : InternalModule R (ContAction FintypeCat.{u} G))
          (T : ContAction FintypeCat.{u} G) (a b : T ⟶ A.X) (t : T.obj.V),
          (fun (f : (T ⟶ A.X) → (T.obj.V → A.X.obj.V))
            (k : A.X.obj.V → (E.functor.obj A).obj.obj.V) ↦
            k (f (prod.lift a b ≫ A.add) t) = k (f a t) + k (f b t) ∧
            k (f (terminal.from T ≫ A.zero) t) = (0 : (E.functor.obj A).obj.obj.V) ∧
            k (f (a ≫ A.neg) t) = -k (f a t) ∧
            ∀ c : R, k (f (a ≫ A.smul c) t) = c • k (f a t))
            (fun h ↦ ((finiteContActionForget G).map h).hom) (i.hom.app A).hom := by
  sorry

end CategoryTheory

end
