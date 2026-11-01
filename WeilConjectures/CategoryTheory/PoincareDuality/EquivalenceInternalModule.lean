/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalModule.InternalModule
public import WeilConjectures.CategoryTheory.Finite.FiniteContinuousModule

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

end InternalModule

section FiniteActions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace InternalModule
variable {R : Type r} [Ring R]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private abbrev ev {X Y : ContAction FintypeCat.{u} G} (f : X ⟶ Y) :
    X.obj.V → Y.obj.V := f.hom.hom

private theorem ev_comp {X Y Z : ContAction FintypeCat.{u} G}
    (f : X ⟶ Y) (h : Y ⟶ Z) (x : X.obj.V) : ev (f ≫ h) x = ev h (ev f x) := rfl

private theorem ev_ext {X Y : ContAction FintypeCat.{u} G} {f h : X ⟶ Y}
    (he : ∀ x, ev f x = ev h x) : f = h := by
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  exact FintypeCat.hom_ext _ _ he

private theorem ev_id (X : ContAction FintypeCat.{u} G) (x : X.obj.V) :
    ev (𝟙 X) x = x := rfl

omit [IsTopologicalGroup G] in
omit [IsTopologicalGroup G] in
omit [IsTopologicalGroup G] in
private def caHom {X Y : ContAction FintypeCat.{u} G} (f : X.obj.V → Y.obj.V)
    (hf : ∀ (g : G) x, f ((X.obj.ρ g).hom x) = (Y.obj.ρ g).hom (f x)) : X ⟶ Y :=
  ⟨⟨FintypeCat.homMk f, fun g ↦ FintypeCat.hom_ext _ _ (hf g)⟩⟩

-- Concrete products let us evaluate categorical diagrams at arbitrary carrier points.
private def pointProd (X Y : ContAction FintypeCat.{u} G) :
    ContAction FintypeCat.{u} G where
  obj :=
    { V := FintypeCat.of (X.obj.V × Y.obj.V)
      ρ :=
        { toFun g := FintypeCat.homMk (fun p ↦ ((X.obj.ρ g).hom p.1, (Y.obj.ρ g).hom p.2))
          map_one' := by
            apply FintypeCat.hom_ext
            intro p
            change ((X.obj.ρ 1).hom p.1, (Y.obj.ρ 1).hom p.2) = p
            simp only [map_one]
            rfl
          map_mul' g h := by
            apply FintypeCat.hom_ext
            intro p
            change ((X.obj.ρ (g*h)).hom p.1, (Y.obj.ρ (g*h)).hom p.2) = _
            simp only [map_mul]
            rfl } }
  property := by
    apply (@continuousSMul_iff_stabilizer_isOpen _ _ _ _ _ _ _ ⟨rfl⟩).mpr
    intro x
    have hx : Continuous (fun g : G ↦ (X.obj.ρ g).hom x.1) :=
      X.property.1.comp (continuous_id.prodMk continuous_const)
    have hy : Continuous (fun g : G ↦ (Y.obj.ρ g).hom x.2) :=
      Y.property.1.comp (continuous_id.prodMk continuous_const)
    change IsOpen {g : G | ((X.obj.ρ g).hom x.1, (Y.obj.ρ g).hom x.2) = x}
    convert (hx.isOpen_preimage {x.1} (isOpen_discrete _)).inter
      (hy.isOpen_preimage {x.2} (isOpen_discrete _)) using 1
    ext g
    exact Prod.ext_iff

private def pointFst (X Y : ContAction FintypeCat.{u} G) : pointProd X Y ⟶ X :=
  caHom (fun p ↦ p.1) (fun _ _ ↦ rfl)
private def pointSnd (X Y : ContAction FintypeCat.{u} G) : pointProd X Y ⟶ Y :=
  caHom (fun p ↦ p.2) (fun _ _ ↦ rfl)

private def pointLift {T X Y : ContAction FintypeCat.{u} G} (a : T ⟶ X) (b : T ⟶ Y) :
    T ⟶ pointProd X Y := caHom (fun t ↦ (ev a t, ev b t)) (by
  intro g t
  exact Prod.ext (congrArg (fun f ↦ f.hom t) (a.hom.comm g))
    (congrArg (fun f ↦ f.hom t) (b.hom.comm g)))

private noncomputable def pairPoint (X Y : ContAction FintypeCat.{u} G)
    (x : X.obj.V) (y : Y.obj.V) : (X ⨯ Y).obj.V :=
  ev (prod.lift (pointFst X Y) (pointSnd X Y)) (x,y)

private theorem lift_ev {T X Y : ContAction FintypeCat.{u} G}
    (a : T ⟶ X) (b : T ⟶ Y) (t : T.obj.V) :
    ev (prod.lift a b) t = pairPoint X Y (ev a t) (ev b t) := by
  have h : pointLift a b ≫ prod.lift (pointFst X Y) (pointSnd X Y) = prod.lift a b := by
    apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst, prod.lift_snd]
    all_goals apply ev_ext; intro t; rfl
  simpa only [ev_comp, pointLift, caHom, pairPoint, ev, FintypeCat.homMk_apply] using
    (congrArg (fun f ↦ ev f t) h).symm

private def pointUnit : ContAction FintypeCat.{u} G where
  obj := Action.trivial G (FintypeCat.of PUnit)
  property := ⟨continuous_snd⟩

private def pointToUnit (T : ContAction FintypeCat.{u} G) : T ⟶ pointUnit :=
  caHom (fun _ ↦ PUnit.unit) (fun _ _ ↦ rfl)

private noncomputable def zeroPoint : (⊤_ (ContAction FintypeCat.{u} G)).obj.V :=
  ev (terminal.from (pointUnit (G := G))) PUnit.unit

private theorem from_ev (T : ContAction FintypeCat.{u} G) (t : T.obj.V) :
    ev (terminal.from T) t = zeroPoint (G := G) := by
  have h : pointToUnit T ≫ terminal.from (pointUnit (G := G)) = terminal.from T :=
    terminal.hom_ext _ _
  simpa only [ev_comp, pointToUnit, caHom, ev, zeroPoint, FintypeCat.homMk_apply] using
    (congrArg (fun f ↦ ev f t) h).symm

-- Recover the ordinary module operations, and evaluate all internal module laws.

private noncomputable def pointAdd (A : InternalModule R (ContAction FintypeCat.{u} G))
    (x y : A.X.obj.V) : A.X.obj.V := ev A.add (pairPoint A.X A.X x y)

private noncomputable def pointZero (A : InternalModule R (ContAction FintypeCat.{u} G)) :
    A.X.obj.V := ev A.zero zeroPoint

private def pointNeg (A : InternalModule R (ContAction FintypeCat.{u} G))
    (x : A.X.obj.V) : A.X.obj.V := ev A.neg x

private def pointSmul (A : InternalModule R (ContAction FintypeCat.{u} G))
    (c : R) (x : A.X.obj.V) : A.X.obj.V := ev (A.smul c) x

private theorem add_ev (A : InternalModule R (ContAction FintypeCat.{u} G))
    {T : ContAction FintypeCat.{u} G} (a b : T ⟶ A.X) (t : T.obj.V) :
    ev (prod.lift a b ≫ A.add) t = pointAdd A (ev a t) (ev b t) := by
  rw [ev_comp, lift_ev]
  rfl

private theorem zero_ev (A : InternalModule R (ContAction FintypeCat.{u} G))
    (T : ContAction FintypeCat.{u} G) (t : T.obj.V) :
    ev (terminal.from T ≫ A.zero) t = pointZero A := by
  rw [ev_comp, from_ev]
  rfl

@[instance_reducible]
private noncomputable def pointGroup
    (A : InternalModule R (ContAction FintypeCat.{u} G)) : AddCommGroup A.X.obj.V := by
  letI : Add A.X.obj.V := ⟨pointAdd A⟩
  letI : Zero A.X.obj.V := ⟨pointZero A⟩
  letI : Neg A.X.obj.V := ⟨pointNeg A⟩
  exact {
    add := pointAdd A
    zero := pointZero A
    neg := pointNeg A
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc x y z := by
      change pointAdd A (pointAdd A x y) z = pointAdd A x (pointAdd A y z)
      let T := pointProd (pointProd A.X A.X) A.X
      let a : T ⟶ A.X := pointFst _ _ ≫ pointFst _ _
      let b : T ⟶ A.X := pointFst _ _ ≫ pointSnd _ _
      let c : T ⟶ A.X := pointSnd _ _
      have h := congrArg (fun f ↦ ev f ((x,y),z)) (A.add_assoc T a b c)
      simpa only [ev_comp, lift_ev, pointAdd, a, b, c, pointFst, pointSnd, caHom, ev,
        FintypeCat.homMk_apply] using h
    zero_add x := by
      change pointAdd A (pointZero A) x = x
      have h := congrArg (fun f ↦ ev f x) (A.zero_add A.X (𝟙 A.X))
      simpa only [ev_comp, lift_ev, from_ev, pointAdd, pointZero, ev_id] using h
    add_zero x := by
      change pointAdd A x (pointZero A) = x
      have h := congrArg (fun f ↦ ev f x) (A.add_zero A.X (𝟙 A.X))
      simpa only [ev_comp, lift_ev, from_ev, pointAdd, pointZero, ev_id] using h
    neg_add_cancel x := by
      change pointAdd A (pointNeg A x) x = pointZero A
      have h := congrArg (fun f ↦ ev f x) (A.neg_add A.X (𝟙 A.X))
      simpa only [ev_comp, lift_ev, from_ev, pointAdd, pointZero, pointNeg, ev_id] using h
    add_comm x y := by
      change pointAdd A x y = pointAdd A y x
      have h := congrArg (fun f ↦ ev f (x,y))
        (A.add_comm (pointProd A.X A.X) (pointFst _ _) (pointSnd _ _))
      simpa only [ev_comp, lift_ev, pointAdd, ev, pointFst, pointSnd, caHom,
        FintypeCat.homMk_apply] using h }

@[instance_reducible]
private noncomputable def pointModule
    (A : InternalModule R (ContAction FintypeCat.{u} G)) :
    letI := pointGroup A
    Module R A.X.obj.V := by
  letI := pointGroup A
  letI : SMul R A.X.obj.V := ⟨pointSmul A⟩
  exact
    { smul := pointSmul A
      one_smul := fun x ↦ congrArg (fun f ↦ ev f x) A.one_smul
      mul_smul := fun a b x ↦ congrArg (fun f ↦ ev f x) (A.mul_smul a b)
      smul_add := fun a x y ↦ by
        change pointSmul A a (pointAdd A x y) =
          pointAdd A (pointSmul A a x) (pointSmul A a y)
        have h := congrArg (fun f ↦ ev f (x,y))
          (A.smul_add a (pointProd A.X A.X) (pointFst _ _) (pointSnd _ _))
        simpa only [ev_comp, lift_ev, pointAdd, pointSmul, pointFst, pointSnd, caHom, ev,
          FintypeCat.homMk_apply] using h
      add_smul := fun a b x ↦ by
        change pointSmul A (a+b) x = pointAdd A (pointSmul A a x) (pointSmul A b x)
        have h := congrArg (fun f ↦ ev f x) (A.add_smul a b A.X (𝟙 A.X))
        simpa only [ev_comp, lift_ev, pointAdd, pointSmul, ev_id] using h
      zero_smul := fun x ↦ by
        change pointSmul A 0 x = pointZero A
        simpa only [pointSmul, zero_ev, pointGroup] using
          congrArg (fun f ↦ ev f x) A.zero_smul
      smul_zero := fun a ↦ by
        change pointSmul A a (pointZero A) = pointZero A
        simpa only [pointSmul, pointZero, pointGroup, ev_comp] using
          congrArg (fun f ↦ ev f zeroPoint) (A.smul_zero a) }

private theorem pairPoint_act (X Y : ContAction FintypeCat.{u} G) (g : G)
    (x : X.obj.V) (y : Y.obj.V) :
    ((X ⨯ Y).obj.ρ g).hom (pairPoint X Y x y) =
      pairPoint X Y ((X.obj.ρ g).hom x) ((Y.obj.ρ g).hom y) := by
  exact (congrArg (fun f ↦ f.hom (x,y))
    ((prod.lift (pointFst X Y) (pointSnd X Y)).hom.comm g)).symm

private theorem action_add (A : InternalModule R (ContAction FintypeCat.{u} G))
    (g : G) (x y : A.X.obj.V) :
    (A.X.obj.ρ g).hom (pointAdd A x y) =
      pointAdd A ((A.X.obj.ρ g).hom x) ((A.X.obj.ρ g).hom y) := by
  have h := congrArg (fun f ↦ f.hom (pairPoint A.X A.X x y)) (A.add.hom.comm g)
  change ev A.add (((A.X ⨯ A.X).obj.ρ g).hom (pairPoint A.X A.X x y)) =
    (A.X.obj.ρ g).hom (pointAdd A x y) at h
  rw [pairPoint_act] at h
  exact h.symm

private theorem action_smul (A : InternalModule R (ContAction FintypeCat.{u} G))
    (g : G) (c : R) (x : A.X.obj.V) :
    (A.X.obj.ρ g).hom (pointSmul A c x) =
      pointSmul A c ((A.X.obj.ρ g).hom x) := by
  exact (congrArg (fun f ↦ f.hom x) ((A.smul c).hom.comm g)).symm

-- The original finite continuous action is linear for the recovered module structure.

private noncomputable def pointRep
    (A : InternalModule R (ContAction FintypeCat.{u} G)) :
    FiniteContinuousModule.{r, g, u} R G := by
  letI := pointGroup A
  letI := pointModule A
  let ρ : Representation R G A.X.obj.V :=
    { toFun := fun g ↦
        { toFun := (A.X.obj.ρ g).hom
          map_add' := action_add A g
          map_smul' := action_smul A g }
      map_one' := by
        ext x
        exact congrArg (fun f ↦ f.hom x) A.X.obj.ρ.map_one
      map_mul' := fun g h ↦ by
        ext x
        exact congrArg (fun f ↦ f.hom x) (A.X.obj.ρ.map_mul g h) }
  refine ⟨⟨Rep.of ρ, ?_⟩, inferInstance⟩
  intro x
  have : DiscreteTopology ((forget₂ (Action FintypeCat G) TopCat).obj A.X.obj) := ⟨rfl⟩
  exact (A.X.property.1.comp (continuous_id.prodMk continuous_const)).isOpen_preimage
    {x} (isOpen_discrete _)

private theorem pairPoint_fst (X Y : ContAction FintypeCat.{u} G)
    (x : X.obj.V) (y : Y.obj.V) :
    ev (prod.fst : X ⨯ Y ⟶ X) (pairPoint X Y x y) = x := by
  have h := congrArg (fun f ↦ ev f (x,y))
    (prod.lift_fst (pointFst X Y) (pointSnd X Y))
  exact h

private theorem pairPoint_snd (X Y : ContAction FintypeCat.{u} G)
    (x : X.obj.V) (y : Y.obj.V) :
    ev (prod.snd : X ⨯ Y ⟶ Y) (pairPoint X Y x y) = y := by
  have h := congrArg (fun f ↦ ev f (x,y))
    (prod.lift_snd (pointFst X Y) (pointSnd X Y))
  exact h

private theorem map_pairPoint {X Y Z W : ContAction FintypeCat.{u} G}
    (f : X ⟶ Z) (h : Y ⟶ W) (x : X.obj.V) (y : Y.obj.V) :
    ev (prod.map f h) (pairPoint X Y x y) = pairPoint Z W (ev f x) (ev h y) := by
  have hm : prod.map f h = prod.lift (prod.fst ≫ f) (prod.snd ≫ h) := by
    apply prod.hom_ext <;> simp
  rw [hm, lift_ev, ev_comp, ev_comp, pairPoint_fst, pairPoint_snd]

private noncomputable def pointRepMap
    {A B : InternalModule R (ContAction FintypeCat.{u} G)} (f : A ⟶ B) :
    pointRep A ⟶ pointRep B := by
  letI := pointGroup A
  letI := pointModule A
  letI := pointGroup B
  letI := pointModule B
  let l : A.X.obj.V →ₗ[R] B.X.obj.V :=
    { toFun := ev f.val
      map_add' := fun x y ↦ by
        change ev f.val (pointAdd A x y) = pointAdd B (ev f.val x) (ev f.val y)
        have h := congrArg (fun k ↦ ev k (pairPoint A.X A.X x y)) f.property.1
        simpa only [ev_comp, map_pairPoint, pointAdd, ev] using h
      map_smul' := fun c x ↦ by
        exact congrArg (fun k ↦ ev k x) (f.property.2.2.2 c) }
  exact ⟨⟨Rep.ofHom
    { toLinearMap := l
      isIntertwining' := fun g ↦ by
        ext x
        exact congrArg (fun k ↦ k.hom x) (f.val.hom.comm g) }⟩⟩

private noncomputable def pointRepFunctor :
    InternalModule R (ContAction FintypeCat.{u} G) ⥤ FiniteContinuousModule.{r, g, u} R G where
  obj := pointRep
  map := pointRepMap
  map_id A := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    ext x
    rfl
  map_comp f h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    ext x
    rfl

-- Conversely, use a representation's pointwise operations as internal operations.

private abbrev repAction (B : FiniteContinuousModule.{r, g, u} R G) :
    ContAction FintypeCat.{u} G := by
  letI : Finite B.obj.obj.V := B.property
  refine ⟨{ V := FintypeCat.of B.obj.obj.V
            ρ :=
              { toFun := fun g ↦ FintypeCat.homMk (B.obj.obj.ρ g)
                map_one' := by
                  apply FintypeCat.hom_ext
                  intro x
                  exact congrArg (fun f ↦ f x) B.obj.obj.ρ.map_one
                map_mul' := fun g h ↦ by
                  apply FintypeCat.hom_ext
                  intro x
                  exact congrArg (fun f ↦ f x) (B.obj.obj.ρ.map_mul g h) } }, ?_⟩
  apply (@continuousSMul_iff_stabilizer_isOpen _ _ _ _ _ _ _ ⟨rfl⟩).mpr
  exact B.obj.property

private theorem ev_comm {X Y : ContAction FintypeCat.{u} G} (f : X ⟶ Y)
    (g : G) (x : X.obj.V) :
    ev f ((X.obj.ρ g).hom x) = (Y.obj.ρ g).hom (ev f x) :=
  congrArg (fun k ↦ k.hom x) (f.hom.comm g)

private noncomputable def repAdd (B : FiniteContinuousModule.{r, g, u} R G) :
    repAction B ⨯ repAction B ⟶ repAction B :=
  caHom (fun p ↦ ev prod.fst p + ev prod.snd p) (by
    intro g p
    rw [ev_comm, ev_comm]
    exact (_root_.map_add (B.obj.obj.ρ g) _ _).symm)

private noncomputable def repZero (B : FiniteContinuousModule.{r, g, u} R G) :
    ⊤_ (ContAction FintypeCat.{u} G) ⟶ repAction B :=
  caHom (fun _ ↦ 0) (by intro g p; exact (_root_.map_zero (B.obj.obj.ρ g)).symm)

private def repNeg (B : FiniteContinuousModule.{r, g, u} R G) :
    repAction B ⟶ repAction B :=
  caHom (fun x ↦ -x) (by intro g x; exact (map_neg (B.obj.obj.ρ g) x).symm)

private def repSmul (B : FiniteContinuousModule.{r, g, u} R G) (c : R) :
    repAction B ⟶ repAction B :=
  caHom (fun x ↦ c • x) (by intro g x; exact ((B.obj.obj.ρ g).map_smul c x).symm)

private theorem repAdd_eval (B : FiniteContinuousModule.{r, g, u} R G)
    {T : ContAction FintypeCat.{u} G} (a b : T ⟶ repAction B) (t : T.obj.V) :
    ev (prod.lift a b ≫ repAdd B) t = ev a t + ev b t := by
  change ev (prod.lift a b ≫ prod.fst) t + ev (prod.lift a b ≫ prod.snd) t = _
  rw [prod.lift_fst, prod.lift_snd]

private noncomputable abbrev repInternal
    (B : FiniteContinuousModule.{r, g, u} R G) :
    InternalModule R (ContAction FintypeCat.{u} G) where
  X := repAction B
  add := repAdd B
  zero := repZero B
  neg := repNeg B
  smul := repSmul B
  add_assoc T a b c := by
    apply ev_ext
    intro t
    simp only [repAdd_eval]
    exact _root_.add_assoc _ _ _
  zero_add T a := by
    apply ev_ext
    intro t
    rw [repAdd_eval]
    exact _root_.zero_add _
  add_zero T a := by
    apply ev_ext
    intro t
    rw [repAdd_eval]
    exact _root_.add_zero _
  neg_add T a := by
    apply ev_ext
    intro t
    rw [repAdd_eval]
    exact _root_.neg_add_cancel _
  add_comm T a b := by
    apply ev_ext
    intro t
    rw [repAdd_eval, repAdd_eval]
    exact _root_.add_comm _ _
  one_smul := by
    apply ev_ext
    intro t
    exact _root_.one_smul R _
  mul_smul a b := by
    apply ev_ext
    intro t
    exact SemigroupAction.mul_smul a b _
  smul_add c T a b := by
    apply ev_ext
    intro t
    change c • ev (prod.lift a b ≫ repAdd B) t = _
    rw [repAdd_eval, repAdd_eval]
    exact _root_.smul_add _ _ _
  add_smul a b T c := by
    apply ev_ext
    intro t
    rw [repAdd_eval]
    exact _root_.add_smul _ _ _
  zero_smul := by
    apply ev_ext
    intro t
    exact _root_.zero_smul R _
  smul_zero c := by
    apply ev_ext
    intro t
    exact _root_.smul_zero c

private def repActionMap {B D : FiniteContinuousModule.{r, g, u} R G} (f : B ⟶ D) :
    repAction B ⟶ repAction D :=
  caHom (fun x ↦ f.hom.hom.hom x) (fun g x ↦
    congrArg (fun k ↦ k x) (f.hom.hom.hom.isIntertwining' g))

private theorem repActionMap_isHom
    {B D : FiniteContinuousModule.{r, g, u} R G} (f : B ⟶ D) :
    IsHom (repInternal B) (repInternal D) (repActionMap f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ev_ext
    intro p
    change f.hom.hom.hom (ev prod.fst p + ev prod.snd p) =
      ev (prod.map (repActionMap f) (repActionMap f) ≫ prod.fst) p +
      ev (prod.map (repActionMap f) (repActionMap f) ≫ prod.snd) p
    rw [prod.map_fst, prod.map_snd]
    exact _root_.map_add f.hom.hom.hom _ _
  · apply ev_ext
    intro p
    exact _root_.map_zero f.hom.hom.hom
  · apply ev_ext
    intro p
    exact map_neg f.hom.hom.hom p
  · intro a
    apply ev_ext
    intro p
    exact f.hom.hom.hom.map_smul a p

private noncomputable def repInternalFunctor :
    FiniteContinuousModule.{r, g, u} R G ⥤ InternalModule R (ContAction FintypeCat.{u} G) where
  obj := repInternal
  map f := ⟨repActionMap f, repActionMap_isHom f⟩
  map_id B := by
    apply Subtype.ext
    apply ev_ext
    intro x
    rfl
  map_comp f h := by
    apply Subtype.ext
    apply ev_ext
    intro x
    rfl

-- The two constructions are strict inverses, including their actions on morphisms.

private theorem pairPoint_eta (X Y : ContAction FintypeCat.{u} G)
    (p : (X ⨯ Y).obj.V) :
    pairPoint X Y (ev prod.fst p) (ev prod.snd p) = p := by
  have h : pointLift (prod.fst : X ⨯ Y ⟶ X) prod.snd ≫
      prod.lift (pointFst X Y) (pointSnd X Y) = 𝟙 (X ⨯ Y) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, Category.id_comp]
      apply ev_ext
      intro x
      rfl
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
      apply ev_ext
      intro x
      rfl
  exact congrArg (fun f ↦ ev f p) h

private theorem internal_ext {A B : InternalModule R (ContAction FintypeCat.{u} G)}
    (hX : A.X = B.X) (ha : HEq A.add B.add) (hz : HEq A.zero B.zero)
    (hn : HEq A.neg B.neg) (hs : HEq A.smul B.smul) : A = B := by
  cases A
  cases B
  cases hX
  cases ha
  cases hz
  cases hn
  cases hs
  rfl

private theorem repInternal_pointRep (A : InternalModule R (ContAction FintypeCat.{u} G)) :
    repInternal (pointRep A) = A := by
  refine internal_ext rfl ?_ ?_ ?_ ?_
  · apply heq_of_eq
    apply ev_ext
    intro p
    change pointAdd A (ev prod.fst p) (ev prod.snd p) = ev A.add p
    dsimp only [pointAdd]
    exact congrArg (ev A.add) (pairPoint_eta A.X A.X p)
  · apply heq_of_eq
    apply ev_ext
    intro p
    change ev A.zero (zeroPoint (G := G)) = ev A.zero p
    have h : ev (terminal.from (⊤_ (ContAction FintypeCat.{u} G))) p = p := by
      have he : terminal.from (⊤_ (ContAction FintypeCat.{u} G)) = 𝟙 _ :=
        terminal.hom_ext _ _
      rw [he, ev_id]
    rw [from_ev] at h
    rw [h]
  · rfl
  · rfl

private noncomputable def pointRepForgetIso :
    InternalModule.forget R (ContAction FintypeCat.{u} G) ⋙ finiteContActionForget G ≅
      pointRepFunctor ⋙ FiniteContinuousModule.forget R G :=
  NatIso.ofComponents (fun A ↦ Action.mkIso (Iso.refl _) (by intro g; rfl))
    (by intro A B f; rfl)

private theorem rep_ext {A B : Rep.{u} R G} (hV : A.V = B.V)
    (ha : HEq (fun x y : A.V ↦ x + y) (fun x y : B.V ↦ x + y))
    (hs : HEq (fun (c : R) (x : A.V) ↦ c • x) (fun (c : R) (x : B.V) ↦ c • x))
    (hρ : HEq (fun (g : G) (x : A.V) ↦ A.ρ g x)
      (fun (g : G) (x : B.V) ↦ B.ρ g x)) : A = B := by
  cases A
  cases B
  cases hV
  have ha' := eq_of_heq ha
  have hg := AddCommGroup.ext ha'
  cases hg
  have hs' := eq_of_heq hs
  have hm := Module.ext' _ _ (fun c x ↦ congrFun (congrFun hs' c) x)
  cases hm
  have hρ' := eq_of_heq hρ
  have hr : _ = _ := MonoidHom.ext (fun g ↦
    LinearMap.ext (fun x ↦ congrFun (congrFun hρ' g) x))
  cases hr
  rfl

private theorem pointRep_repInternal (B : FiniteContinuousModule.{r, g, u} R G) :
    pointRep (repInternal B) = B := by
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  refine rep_ext rfl ?_ ?_ ?_
  · apply heq_of_eq
    funext x y
    change B.obj.obj.hV1.add
      (ev prod.fst (pairPoint (repAction B) (repAction B) x y))
      (ev prod.snd (pairPoint (repAction B) (repAction B) x y)) = B.obj.obj.hV1.add x y
    rw [pairPoint_fst, pairPoint_snd]
  · rfl
  · rfl

private theorem internal_hom_heq
    {A B A' B' : InternalModule R (ContAction FintypeCat.{u} G)}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (h : A' ⟶ B')
    (hv : HEq f.val h.val) : HEq f h := by
  subst A'
  subst B'
  exact heq_of_eq (Subtype.ext (eq_of_heq hv))

private theorem rep_hom_heq
    {A B A' B' : FiniteContinuousModule.{r, g, u} R G}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (h : A' ⟶ B')
    (hv : HEq (fun x ↦ f.hom.hom.hom x) (fun x ↦ h.hom.hom.hom x)) : HEq f h := by
  subst A'
  subst B'
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  ext x
  exact congrFun (eq_of_heq hv) x

private theorem pointRep_internal_comp :
    (pointRepFunctor (R := R) (G := G)) ⋙ repInternalFunctor = 𝟭 _ := by
  apply Functor.hext repInternal_pointRep
  intro A B f
  apply internal_hom_heq (repInternal_pointRep A) (repInternal_pointRep B)
  rfl

private theorem internal_pointRep_comp :
    (repInternalFunctor (R := R) (G := G)) ⋙ pointRepFunctor = 𝟭 _ := by
  apply Functor.hext pointRep_repInternal
  intro A B f
  apply rep_hom_heq (pointRep_repInternal A) (pointRep_repInternal B)
  rfl

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
  let F := InternalModule.pointRepFunctor (R := R) (G := G)
  let I := InternalModule.repInternalFunctor (R := R) (G := G)
  have hFI : F ⋙ I = 𝟭 _ := InternalModule.pointRep_internal_comp
  have hIF : I ⋙ F = 𝟭 _ := InternalModule.internal_pointRep_comp
  let E := Equivalence.mk F I (eqToIso hFI.symm) (eqToIso hIF)
  refine ⟨E, hFI, hIF, InternalModule.pointRepForgetIso, ?_⟩
  intro A T a b t
  change InternalModule.ev (prod.lift a b ≫ A.add) t =
      InternalModule.pointAdd A (InternalModule.ev a t) (InternalModule.ev b t) ∧
    InternalModule.ev (terminal.from T ≫ A.zero) t = InternalModule.pointZero A ∧
    InternalModule.ev (a ≫ A.neg) t = InternalModule.pointNeg A (InternalModule.ev a t) ∧
    ∀ c : R, InternalModule.ev (a ≫ A.smul c) t =
      InternalModule.pointSmul A c (InternalModule.ev a t)
  exact ⟨InternalModule.add_ev A a b t, InternalModule.zero_ev A T t, rfl, fun _ ↦ rfl⟩

omit [IsTopologicalGroup G] in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
end InternalModule
end FiniteActions

end CategoryTheory

end
