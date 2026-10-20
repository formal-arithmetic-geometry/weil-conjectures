/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.CategoryTheory.SignedFibreShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # The signed interchange of two cone coordinates

Source: Stacks Project, Derived Categories, Tags 014E/014F and the signed double
cone calculation in steps 4--6 of lem-amb-signed-fibre-triangulated
(blueprint: lem-amb-signed-fibre-cone).

Applying an additive functor to the cone inclusions and projections gives an
explicit direct-sum decomposition. The signed permutation sends source order
`(x,y,z,w)` to target order `(x,z,y,-w)`. The two cone projections reduce the
chain-map check to four equations; naturality of `r` cancels the mixed terms.
The inverse is the inverse permutation with the same sign. Projection checks
also prove naturality, the inclusion identity, and the boundary identity for
Mathlib's negative cone projection.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace CategoryTheory.SignedFibre

variable {C : Type u} [Category.{v} C] [Abelian C]
  (A B : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive] (r : A ⟶ B)

/-- Additive functors preserve the coordinate decomposition of a cone. -/
noncomputable def coneCoordinates (T : C ⥤ AddCommGrpCat.{w}) [T.Additive]
    {I J : CochainComplex C ℤ} (f : I ⟶ J) (n m : ℤ) (h : n + 1 = m) :
    T.obj ((mappingCone f).X n) ≅ AddCommGrpCat.of (T.obj (I.X m) × T.obj (J.X n)) :=
  AddEquiv.toAddCommGrpIso
    { toFun := fun t ↦ (T.map ((mappingCone.fst f).1.v n m h) t,
        T.map ((mappingCone.snd f).v n n (add_zero n)) t)
      invFun := fun t ↦ T.map ((mappingCone.inl f).v m n (by omega)) t.1 +
        T.map ((mappingCone.inr f).f n) t.2
      left_inv := by
        intro t
        dsimp
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← T.map_comp, ← T.map_comp, ← AddCommGrpCat.hom_add_apply, ← T.map_add,
          mappingCone.id_X f n m h, T.map_id]
        rfl
      right_inv := by
        intro t
        apply Prod.ext <;>
          simp only [map_add, ← ConcreteCategory.comp_apply, ← T.map_comp,
            mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v,
            mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v,
            T.map_id, T.map_zero, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply,
            AddCommGrpCat.hom_id, AddMonoidHom.id_apply, zero_add, add_zero]
      map_add' := by intro a b; simp only [map_add, Prod.mk_add_mk] }

/-- The signed interchange of four coordinates. -/
def conePermutation (P Q R S : AddCommGrpCat.{w}) :
    ((P × Q) × (R × S)) ≃+ ((P × R) × (Q × S)) where
  toFun t := ((t.1.1, -t.2.1), (t.1.2, t.2.2))
  invFun t := ((t.1.1, t.2.1), (-t.1.2, t.2.2))
  left_inv t := by simp
  right_inv t := by simp
  map_add' x y := by simp [add_comm]

/-- The canonical degreewise signed cone interchange. -/
noncomputable def coneXIso {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ) :
    X A B (mappingCone f) n ≅ (mappingCone (map A B r f)).X n :=
  AddEquiv.toAddCommGrpIso
    ((AddEquiv.prodCongr
      (coneCoordinates A f n (n + 1) rfl).addCommGroupIsoToAddEquiv
      (coneCoordinates B f (n - 1) ((n + 1) - 1) (by omega)).addCommGroupIsoToAddEquiv).trans
      ((conePermutation _ _ _ _).trans
        (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
          (coneCoordinates (𝟭 AddCommGrpCat.{w}) (map A B r f) n (n + 1) rfl)).symm))

lemma coneXIso_hom_apply {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ)
    (t : X A B (mappingCone f) n) :
    (coneXIso A B r f n).hom t =
      (mappingCone.inl (map A B r f)).v (n + 1) n (by omega)
        (A.map ((mappingCone.fst f).1.v n (n + 1) rfl) t.1,
          -B.map ((mappingCone.fst f).1.v (n - 1) ((n + 1) - 1) (by omega)) t.2) +
      (mappingCone.inr (map A B r f)).f n
        (A.map ((mappingCone.snd f).v n n (add_zero n)) t.1,
          B.map ((mappingCone.snd f).v (n - 1) (n - 1) (add_zero (n - 1))) t.2) := rfl

lemma coneXIso_fst_apply {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ)
    (t : X A B (mappingCone f) n) :
    (mappingCone.fst (map A B r f)).1.v n (n + 1) rfl ((coneXIso A B r f n).hom t) =
      (A.map ((mappingCone.fst f).1.v n (n + 1) rfl) t.1,
        -B.map ((mappingCone.fst f).1.v (n - 1) ((n + 1) - 1) (by omega)) t.2) := by
  rw [coneXIso_hom_apply]
  simp only [map_add, ← ConcreteCategory.comp_apply, mappingCone.inl_v_fst_v,
    mappingCone.inr_f_fst_v, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply, add_zero]
  rfl

lemma coneXIso_snd_apply {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ)
    (t : X A B (mappingCone f) n) :
    (mappingCone.snd (map A B r f)).v n n (add_zero n) ((coneXIso A B r f n).hom t) =
      (A.map ((mappingCone.snd f).v n n (add_zero n)) t.1,
        B.map ((mappingCone.snd f).v (n - 1) (n - 1) (add_zero (n - 1))) t.2) := by
  rw [coneXIso_hom_apply]
  simp only [map_add, ← ConcreteCategory.comp_apply, mappingCone.inl_v_snd_v,
    mappingCone.inr_f_snd_v, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply, zero_add]
  rfl

/-- A cochain component is compatible with transport of both integer indices. -/
lemma cochain_transport {K L : CochainComplex C ℤ} {k : ℤ}
    (γ : HomComplex.Cochain K L k) {p q p' q' : ℤ} (h : p + k = q)
    (hp : p = p') (hq : q = q') (h' : p' + k = q') :
    γ.v p q h ≫ (L.XIsoOfEq hq).hom =
      (K.XIsoOfEq hp).hom ≫ γ.v p' q' h' := by
  subst p'
  subst q'
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Tags 014E/014F, explicit signed double-cone calculation
(blueprint: lem-amb-signed-fibre-cone).

The signed interchange commutes with the cone differentials. Compose with each
cone projection. The first projection uses `d_fst_v`, the second `d_snd_v`;
additivity and naturality of `r` give the four coordinate equations. The
component isomorphisms already carry explicit inverses, so these equalities
assemble into an isomorphism of complexes. -/
noncomputable def coneIso {I J : CochainComplex C ℤ} (f : I ⟶ J) :
    obj A B r (mappingCone f) ≅ mappingCone (map A B r f) :=
  HomologicalComplex.Hom.isoOfComponents (coneXIso A B r f) (by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    apply mappingCone.ext_to (map A B r f) (i + 1) (i + 1 + 1) rfl
    · rw [Category.assoc, mappingCone.d_fst_v _ i (i + 1) (i + 1 + 1) rfl rfl]
      apply AddCommGrpCat.ext
      intro t
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
        AddCommGrpCat.hom_neg, AddMonoidHom.neg_apply]
      rw [coneXIso_fst_apply, coneXIso_fst_apply,
        obj_d_apply A B r (mappingCone f) i (i + 1) rfl,
        obj_d_apply A B r I (i + 1) (i + 1 + 1) rfl]
      dsimp
      simp only [map_sub, map_neg, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        mappingCone.d_fst_v, Functor.map_neg, AddCommGrpCat.hom_neg,
        AddMonoidHom.neg_apply, r.naturality]
      rw [mappingCone.d_fst_v f (i - 1) (i + 1 - 1) (i + 1 + 1 - 1)
        (by omega) (by omega), B.map_neg]
      simp only [Category.assoc, ← B.map_comp,
        ← cochain_transport (mappingCone.fst f).1 rfl
          (show i = i + 1 - 1 by omega) (show i + 1 = i + 1 + 1 - 1 by omega)]
      rfl
    · rw [Category.assoc, mappingCone.d_snd_v _ i (i + 1) rfl]
      apply AddCommGrpCat.ext
      intro t
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
        AddCommGrpCat.hom_add, AddMonoidHom.add_apply]
      rw [coneXIso_fst_apply, coneXIso_snd_apply, coneXIso_snd_apply,
        obj_d_apply A B r (mappingCone f) i (i + 1) rfl,
        obj_d_apply A B r J i (i + 1) rfl, map_apply]
      dsimp
      simp only [map_sub, map_neg, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        mappingCone.d_snd_v, Functor.map_add, AddCommGrpCat.hom_add,
        AddMonoidHom.add_apply, r.naturality]
      rw [mappingCone.d_snd_v f (i - 1) (i + 1 - 1) (by omega), B.map_add]
      simp only [Category.assoc, ← B.map_comp,
        ← cochain_transport (mappingCone.snd f) (add_zero i)
          (show i = i + 1 - 1 by omega) (show i = i + 1 - 1 by omega)]
      apply Prod.ext
      · rfl
      · simp only [AddCommGrpCat.hom_add, AddMonoidHom.add_apply]
        abel)

@[simp] lemma coneIso_hom_f {I J : CochainComplex C ℤ} (f : I ⟶ J) (n : ℤ) :
    (coneIso A B r f).hom.f n = (coneXIso A B r f n).hom := rfl

private lemma cone_map_fst {E : Type*} [Category* E] [Abelian E]
    {I J I' J' : CochainComplex E ℤ} (f : I ⟶ J) (f' : I' ⟶ J')
    (a : I ⟶ I') (b : J ⟶ J') (h : f ≫ b = a ≫ f') (n m : ℤ) (hnm : n + 1 = m) :
    (mappingCone.map f f' a b h).f n ≫ (mappingCone.fst f').1.v n m hnm =
      (mappingCone.fst f).1.v n m hnm ≫ a.f m := by
  apply mappingCone.ext_from f m n hnm <;> simp [mappingCone.map]

private lemma cone_map_snd {E : Type*} [Category* E] [Abelian E]
    {I J I' J' : CochainComplex E ℤ} (f : I ⟶ J) (f' : I' ⟶ J')
    (a : I ⟶ I') (b : J ⟶ J') (h : f ≫ b = a ≫ f') (n : ℤ) :
    (mappingCone.map f f' a b h).f n ≫ (mappingCone.snd f').v n n (add_zero n) =
      (mappingCone.snd f).v n n (add_zero n) ≫ b.f n := by
  apply mappingCone.ext_from f (n + 1) n rfl <;> simp [mappingCone.map]

/-- Naturality of the signed interchange in strictly commuting squares. -/
lemma coneIso_naturality {I J I' J' : CochainComplex C ℤ}
    (f : I ⟶ J) (f' : I' ⟶ J') (a : I ⟶ I') (b : J ⟶ J')
    (h : f ≫ b = a ≫ f') :
    map A B r (mappingCone.map f f' a b h) ≫ (coneIso A B r f').hom =
      (coneIso A B r f).hom ≫ mappingCone.map (map A B r f) (map A B r f')
        (map A B r a) (map A B r b)
        (((functor A B r).map_comp f b).symm.trans
          ((congrArg (functor A B r).map h).trans ((functor A B r).map_comp a f'))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mappingCone.ext_to (map A B r f') n (n + 1) rfl
  · simp only [HomologicalComplex.comp_f, Category.assoc, cone_map_fst]
    apply AddCommGrpCat.ext
    intro t
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, coneIso_hom_f]
    rw [coneXIso_fst_apply, coneXIso_fst_apply, map_apply, map_apply]
    dsimp
    simp only [map_neg, ← ConcreteCategory.comp_apply, ← Functor.map_comp, cone_map_fst]
  · simp only [HomologicalComplex.comp_f, Category.assoc, cone_map_snd]
    apply AddCommGrpCat.ext
    intro t
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, coneIso_hom_f]
    rw [coneXIso_snd_apply, coneXIso_snd_apply, map_apply, map_apply]
    dsimp
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, cone_map_snd]

/-- The signed interchange preserves the cone inclusion. -/
lemma coneIso_inr {I J : CochainComplex C ℤ} (f : I ⟶ J) :
    map A B r (mappingCone.inr f) ≫ (coneIso A B r f).hom =
      mappingCone.inr (map A B r f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mappingCone.ext_to (map A B r f) n (n + 1) rfl
  · simp only [HomologicalComplex.comp_f, mappingCone.inr_f_fst_v]
    apply AddCommGrpCat.ext
    intro t
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, coneIso_hom_f]
    rw [coneXIso_fst_apply, map_apply]
    dsimp
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      mappingCone.inr_f_fst_v, Functor.map_zero]
    simp
  · simp only [HomologicalComplex.comp_f, mappingCone.inr_f_snd_v]
    apply AddCommGrpCat.ext
    intro t
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, coneIso_hom_f]
    rw [coneXIso_snd_apply, map_apply]
    dsimp
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      mappingCone.inr_f_snd_v, Functor.map_id]
    rfl

private lemma triangle_boundary_f {E : Type*} [Category* E] [Abelian E]
    {I J : CochainComplex E ℤ} (f : I ⟶ J) (n : ℤ) :
    (mappingCone.triangle f).mor₃.f n = -(mappingCone.fst f).1.v n (n + 1) rfl := by
  apply mappingCone.ext_from f (n + 1) n rfl <;> simp [shiftFunctorObjXIso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The cone boundary has the sign compatible with the signed shift comparison. -/
lemma coneIso_boundary {I J : CochainComplex C ℤ} (f : I ⟶ J) :
    map A B r (mappingCone.triangle f).mor₃ ≫ (shiftIso A B r I 1).hom =
      (coneIso A B r f).hom ≫ (mappingCone.triangle (map A B r f)).mor₃ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.ext
  intro t
  simp only [HomologicalComplex.comp_f, AddCommGrpCat.hom_comp,
    AddMonoidHom.comp_apply, shiftIso_hom_f, coneIso_hom_f, triangle_boundary_f,
    AddCommGrpCat.hom_neg, AddMonoidHom.neg_apply]
  change (shiftXIso A B I 1 n).hom
      ((map A B r (mappingCone.triangle f).mor₃).f n t) =
    -(mappingCone.fst (map A B r f)).1.v n (n + 1) rfl
      ((coneXIso A B r f n).hom t)
  rw [shiftXIso_hom_apply, map_apply, coneXIso_fst_apply]
  dsimp
  simp only [triangle_boundary_f, Functor.map_neg, AddCommGrpCat.hom_neg,
    AddMonoidHom.neg_apply, Units.neg_smul, one_smul, map_neg, neg_neg,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, HomComplex.Cochain.v_comp_XIsoOfEq_hom]

end CategoryTheory.SignedFibre
