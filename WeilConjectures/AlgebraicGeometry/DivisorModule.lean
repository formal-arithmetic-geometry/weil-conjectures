/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The module associated to a divisor

## Main definitions

- `Divisor.sectionCondition`: locally constant functions satisfying the order bounds.
- `Divisor.sectionModule`: the explicit section submodule.
- `Divisor.modulePresheaf`: these sections with pointwise restrictions.
- `Divisor.associatedModule`: the resulting sheaf of modules.
- `Divisor.moduleOfSmoothConnectedCurve`: the construction for smooth connected curves.

## Implementation details

The divisor group, principal-divisor map, class group and degree are the existing
`Scheme.Divisor`, `Scheme.div`, `Scheme.DivisorClassGroup` and `Scheme.Divisor.degree`.
We supply the missing module O_X(D). Locally constant functions represent sections of the
constant sheaf of the function field. On a nonempty open of an integral scheme these are
constant; on the empty open there is exactly one function, giving the zero module.
The construction applies to regular integral Noetherian schemes, hence to smooth connected
curves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] [IsRegular X]

/-- Pointwise scalar action on function-field-valued functions, by taking the germ at each
point and then specializing to the generic point. -/
noncomputable def divisorScalarMap (U : X.Opens) : Γ(X, U) →+* (U → X.functionField) :=
  RingHom.pi fun x : U ↦
    (algebraMap (X.presheaf.stalk x.val) X.functionField).comp
      (X.presheaf.germ U x.val x.property).hom

/-- Scalar multiplication induced by the explicit pointwise germ map. -/
noncomputable instance divisorFunctionAlgebra (U : X.Opens) :
    Algebra Γ(X, U) (U → X.functionField) :=
  (divisorScalarMap X U).toAlgebra

/-- Locally constant rational functions obeying the divisor bounds at closed points. -/
def Divisor.sectionCondition (D : X.Divisor) (U : X.Opens) (s : U → X.functionField) : Prop :=
  IsLocallyConstant s ∧ ∀ (x : U) (hx : IsClosed ({x.val} : Set X)),
    s x = 0 ∨ 0 ≤ X.ord (s x) x.val + D ⟨x.val, hx⟩

/-- Zero satisfies every order bound. -/
theorem Divisor.sectionCondition_zero (D : X.Divisor) (U : X.Opens) :
    D.sectionCondition X U 0 := by
  have _hreg : IsRegular X := inferInstance
  exact ⟨IsLocallyConstant.const 0, fun _ _ ↦ Or.inl rfl⟩

/-- Closure under addition. -/
theorem Divisor.sectionCondition_add (D : X.Divisor) (U : X.Opens)
    (s t : U → X.functionField) (hs : D.sectionCondition X U s)
    (ht : D.sectionCondition X U t) : D.sectionCondition X U (s + t) := by
  refine ⟨hs.1.add ht.1, fun x hx ↦ ?_⟩
  change s x + t x = 0 ∨ 0 ≤ X.ord (s x + t x) x.val + D ⟨x.val, hx⟩
  by_cases hsum : s x + t x = 0
  · exact Or.inl hsum
  right
  rcases hs.2 x hx with h | h
  · simpa [h] using ht.2 x hx |>.resolve_left (by simpa [h] using hsum)
  rcases ht.2 x hx with h' | h'
  · simpa [h'] using h
  by_cases hd : Order.coheight x.val = 1
  · have : IsDiscreteValuationRing (X.presheaf.stalk x.val) :=
      IsRegularLocalRing.isDiscreteValuationRing _ (by
        rw [ringKrullDim_stalk_eq_coheight, hd]
        rfl)
    have hmin := ord_add (X := X) (x := x.val) hsum
    omega
  · rw [ord_eq_zero_of_coheight_neq_one hd] at h ⊢
    exact h

/-- Closure under regular scalars. -/
theorem Divisor.sectionCondition_smul (D : X.Divisor) (U : X.Opens)
    (a : Γ(X, U)) (s : U → X.functionField) (hs : D.sectionCondition X U s) :
    D.sectionCondition X U (a • s) := by
  have hreg : IsRegular X := inferInstance
  have hconst : IsLocallyConstant (divisorScalarMap X U a) := by
    apply IsLocallyConstant.of_constant
    intro x y
    have : Nonempty U := ⟨x⟩
    change algebraMap (X.presheaf.stalk x.val) X.functionField
        (X.presheaf.germ U x.val x.property a) =
      algebraMap (X.presheaf.stalk y.val) X.functionField
        (X.presheaf.germ U y.val y.property a)
    simp only [algebraMap_germ_eq_germToFunctionField]
  refine ⟨hconst.mul hs.1, fun x hx ↦ ?_⟩
  change divisorScalarMap X U a x * s x = 0 ∨
    0 ≤ X.ord (divisorScalarMap X U a x * s x) x.val + D ⟨x.val, hx⟩
  by_cases ha : a = 0
  · left
    simp [ha]
  rcases hs.2 x hx with h | h
  · left
    simp [h]
  right
  have hord : X.ord (s x) x.val ≤
      X.ord (divisorScalarMap X U a x * s x) x.val := by
    have : Nonempty U := ⟨x⟩
    convert ord_le_smul (X := X) x.property ha (s x) using 1
    change X.ord (algebraMap (X.presheaf.stalk x.val) X.functionField
      (X.presheaf.germ U x.val x.property a) * s x) x.val = _
    rw [algebraMap_germ_eq_germToFunctionField]
    rfl
  omega

/-- The explicit section submodule O_X(D)(U) inside function-field-valued functions. -/
noncomputable def Divisor.sectionModule (D : X.Divisor) (U : X.Opens) :
    Submodule Γ(X, U) (U → X.functionField) where
  carrier := {s | D.sectionCondition X U s}
  zero_mem' := D.sectionCondition_zero X U
  add_mem' := fun {s t} hs ht ↦ D.sectionCondition_add X U s t hs ht
  smul_mem' := D.sectionCondition_smul X U

/-- Restriction retains the local conditions. -/
theorem Divisor.sectionCondition_restrict (D : X.Divisor) {U V : X.Opens}
    (i : V ⟶ U) (s : D.sectionModule X U) :
    D.sectionCondition X V (fun x ↦ s.val ⟨x.val, leOfHom i x.property⟩) := by
  refine ⟨s.property.1.comp_continuous ?_, fun x hx ↦
    s.property.2 ⟨x.val, leOfHom i x.property⟩ hx⟩
  exact continuous_subtype_val.subtype_mk _

/-- Pointwise restriction of the explicit section submodules. -/
noncomputable def Divisor.restrictSection (D : X.Divisor) {U V : X.Opens}
    (i : V ⟶ U) (s : D.sectionModule X U) : D.sectionModule X V :=
  ⟨fun x ↦ s.val ⟨x.val, leOfHom i x.property⟩, D.sectionCondition_restrict X i s⟩

/-- Additivity of restriction. -/
theorem Divisor.restrictSection_add (D : X.Divisor) {U V : X.Opens}
    (i : V ⟶ U) (s t : D.sectionModule X U) :
    D.restrictSection X i (s + t) = D.restrictSection X i s + D.restrictSection X i t := by
  rfl

/-- Semilinearity of restriction. -/
theorem Divisor.restrictSection_smul (D : X.Divisor) {U V : X.Opens}
    (i : V ⟶ U) (a : Γ(X, U)) (s : D.sectionModule X U) :
    D.restrictSection X i (a • s) =
      X.presheaf.map i.op a • D.restrictSection X i s := by
  apply Subtype.ext
  funext x
  change algebraMap (X.presheaf.stalk x.val) X.functionField
      (X.presheaf.germ U x.val (leOfHom i x.property) a) * s.val _ =
    algebraMap (X.presheaf.stalk x.val) X.functionField
      (X.presheaf.germ V x.val x.property (X.presheaf.map i.op a)) * s.val _
  rw [TopCat.Presheaf.germ_res_apply]

/-- Restriction as a semilinear map. -/
noncomputable def Divisor.restrictLinear (D : X.Divisor) {U V : X.Opens} (i : V ⟶ U) :
    D.sectionModule X U →ₛₗ[(X.presheaf.map i.op).hom] D.sectionModule X V where
  toFun := D.restrictSection X i
  map_add' := D.restrictSection_add X i
  map_smul' := D.restrictSection_smul X i

/-- Identity restriction. -/
theorem Divisor.restrictSection_id (D : X.Divisor) (U : X.Opens)
    (s : D.sectionModule X U) : D.restrictSection X (𝟙 U) s = s := by
  rfl

/-- Composition of restrictions. -/
theorem Divisor.restrictSection_comp (D : X.Divisor) {U V W : X.Opens}
    (i : V ⟶ U) (j : W ⟶ V) (s : D.sectionModule X U) :
    D.restrictSection X (j ≫ i) s =
      D.restrictSection X j (D.restrictSection X i s) := by
  rfl

/-- The presheaf with the specified sections and pointwise restriction. -/
noncomputable def Divisor.modulePresheaf (D : X.Divisor) : X.PresheafOfModules where
  obj U := ModuleCat.of Γ(X, U.unop) (D.sectionModule X U.unop)
  map {U V} i := ModuleCat.ofHom
    (X := ModuleCat.of Γ(X, U.unop) (D.sectionModule X U.unop))
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (ModuleCat.of Γ(X, V.unop) (D.sectionModule X V.unop)))
    { toFun := D.restrictSection X i.unop
      map_add' := D.restrictSection_add X i.unop
      map_smul' := D.restrictSection_smul X i.unop }
  map_id U := by
    ext s
    exact D.restrictSection_id X U.unop s
  map_comp i j := by
    ext s
    exact D.restrictSection_comp X i.unop j.unop s

/-- The specified presheaf is a sheaf. -/
theorem Divisor.modulePresheaf_isSheaf (D : X.Divisor) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (D.modulePresheaf X).presheaf := by
  let P : TopCat.LocalPredicate (fun _ : X ↦ X.functionField) :=
    { pred := fun {U} f ↦ D.sectionCondition X U f
      res := fun i f hf ↦ D.sectionCondition_restrict X i ⟨f, hf⟩
      locality := by
        intro U f h
        refine ⟨?_, fun x hx ↦ ?_⟩
        · let : TopologicalSpace X.functionField := ⊥
          have : DiscreteTopology X.functionField := ⟨rfl⟩
          apply (IsLocallyConstant.iff_continuous f).mpr
          apply (TopCat.continuousLocal X X.functionField).locality
          intro x
          obtain ⟨V, hxV, i, hi⟩ := h x
          exact ⟨V, hxV, i, hi.1.continuous⟩
        · obtain ⟨V, hxV, i, hi⟩ := h x
          exact hi.2 ⟨x.val, hxV⟩ hx }
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (CategoryTheory.forget Ab)
    (D.modulePresheaf X).presheaf).mpr
  exact TopCat.subpresheafToTypes.isSheaf P

/-- The associated `O_X`-module `O_X(D)`, with explicit section data. -/
noncomputable def Divisor.associatedModule (D : X.Divisor) : X.Modules :=
  ⟨D.modulePresheaf X, D.modulePresheaf_isSheaf X⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Divisor

/-- The module `O_C(D)` for a smooth connected curve `C` over an algebraically closed field. -/
noncomputable def moduleOfSmoothConnectedCurve (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (D : C.Divisor) : C.Modules :=
  letI : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  letI : ConnectedSpace C := IsConnectedCurve.connectedSpace (f := f)
  letI : IsRegular C := IsRegular.of_smooth f
  letI : IsIntegral C := IsRegular.isIntegral C
  D.associatedModule C

end AlgebraicGeometry.Scheme.Divisor
