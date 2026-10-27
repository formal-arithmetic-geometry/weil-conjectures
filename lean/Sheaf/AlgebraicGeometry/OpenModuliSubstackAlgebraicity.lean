/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.OpenStackAlgebraicLfp

/-! # Algebraicity of open full substacks -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- The full inclusion preserves and reflects lifts of base morphisms.
Source: Stacks Project, algebraic.tex, Tag 05UN, full-subcategory projection
(blueprint: lem-sfb-full-open-substack-algebraicity).
Proof: eliminate the hom-lift witness in either direction. Both projections send
an arrow of the full subcategory to the same base arrow. -/
theorem fullModuli_isHomLift {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {P : F.obj → Prop}
    {x y : (fullModuliSubcategory F P).obj} {T U : Over S} (f : T ⟶ U)
    (φ : x ⟶ y) :
    (fullModuliSubcategory F P).p.IsHomLift f φ ↔ F.p.IsHomLift f φ.hom := by
  constructor
  · intro h
    cases h
    exact Functor.IsHomLift.map (p := F.p) φ.hom
  · intro h
    cases h
    exact Functor.IsHomLift.map (p := (fullModuliSubcategory F P).p) φ


set_option backward.isDefEq.respectTransparency false in
private theorem fullModuli_stronglyCartesian {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {P : F.obj → Prop}
    {x y : (fullModuliSubcategory F P).obj} {T U : Over S} (f : T ⟶ U)
    (φ : x ⟶ y) [F.p.IsStronglyCartesian f φ.hom] :
    (fullModuliSubcategory F P).p.IsStronglyCartesian f φ := by
  have := (fullModuli_isHomLift f φ).mpr inferInstance
  refine ⟨?_⟩
  intro z g ψ hψ
  have := (fullModuli_isHomLift _ ψ).mp hψ
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ :=
    Functor.IsStronglyCartesian.universal_property'
      (p := F.p) (f := f) (φ := φ.hom) g ψ.hom
  refine ⟨ObjectProperty.homMk χ,
    ⟨(fullModuli_isHomLift _ _).mpr hχ, ?_⟩, ?_⟩
  · exact (ObjectProperty.ι P).map_injective hfac
  · intro χ' ⟨hχ', hfac'⟩
    apply (ObjectProperty.ι P).map_injective
    exact huniq χ'.hom ⟨(fullModuli_isHomLift _ _).mp hχ',
      congrArg (fun t ↦ t.hom) hfac'⟩

set_option backward.isDefEq.respectTransparency false in
private theorem fullModuli_isFibredInGroupoids {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (hF : IsFibredInGroupoids F)
    (P : F.obj → Prop) (hP : ∀ {x y : F.obj} (_f : x ⟶ y), P y → P x) :
    IsFibredInGroupoids (fullModuliSubcategory F P) := by
  let := hF.1
  have hf : (fullModuliSubcategory F P).p.IsFibered := by
    apply Functor.IsFibered.of_exists_isStronglyCartesian
    intro x T f
    obtain ⟨y, φ, hφ⟩ := IsPreFibered.exists_isCartesian F.p rfl f
    have : F.p.IsCartesian f φ := hφ
    let y' : (fullModuliSubcategory F P).obj := ⟨y, hP φ x.property⟩
    have hsc : F.p.IsStronglyCartesian f φ :=
      Functor.IsFibered.isStronglyCartesian_of_isCartesian F.p f φ
    refine ⟨y', ObjectProperty.homMk φ, ?_⟩
    exact @fullModuli_stronglyCartesian _ F P y' x _ _ f _ hsc
  refine ⟨hf, ?_⟩
  intro x y φ
  have : F.p.IsStronglyCartesian (F.p.map φ.hom) φ.hom := hF.2 φ.hom
  change (fullModuliSubcategory F P).p.IsStronglyCartesian (F.p.map φ.hom) φ
  exact @fullModuli_stronglyCartesian _ F P x y _ _ _ φ (hF.2 φ.hom)

/-- An open full substack of an algebraic stack is algebraic, retaining the scheme
atlas convention and the original base category.
Source: Stacks Project, algebraic.tex, Tag 05UN
(blueprint: lem-sfb-full-open-substack-algebraicity).

Proof: the full inclusion is representable by open subschemes by `open_pullback`.
Its source is fibred in groupoids: take a cartesian lift in the ambient category and
use `pullback` to retain its domain; fullness retains its universal property. Descent
of objects and arrows follows from ambient descent, because membership in the open
can be tested after the surjective etale covering: its pullback open contains that
covering and is therefore the whole test scheme. The diagonal is the base change of
the ambient diagonal, since the inclusion is full. Pull back a smooth surjective
scheme atlas of the ambient stack along the inclusion. Representability of the
inclusion identifies its source with an open subscheme of the atlas; every scheme
base change is the corresponding base change of the original atlas. Smoothness and
surjectivity are preserved. These give the three conjuncts of algebraicity. The empty
open yields the empty scheme atlas, so no nonemptiness assumption is used. -/
theorem OpenModuliSubstack.isAlgebraic {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (U : OpenModuliSubstack F)
    (hF : IsAlgebraicModuliStack F) : IsAlgebraicModuliStack U.category := by
  exact (openStackAlgebraicLfp U.category F (fullModuliInclusion F U.property)
    (fullModuli_isFibredInGroupoids U.fibred U.property U.pullback) hF U.open_pullback).1

end CategoryTheory
