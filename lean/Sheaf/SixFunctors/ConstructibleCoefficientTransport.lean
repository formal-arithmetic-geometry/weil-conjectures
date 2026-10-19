/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Changing a presentation of the condensed coefficient ring

Source: blueprint main-20261015, sk-thm-sf-pf-field-tensor.proof.md, proof (1),
coefficient presentation transport (blueprint: lem-sf-constructible-coefficient-transport).
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

private lemma point_fp_comap
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) S}
    (h : Mod.IsFinitelyPresented S M) :
    Mod.IsFinitelyPresented R ((Mod.comap φ).obj M) := by
  let F : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) S ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R := Mod.comap φ
  let e : F.obj (Mod.regular S) ≅ Mod.regular R := by
    simpa using Mod.regularIsoOfIsIso (inv φ)
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  let en (n : ℕ) : F.obj (Mod.finiteFree S n) ≅ Mod.finiteFree R n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular S) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let f' : Mod.finiteFree R m ⟶ Mod.finiteFree R n :=
    (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private lemma model_comap
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Γ] [IsCommMonObj Λ] [IsCommMonObj Γ]
    (φ : Λ ⟶ Γ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X))
    (hM : HasFiniteConstantLocalModel Γ X M) :
    HasFiniteConstantLocalModel Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun j ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hU j
  refine ⟨(Mod.comap φ).obj P, point_fp_comap φ hP, ⟨?_⟩⟩
  exact (comapUpperStarIso φ (U.f j)).symm.app M ≪≫
    (Mod.comap (coefficientMap φ (U.X j))).mapIso e ≪≫
    ((upperStarFromPoint (U.X j)).mapModComapIso φ).symm.app P

private lemma model_iso
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun j ↦ ?_⟩
  obtain ⟨P, hP, ⟨i⟩⟩ := hU j
  exact ⟨P, hP, ⟨(upperStar Λ (U.f j)).mapIso e.symm ≪≫ i⟩⟩

private lemma stratified_iso
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun j ↦ model_iso _ ((upperStar Λ (S.immersion j)).mapIso e) (hS j)⟩

private lemma stratified_comap
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Γ] [IsCommMonObj Λ] [IsCommMonObj Γ]
    (φ : Λ ⟶ Γ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X))
    (hM : IsFiniteConstantStratified Γ X M) :
    IsFiniteConstantStratified Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun j ↦ ?_⟩
  exact model_iso _ ((comapUpperStarIso φ (S.immersion j)).app M)
    (model_comap φ _ _ (hS j))

private lemma constructible_comap
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Γ] [IsCommMonObj Λ] [IsCommMonObj Γ]
    (φ : Λ ⟶ Γ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X))
    (hM : IsConstantModelConstructible Γ X M) :
    IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hX
  · exact stratified_comap φ X M hM
  · intro U hU
    exact stratified_iso _ ((comapUpperStarIso φ U.ι).app M)
      (stratified_comap φ _ _ (hM U hU))

private lemma constructible_iso
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hX
  · exact stratified_iso X e hM
  · intro U hU
    exact stratified_iso _ ((upperStar Λ U.ι).mapIso e) (hM U hU)

private lemma bounded_iso
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {K N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (e : K ≅ N) (hK : constantModelBoundedConstructible Λ X K) :
    constantModelBoundedConstructible Λ X N := by
  exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
    fun n ↦ constructible_iso X ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩

private lemma derived_comap
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Γ] [IsCommMonObj Λ] [IsCommMonObj Γ]
    (φ : Λ ⟶ Γ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X)))
    (hK : constantModelBoundedConstructible Γ X K) :
    constantModelBoundedConstructible Λ X
      ((Mod.comap (coefficientMap φ X)).mapDerivedCategory.obj K) := by
  refine ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦ ?_⟩
  exact constructible_iso X
    (((Mod.comap (coefficientMap φ X)).mapDerivedCategoryHomologyFunctorIso n).app K)
    (constructible_comap φ X _ (hK.2 n))

/-- A coefficient-ring isomorphism gives a strong monoidal equivalence of derived
module categories preserving bounded finite-constant-model constructibility.

Source: blueprint main-20261015, sk-thm-sf-pf-field-tensor.proof.md, proof (1),
change of coefficient presentation (blueprint: lem-sf-constructible-coefficient-transport).

Proof: Restrict scalars along the pulled-back ring isomorphism and its inverse.
These are inverse exact additive module equivalences. A finite presentation transports
by the regular-module comparison and preservation of finite sums and cokernels.
The inverse-image comparison transports each constant local model on the same cover,
then on the same stratification and affine opens. Exactness identifies cohomology and
preserves boundedness, giving the constructibility biconditional in both directions.
The scalar equivalence is strong monoidal and preserves flat modules; its derived
strong monoidal structure is transported through its exact derived-functor comparison.
The unit of the derived equivalence identifies the inverse composite with the identity.
All assertions include the zero module, the empty scheme, and arbitrary ring objects. -/
theorem constructibleCoefficientTransport
    (Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (i : Mon.mk Λ ≅ Mon.mk Γ) (X : Scheme.{u}) :
    ∃ e : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ≌
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X)),
      Exists fun [_hmon : e.functor.Monoidal] ↦
        ∀ K, constantModelBoundedConstructible Γ X (e.functor.obj K) ↔
          constantModelBoundedConstructible Λ X K := by
  let φ : Λ ⟶ Γ := i.hom.hom
  have : IsIso φ := (Mon.forget _).map_isIso i.hom
  let E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X) ≌
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
    Mod.comapEquivalenceOfIsIso (coefficientMap φ X)
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X) :=
    Mod.comap (inv (coefficientMap φ X))
  have : F.IsEquivalence := inferInstanceAs E.symm.functor.IsEquivalence
  have : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  let : F.leftDerivedFunctor.Monoidal := Functor.residueDerivedMonoidal F
  let : F.mapDerivedCategory.Monoidal :=
    Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory
  let : E.functor.Additive :=
    inferInstanceAs (Mod.comap (coefficientMap φ X)).Additive
  let : E.inverse.Additive :=
    inferInstanceAs (Mod.comap (inv (coefficientMap φ X))).Additive
  let : E.symm.functor.Additive :=
    inferInstanceAs (Mod.comap (inv (coefficientMap φ X))).Additive
  let : E.symm.inverse.Additive :=
    inferInstanceAs (Mod.comap (coefficientMap φ X)).Additive
  let e := E.symm.mapDerivedCategory
  have he : e.functor.Monoidal := by
    change F.mapDerivedCategory.Monoidal
    exact inferInstance
  refine ⟨e, he, ?_⟩
  intro K
  constructor
  · intro hK
    exact bounded_iso X (e.unitIso.app K).symm (derived_comap φ X _ hK)
  · intro hK
    have h := derived_comap (inv φ) X K hK
    change constantModelBoundedConstructible Γ X
      ((Mod.comap (inv (coefficientMap φ X))).mapDerivedCategory.obj K)
    simpa only [coefficientMap, Functor.map_inv] using h

end AlgebraicGeometry.ProEtale.CondensedRing
