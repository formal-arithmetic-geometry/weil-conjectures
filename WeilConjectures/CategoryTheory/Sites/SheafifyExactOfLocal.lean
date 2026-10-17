/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Exactness after sheafification from local exactness

Let `S` be a short complex of presheaves with values in a concrete abelian category `A`
whose underlying types carry compatible additive structures (e.g. abelian groups or modules).
If every cycle of `S` is locally a boundary, then the sheafification of `S` is exact.

## Main results

- `CategoryTheory.Presheaf.epi_presheafToSheaf_map_of_isLocallySurjective`
- `CategoryTheory.Presheaf.exact_map_presheafToSheaf_of_isLocallySurjective_toCycles`
- `CategoryTheory.Presheaf.isLocallySurjective_toCycles_of_imageSieve_mem`
- `CategoryTheory.Presheaf.exact_map_presheafToSheaf_of_imageSieve_mem`
-/

@[expose] public section

universe w' v' u' v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

section

variable [HasWeakSheafify J A] [J.WEqualsLocallyBijective A] [J.HasSheafCompose (forget A)]

/-- The sheafification of a locally surjective morphism of presheaves is an epimorphism. -/
lemma epi_presheafToSheaf_map_of_isLocallySurjective {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q)
    [IsLocallySurjective J φ] : Epi ((presheafToSheaf J A).map φ) := by
  have : Sheaf.IsLocallySurjective ((presheafToSheaf J A).map φ) :=
    (isLocallySurjective_presheafToSheaf_map_iff J φ).2 inferInstance
  infer_instance

end

variable [Abelian A] [HasSheafify J A] [J.WEqualsLocallyBijective A]
  [J.HasSheafCompose (forget A)] [(presheafToSheaf J A).PreservesHomology]

/-- If `S.toCycles` is locally surjective, then the sheafification of `S` is exact. -/
lemma exact_map_presheafToSheaf_of_isLocallySurjective_toCycles
    (S : ShortComplex (Cᵒᵖ ⥤ A)) [IsLocallySurjective J S.toCycles] :
    (S.map (presheafToSheaf J A)).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine IsZero.of_iso ?_ (S.mapHomologyIso (presheafToSheaf J A))
  have := epi_presheafToSheaf_map_of_isLocallySurjective J S.toCycles
  have h0 : (presheafToSheaf J A).map S.homologyπ = 0 := by
    rw [← cancel_epi ((presheafToSheaf J A).map S.toCycles), ← Functor.map_comp,
      S.toCycles_comp_homologyπ, Functor.map_zero, comp_zero]
  exact IsZero.of_epi_eq_zero _ h0

variable [∀ X, AddCommGroup (CA X)] [(forget A).PreservesMonomorphisms]

/-- If every cycle of a short complex of presheaves is locally a boundary, then
`S.toCycles` is locally surjective. -/
omit [HasSheafify J A] [J.WEqualsLocallyBijective A] [J.HasSheafCompose (forget A)]
  [(presheafToSheaf J A).PreservesHomology] in
lemma isLocallySurjective_toCycles_of_imageSieve_mem (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hsub : ∀ {X Y : A} (f g : X ⟶ Y) (x : ToType X), (f - g) x = f x - g x)
    (hS : ∀ (U : C) (x : ToType (S.X₂.obj (op U))), S.g.app (op U) x = 0 →
      imageSieve S.f x ∈ J U) :
    IsLocallySurjective J S.toCycles where
  imageSieve_mem {U} s := by
    have hzero : ∀ {X Y : A} (x : ToType X), (0 : X ⟶ Y) x = 0 := by
      intro X Y x
      simpa using hsub (0 : X ⟶ Y) 0 x
    have hg : S.g.app (op U) (S.iCycles.app (op U) s) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, S.iCycles_g,
        NatTrans.app_zero, hzero]
    refine J.superset_covering ?_ (hS U _ hg)
    rintro V f ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hmono : Function.Injective (S.iCycles.app (op V)) := by
      have : Mono ((forget A).map (S.iCycles.app (op V))) := inferInstance
      exact (mono_iff_injective _).1 this
    apply hmono
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, S.toCycles_i, hy,
      NatTrans.naturality_apply]

/-- If every cycle of a short complex of presheaves is locally a boundary, then its
sheafification is exact. -/
lemma exact_map_presheafToSheaf_of_imageSieve_mem (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hsub : ∀ {X Y : A} (f g : X ⟶ Y) (x : ToType X), (f - g) x = f x - g x)
    (hS : ∀ (U : C) (x : ToType (S.X₂.obj (op U))), S.g.app (op U) x = 0 →
      imageSieve S.f x ∈ J U) :
    (S.map (presheafToSheaf J A)).Exact := by
  have := isLocallySurjective_toCycles_of_imageSieve_mem J S hsub hS
  exact exact_map_presheafToSheaf_of_isLocallySurjective_toCycles J S

end CategoryTheory.Presheaf
