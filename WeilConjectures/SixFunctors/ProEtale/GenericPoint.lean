/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits

/-!
# The geometric generic point in the pro-étale site

Let `X` be an integral scheme with function field `K` and let `Kˢᵉᵖ = SeparableClosure K`. The
composite `Spec Kˢᵉᵖ ⟶ Spec K ⟶ X` is weakly étale: `Spec K ⟶ X` is the spectrum of a
localization of the ring of an affine open (ind-Zariski, hence weakly étale), and `K → Kˢᵉᵖ` is
a separable algebraic extension, hence ind-étale. This gives an object
`AlgebraicGeometry.Scheme.ProEt.genericPointSep X` of `X_proét`, on which the Galois group
`Gal(Kˢᵉᵖ/K)` acts (on the right).

A nonempty weakly étale scheme over a separably closed field has a section
(`AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale_of_isSepClosed`), so every covering
sieve of an object of `X_proét` whose underlying scheme is the spectrum of a separably closed
field contains the identity. For such an object `T`, taking sections over `T` preserves
epimorphisms of sheaves with values in a concrete category, and evaluating the map from a
presheaf to its sheafification at `T` is bijective.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.genericPointSep`: the object `Spec Kˢᵉᵖ ⟶ X` of `X_proét`.
- `AlgebraicGeometry.Scheme.ProEt.genericPointSepAut`: the action of `Gal(Kˢᵉᵖ/K)` on it.

## Main statements

- `Algebra.IndEtale.of_isSeparable`: a separable algebraic field extension is ind-étale.
- `AlgebraicGeometry.Scheme.weaklyEtale_fromSpecStalk`: `Spec 𝒪_{X,x} ⟶ X` is weakly étale.
- `AlgebraicGeometry.Scheme.ProEt.id_mem_of_mem_topology_of_isSepClosed`: covering sieves of an
  object whose underlying scheme is the spectrum of a separably closed field contain `𝟙`.
- `AlgebraicGeometry.Scheme.ProEt.genericPointSepAut_mul`:
  `genericPointSepAut X (σ * τ) = genericPointSepAut X σ ≫ genericPointSepAut X τ`.
- `AlgebraicGeometry.ProEtale.preservesEpimorphisms_sheafSections_of_forall_id_mem`,
  `AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_forall_id_mem`, and their
  specialisations to `genericPointSep`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

/-- A separable algebraic field extension `L / K` is ind-étale: every finitely generated
`K`-subalgebra of `L` is a finite separable field extension of `K`, hence étale. -/
theorem Algebra.IndEtale.of_isSeparable (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] : Algebra.IndEtale K L :=
  .of_forall_fg_etale fun A hA ↦ by
    let := (Subalgebra.isField_of_algebraic A).toField
    have : Algebra.IsSeparable K A := .of_algHom K L A.val
    have : Algebra.FiniteType K A := hA.finiteType
    have : Algebra.FormallyEtale K A := .of_isSeparable K A
    exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

namespace AlgebraicGeometry

/-- The canonical morphism `Spec 𝒪_{X,x} ⟶ X` is weakly étale: on an affine open neighbourhood
`U` of `x`, it is the spectrum of the localization `Γ(X, U) → 𝒪_{X,x}`, which is ind-Zariski. -/
instance Scheme.weaklyEtale_fromSpecStalk (X : Scheme.{u}) (x : X) :
    WeaklyEtale (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk]
  let := (X.presheaf.germ U x hxU).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.IndZariski Γ(X, U) (X.presheaf.stalk x) :=
    .of_isLocalization _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have : WeaklyEtale (Spec.map (X.presheaf.germ U x hxU)) :=
    weaklyEtale_SpecMap_algebraMap (R := Γ(X, U)) (S := X.presheaf.stalk x)
  infer_instance

namespace Scheme.ProEt

variable {X : Scheme.{u}}

end Scheme.ProEt

namespace ProEtale

variable {X : Scheme.{u}}

section Concrete

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization A]

end Concrete

section Sheafify

variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [HasSheafify (Scheme.ProEt.topology X) A]
  [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
  [(Scheme.ProEt.topology X).PreservesSheafification (CategoryTheory.forget A)]

end Sheafify

end ProEtale

namespace Scheme.ProEt

variable (X : Scheme.{u}) [IsIntegral X]

end Scheme.ProEt

namespace ProEtale

variable (X : Scheme.{u}) [IsIntegral X]

end ProEtale

end AlgebraicGeometry
