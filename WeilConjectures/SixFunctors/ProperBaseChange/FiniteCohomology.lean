/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.DerivedFunctors.Full
public import WeilConjectures.SixFunctors.DerivedFunctors.CategoryConstruction

/-!

# Finite étale cohomology, ordinary and with compact support

This file introduces derived global sections and étale cohomology, compactly supported
global sections and compactly supported étale cohomology (via the exceptional direct
image `Rp_!` of `WeilConjectures.SixFunctors.DerivedFunctors.Full`), the canonical
comparison `Rf_! ⟶ Rf_*` (an isomorphism for proper `f`), and states the finiteness
theorems for constructible complexes with finite coefficients over an algebraically
closed field:

- the *compactly supported* finiteness theorem, for a separated finite-type scheme; this
  is the primary statement, since compactly supported cohomology is the formulation
  stable under compactification and exceptional direct image;
- the *ordinary* finiteness theorem for a proper scheme, which follows via the canonical
  identification `Rp_! ≅ Rp_*`.

## Main definitions

- `AlgebraicGeometry.Etale.globalSections`: the global sections functor `Γ(X_ét, -)`,
  evaluation at the terminal object `𝟙 X` of the small étale site.
- `AlgebraicGeometry.Etale.derivedGlobalSections`: derived global sections
  `RΓ(X_ét, -) : D(X_ét) ⥤ D(A)`.
- `AlgebraicGeometry.Etale.cohomologyFunctor`: étale cohomology
  `H^n_ét(X, -) := H^n(RΓ(X, -))`.
- `AlgebraicGeometry.Etale.lowerShriekToLowerStar`: the canonical comparison
  `ι_f : Rf_! ⟶ Rf_*` for `f` admitting a compactification, an isomorphism for proper
  `f` (`Etale.isIso_lowerShriekToLowerStar`).
- `AlgebraicGeometry.Etale.derivedCompactlySupportedGlobalSections`: compactly supported
  derived global sections `RΓ_c(X, -) := RΓ(Spec k, Rp_! -)` for `p : X ⟶ Spec k`.
- `AlgebraicGeometry.Etale.compactlySupportedCohomologyFunctor`: compactly supported
  étale cohomology `H^n_c(X, -)`.
- `AlgebraicGeometry.Etale.compactlySupportedToGlobalSections` and
  `Etale.compactlySupportedCohomologyToCohomology`: the canonical maps
  `RΓ_c(X, K) ⟶ RΓ(X, K)` and `H^n_c(X, K) ⟶ H^n_ét(X, K)`, isomorphisms for `X`
  proper over `k`.

## Main statements

- `AlgebraicGeometry.Etale.finite_compactlySupportedCohomology`: for `X` separated of
  finite type over an algebraically closed field, `Λ` a finite commutative ring and
  `K ∈ D^b_c(X_ét, Λ)`, all `H^n_c(X, K)` are finite `Λ`-modules.
- `AlgebraicGeometry.Etale.finite_cohomology_of_isProper`: for `X` proper over an
  algebraically closed field, all `H^n_ét(X, K)` are finite `Λ`-modules.

## References

- Stacks Project, Section 63.9, *Derived lower shriek via compactifications*,
  <https://stacks.math.columbia.edu/tag/0F7H>
- Stacks Project, Section 63.12, *Compactly supported cohomology*,
  <https://stacks.math.columbia.edu/tag/0GJY>
- Stacks Project, Section 63.15, finite compactly supported cohomology,
  <https://stacks.math.columbia.edu/tag/0GLG>

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

variable [∀ (T : Scheme.{u}), HasWeakSheafify T.smallEtaleTopology A]
  [∀ (T : Scheme.{u}), HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology A)]
  [HasDerivedCategory.{w} A]

section GlobalSections

variable (X : Scheme.{u})

/-- The global sections functor `Γ(X_ét, -)` on étale sheaves: evaluation at the
terminal object `𝟙 X` of the small étale site of `X`. -/
noncomputable def Etale.globalSections : Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf _ _ ⋙ (evaluation X.Etaleᵒᵖ A).obj (op (Scheme.Etale.mk (𝟙 X)))

/-- Global sections is an additive functor: it acts on morphisms by evaluating the
underlying natural transformation, which is compatible with the objectwise addition. -/
instance : (Etale.globalSections A X).Additive where
  map_add := rfl

/-- The derived global sections `RΓ(X_ét, -) : D(X_ét) ⥤ D(A)`: the total right derived
functor of the global sections functor on the unbounded derived categories, computed via
K-injective resolutions. -/
noncomputable def Etale.derivedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  (Etale.globalSections A X).rightDerivedFunctor

/-- Étale cohomology `H^n_ét(X, -) : D(X_ét) ⥤ A`: the `n`-th homology of the derived
global sections. For a sheaf `F` placed in degree `0` this recovers the usual étale
cohomology `H^n_ét(X, F)`. -/
noncomputable def Etale.cohomologyFunctor (n : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ A :=
  Etale.derivedGlobalSections A X ⋙ DerivedCategory.homologyFunctor A n

/-- The Leray composition isomorphism `RΓ(Y_ét, Rf_* K) ≅ RΓ(X_ét, K)` for a morphism
`f : X ⟶ Y`.

Mathematically, at the underived level `Γ_Y ∘ f_*` is canonically isomorphic to `Γ_X`
(the sections of `f_* F` over `𝟙 Y` are the sections of `F` over the base change
`Y ×_Y X ≅ X`), and `f_*` preserves K-injective complexes since it is right adjoint to
the exact pullback `f^*`; hence the composition of the derived functors is the derived
functor of the composition. Its formalization is part of the pending composition
infrastructure for the derived functors and is not yet available. -/
noncomputable def Etale.derivedGlobalSectionsComp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale.rightDerivedLowerStar A f ⋙ Etale.derivedGlobalSections A Y ≅
      Etale.derivedGlobalSections A X :=
  sorry

end GlobalSections

section LowerShriekComparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The canonical comparison `ι_f : Rf_! ⟶ Rf_*` from the exceptional direct image to
the derived pushforward, for a morphism `f` admitting a compactification.

Mathematically, after choosing a compactification `X --j--> X̄ --f̄--> Y` (with `j` an
open immersion and `f̄` proper), it is induced by the canonical monomorphism
`j_! ⟶ j_*` from extension by zero to pushforward, using `Rf_! = Rf̄_* ∘ j_!` and the
composition isomorphism `Rf̄_* ∘ Rj_* ≅ Rf_*`; the resulting transformation is
independent of the chosen compactification. Its formalization is part of the pending
composition/independence infrastructure for the lower shriek (see the TODOs in
`WeilConjectures.SixFunctors.LowerShriek.Etale`) and is not yet available. -/
noncomputable def Etale.lowerShriekToLowerStar :
    Etale.rightDerivedLowerShriek A f ⟶ Etale.rightDerivedLowerStar A f :=
  sorry

/-- For a proper morphism `f`, the canonical comparison `ι_f : Rf_! ⟶ Rf_*` is an
isomorphism: a proper morphism is a compactification of itself, with `j = 𝟙 X`. -/
theorem Etale.isIso_lowerShriekToLowerStar [IsProper f] :
    IsIso (Etale.lowerShriekToLowerStar A f) :=
  sorry

end LowerShriekComparison

section CompactSupport

variable (k : Type u) [Field k]
variable {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [HasCompactification p]

/-- The compactly supported derived global sections
`RΓ_c(X, -) := RΓ(Spec k, Rp_! -) : D(X_ét) ⥤ D(A)` of a scheme `X` with a structure
morphism `p : X ⟶ Spec k` admitting a compactification (by Nagata, any separated
finite-type `p` qualifies). -/
noncomputable def Etale.derivedCompactlySupportedGlobalSections :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  Etale.rightDerivedLowerShriek A p ⋙ Etale.derivedGlobalSections A (Spec (.of k))

/-- Compactly supported étale cohomology `H^n_c(X, -) : D(X_ét) ⥤ A`: the `n`-th
homology of the compactly supported derived global sections. -/
noncomputable def Etale.compactlySupportedCohomologyFunctor (n : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ A :=
  Etale.derivedCompactlySupportedGlobalSections A k p ⋙ DerivedCategory.homologyFunctor A n

/-- The canonical comparison `RΓ_c(X, K) ⟶ RΓ(X, K)` from compactly supported to
ordinary derived global sections, induced by `ι_p : Rp_! ⟶ Rp_*` and the Leray
composition isomorphism. -/
noncomputable def Etale.compactlySupportedToGlobalSections :
    Etale.derivedCompactlySupportedGlobalSections A k p ⟶ Etale.derivedGlobalSections A X :=
  Functor.whiskerRight (Etale.lowerShriekToLowerStar A p)
      (Etale.derivedGlobalSections A (Spec (.of k))) ≫
    (Etale.derivedGlobalSectionsComp A p).hom

/-- For `X` proper over `k`, compactly supported and ordinary derived global sections
agree: the canonical comparison `RΓ_c(X, K) ⟶ RΓ(X, K)` is an isomorphism. -/
theorem Etale.isIso_compactlySupportedToGlobalSections [IsProper p] :
    IsIso (Etale.compactlySupportedToGlobalSections A k p) := by
  haveI := Etale.isIso_lowerShriekToLowerStar A p
  simp only [Etale.compactlySupportedToGlobalSections]
  infer_instance

/-- The canonical comparison `H^n_c(X, K) ⟶ H^n_ét(X, K)` from compactly supported to
ordinary étale cohomology. -/
noncomputable def Etale.compactlySupportedCohomologyToCohomology (n : ℤ) :
    Etale.compactlySupportedCohomologyFunctor A k p n ⟶ Etale.cohomologyFunctor A X n :=
  Functor.whiskerRight (Etale.compactlySupportedToGlobalSections A k p)
    (DerivedCategory.homologyFunctor A n)

/-- For `X` proper over `k`, compactly supported and ordinary étale cohomology agree:
the canonical comparison `H^n_c(X, K) ⟶ H^n_ét(X, K)` is an isomorphism. -/
theorem Etale.isIso_compactlySupportedCohomologyToCohomology [IsProper p] (n : ℤ) :
    IsIso (Etale.compactlySupportedCohomologyToCohomology A k p n) := by
  haveI := Etale.isIso_compactlySupportedToGlobalSections A k p
  simp only [Etale.compactlySupportedCohomologyToCohomology]
  infer_instance

end CompactSupport

section Finiteness

variable (Λ : Type u) [CommRing Λ] [Finite Λ]

/- Additional infrastructure needed for the bounded constructible category `D^b_c`:
sheafification on the localized sites and pointwise left Kan extensions, with
coefficients in the finite ring `Λ`. -/
variable [∀ (T : Scheme.{u}), HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ (T : Scheme.{u}) (U : T.Etale),
    HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T : Scheme.{u}),
    HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasDerivedCategory.{w} (ModuleCat.{u} Λ)]

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- **Finite compactly supported cohomology** (Stacks Project, Tag 0GLG): let `X` be
separated of finite type over an algebraically closed field `k` (so its structure
morphism `p` is quasi-compact and admits a compactification by Nagata), let `Λ` be a
finite commutative ring and let `K ∈ D^b_c(X_ét, Λ)`. Then `H^n_c(X, K)` is a finite
`Λ`-module for every `n`. Compact support is essential: this is the finiteness statement
that is stable under compactification and exceptional direct image. -/
theorem Etale.finite_compactlySupportedCohomology
    (p : X ⟶ Spec (.of k)) [HasCompactification p] [QuasiCompact p]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : Etale.boundedConstructible (ModuleCat.{u} Λ) X K) (n : ℤ) :
    Module.Finite Λ
      ((Etale.compactlySupportedCohomologyFunctor (ModuleCat.{u} Λ) k p n).obj K) :=
  sorry

/-- **Finite ordinary cohomology for proper schemes**: let `X` be proper over an
algebraically closed field `k`, let `Λ` be a finite commutative ring and let
`K ∈ D^b_c(X_ét, Λ)`. Then `H^n_ét(X, K)` is a finite `Λ`-module for every `n`.

Mathematically this follows from `Etale.finite_compactlySupportedCohomology` by
transporting finiteness along the isomorphism
`Etale.isIso_compactlySupportedCohomologyToCohomology`, since `X` is proper over `k`. -/
theorem Etale.finite_cohomology_of_isProper
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : Etale.boundedConstructible (ModuleCat.{u} Λ) X K) (n : ℤ) :
    Module.Finite Λ ((Etale.cohomologyFunctor (ModuleCat.{u} Λ) X n).obj K) :=
  sorry

end Finiteness

end AlgebraicGeometry
