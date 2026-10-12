/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedScheme
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Cohomological correspondences

Let `X` be a scheme over a base `s` with structure morphism `aX : X ⟶ s`, and `K` an object of
the derived category `D(X_ét, A)` of étale sheaves. A *cohomological correspondence* on `K` is a
scheme `C` with two morphisms `c₁ c₂ : C ⟶ X` over `s`, i.e. `c = (c₁, c₂) : C ⟶ X ×_s X`,
together with a morphism `u : c₂^* K ⟶ Rc₁^! K` in `D(C_ét, A)`. Here `c₂` is the pullback
leg and `c₁` the exceptional leg. The *graph correspondence* of an endomorphism `h : X ⟶ X`
over `s` and a morphism `v : h^* K ⟶ K` is `C = X`, `c₁ = 𝟙`, `c₂ = h`, `u = v`; its fixed scheme
is the fixed scheme `Fix(h)` of `h`.

## Main definitions

- `AlgebraicGeometry.Etale.CohomologicalCorrespondence`: a cohomological correspondence
  (blueprint `def-trf-correspondence`).
- `AlgebraicGeometry.Etale.CohomologicalCorrespondence.fixedScheme`: its fixed scheme
  `Fix(c) = C ×_{X ×_s X, c, Δ_X} X` (blueprint `def-trf-fixed-scheme`).
- `AlgebraicGeometry.Etale.CohomologicalCorrespondence.graph`: the graph correspondence of
  `(h, v)` (blueprint `def-trf-graph-correspondence`), whose fixed scheme is `Fix(h)`
  (`AlgebraicGeometry.Etale.CohomologicalCorrespondence.fixedScheme_graph`).

## Implementation notes

The pullback leg is the derived pullback `D((c₂)^*[A])` along `c₂`, which is the derived
functor `L((c₂)^*[A])` since `c₂^*` is exact
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`); using it needs no
monoidal structure on `A`. The exceptional leg is the ambient exceptional inverse image
`R(c₁)^![A]`, which needs `c₁` to admit a compactification and `R(c₁)_![A]` to be a left
adjoint; both are recorded as instance fields. The blueprint's admissibility of `c₁`
(`def-trf-admissibility`, the existence of the adjunction `Rc₁_! ⊣ Rc₁^!` with its exchange
isomorphisms) is a theorem for separated finite type morphisms, and is not part of the data.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {X s : Scheme.{u}} (aX : X ⟶ s) (K : DerivedCategory (Sheaf X.smallEtaleTopology A))

/-- Blueprint `def-trf-correspondence`: Cohomological correspondence.

A cohomological correspondence on an object `K` of `D(X_ét, A)`, for `X` over `s` via `aX`: a
separated scheme `C` of finite type over `s` with morphisms `c = (c₁, c₂) : C ⟶ X ×_s X`, that
is `c₁ c₂ : C ⟶ X` with `c₁ ≫ aX = c₂ ≫ aX`, and a morphism `u : c₂^* K ⟶ Rc₁^! K` in
`D(C_ét, A)`. The leg `c₂` is the pullback leg and `c₁` the exceptional leg. -/
structure CohomologicalCorrespondence where
  /-- The correspondence scheme `C`. -/
  C : Scheme.{u}
  /-- The exceptional leg `c₁ : C ⟶ X`. -/
  c₁ : C ⟶ X
  /-- The pullback leg `c₂ : C ⟶ X`. -/
  c₂ : C ⟶ X
  /-- The two legs are morphisms over `s`, so that `c = (c₁, c₂) : C ⟶ X ×_s X`. -/
  w : c₁ ≫ aX = c₂ ≫ aX
  /-- `C` is separated over `s`. -/
  isSeparated : IsSeparated (c₁ ≫ aX)
  /-- `C` is locally of finite type over `s`. -/
  locallyOfFiniteType : LocallyOfFiniteType (c₁ ≫ aX)
  /-- `C` is quasi-compact over `s`. -/
  quasiCompact : QuasiCompact (c₁ ≫ aX)
  /-- The exceptional leg admits a compactification. -/
  [hasCompactification : HasCompactification c₁]
  /-- The derived lower shriek along the exceptional leg is a left adjoint, so that the
  exceptional inverse image `Rc₁^!` is defined. -/
  [isLeftAdjoint : (R(c₁)_![A]).IsLeftAdjoint]
  /-- The cohomological correspondence `u : c₂^* K ⟶ Rc₁^! K`. -/
  u : (D((c₂)^*[A])).obj K ⟶ (R(c₁)^![A]).obj K

namespace CohomologicalCorrespondence

attribute [instance] hasCompactification isLeftAdjoint

variable {A aX K} (c : CohomologicalCorrespondence A aX K)

/-- The fixed scheme `Fix(c) = C ×_{X ×_s X, c, Δ_X} X` of a cohomological correspondence
(blueprint `def-trf-fixed-scheme`). -/
noncomputable abbrev fixedScheme : Scheme.{u} :=
  Scheme.fixedScheme aX c.c₁ c.c₂ c.w

section Graph

variable (A) [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

/-- Blueprint `def-trf-graph-correspondence`: Graph correspondence.

The graph correspondence of a separated finite type endomorphism `h : X ⟶ X` over `s` and a
morphism `v : h^* K ⟶ K`: `C = X`, `c₁ = 𝟙 X`, `c₂ = h` and `u = v`, composed with the
identification `R(𝟙 X)^! ≅ 𝟭` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`). Its
fixed scheme is `Fix(h)` (`fixedScheme_graph`). -/
noncomputable def graph [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[A])).obj K ⟶ K) :
    CohomologicalCorrespondence A aX K where
  C := X
  c₁ := 𝟙 X
  c₂ := h
  w := by rw [hh, Category.id_comp]
  isSeparated := by rwa [Category.id_comp]
  locallyOfFiniteType := by rwa [Category.id_comp]
  quasiCompact := by rwa [Category.id_comp]
  u := v ≫ (rightDerivedUpperShriekIdIso A X).inv.app K

variable {A} [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]

@[simp]
lemma graph_C (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[A])).obj K ⟶ K) :
    (graph A h hh v).C = X :=
  rfl

@[simp]
lemma graph_c₁ (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[A])).obj K ⟶ K) :
    (graph A h hh v).c₁ = 𝟙 X :=
  rfl

@[simp]
lemma graph_c₂ (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[A])).obj K ⟶ K) :
    (graph A h hh v).c₂ = h :=
  rfl

/-- The fixed scheme of the graph correspondence of `h` is the fixed scheme `Fix(h)` of `h`,
the scheme-theoretic equalizer of `𝟙 X` and `h` (blueprint `def-trf-graph-correspondence`). -/
lemma fixedScheme_graph (h : X ⟶ X) (hh : h ≫ aX = aX) (v : (D((h)^*[A])).obj K ⟶ K) :
    (graph A h hh v).fixedScheme = Hom.fixedScheme aX h hh :=
  rfl

end Graph

end CohomologicalCorrespondence

end AlgebraicGeometry.Etale
