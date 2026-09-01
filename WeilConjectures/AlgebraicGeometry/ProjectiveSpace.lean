/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective space over a base scheme

`ℙ(n; S)` is the projective `n`-space over an arbitrary base scheme `S`, defined as the base
change `S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model `ℙⁿ_ℤ = Proj ℤ[T]` along the structure
morphism of `S`, exactly as Mathlib's affine space `𝔸(n; S)` is defined as `S ×_{Spec ℤ} 𝔸ⁿ_ℤ`.
Here `n : Type u` is the index type of the *homogeneous* coordinates, so that the space Stacks
writes `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`.

Mathlib has no relative projective space to reuse, only the absolute `Proj` of a graded ring,
so everything below is new; the integral model itself is
`Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)`.

## Main definitions

- `AlgebraicGeometry.Proj.projectiveSpaceOverAffine` — the projective space `ℙ^σ_A` over an
  affine base, i.e. `Proj` of the polynomial ring `A[T]` with its total-degree grading.
- `AlgebraicGeometry.Proj.projectiveSpaceOverAffineToSpec` — its structure morphism
  `ℙ^σ_A ⟶ Spec A`.
- `AlgebraicGeometry.ProjectiveSpace` — `ℙ(n; S)` is the projective `n`-space over `S`, with
  structure morphism `ℙ(n; S) ↘ S`.
- `AlgebraicGeometry.ProjectiveSpace.map` — functoriality of `ℙ(n; S)` in the base `S`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.instIsProper` — for a finite index type, the structure
  morphism `ℙ(n; S) ↘ S` is proper.

## Implementation notes

Mathlib does not make the total-degree grading of `MvPolynomial σ A` a global instance, since
one may want to grade by another weight function; it is enabled here as a local instance. To
keep it out of the statements of the results below, `Proj.projectiveSpaceOverAffine σ A` is a plain
definition rather than an abbreviation, so that downstream files need not re-enable the
instance.

Defining `ℙ(n; S)` by base change is the cheap route: it needs no gluing, and properness of
`ℙ(n; S) ↘ S` follows from properness of the integral model by base change. The blueprint's
`def:nagata-relative-projective-space` instead constructs `ℙ^r_X` as the relative `Proj` of
a symmetric algebra, and requires its standard opens to be the relative spectra of the
degree-zero homogeneous localizations. The definition here is intended to be canonical for
everything that only needs `ℙ(n; S)` as a scheme over `S`; the chart interface is what
relative `Proj` would add on top, and the comparison of the two is left to the file that
builds relative `Proj`.

## TODO

- `ℙ(n; Spec A) ≅ Proj.projectiveSpaceOverAffine n A` over `Spec A`, the analogue of
  `AlgebraicGeometry.AffineSpace.SpecIso`. This needs `Proj` to commute with base change,
  which Mathlib does not have, so `Proj.projectiveSpaceOverAffine` and `ProjectiveSpace` are
  for now two unrelated definitions.
- The standard affine charts of `ℙ(n; S)`, i.e. isomorphisms
  `ProjectiveSpace.standardOpen (n ⊕ Unit) S i ≅ 𝔸(n; S)` obtained from `Proj.awayι`. They are
  a prerequisite for proving Chow's lemma. Morphisms *into* a projective space are constructed
  from families of global sections generating the unit ideal, see
  `AlgebraicGeometry.ProjectiveSpace.homOfSections`.

## Blueprint

`ProjectiveSpace` implements `def:nagata-projective-space-base-change` of the Nagata
compactification blueprint, which is the base-change substitute for
`def:nagata-relative-projective-space` described above, and `ProjectiveSpace.instIsProper`
implements `lemma:nagata-projective-space-base-change-proper`. `Proj.projectiveSpaceOverAffine` is
`def:nagata-affine-proj` for a polynomial ring.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

section Affine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (σ : Type u) (A : Type u) [CommRing A]

/-- The projective space `ℙ^σ_A` over an affine base, defined as `Proj` of the polynomial
ring `A[T]` in the variables `σ` with its total-degree grading.
(blueprint: `def:nagata-affine-proj`, for a polynomial ring) -/
def Proj.projectiveSpaceOverAffine : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule σ A)

/-- The structure morphism `ℙ^σ_A ⟶ Spec A` of the projective space over an affine base. -/
def Proj.projectiveSpaceOverAffineToSpec : Proj.projectiveSpaceOverAffine σ A ⟶ Spec (.of A) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ A) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.homogeneousSubmoduleZeroEquiv σ A).toRingHom)

/-- **Projective space over an affine base is proper**: for a finite index type `σ`, the
structure morphism `ℙ^σ_A ⟶ Spec A` is proper. -/
instance Proj.instIsProperProjectiveSpaceOverAffineToSpec [Finite σ] :
    IsProper (Proj.projectiveSpaceOverAffineToSpec σ A) := by
  rw [Proj.projectiveSpaceOverAffineToSpec]
  infer_instance

end Affine

/-- `ℙ(n; S)` is the projective `n`-space over `S`, that is, the base change
`S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model along the structure morphism of `S`.
Note that `n : Type u` indexes the *homogeneous* coordinates, so that the classical `ℙⁿ_S` is
`ℙ(Fin (n + 1); S)`.
(blueprint: `def:nagata-projective-space-base-change`) -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)))

namespace ProjectiveSpace

/-- `ℙ(n; S)` is the projective `n`-space over `S`. -/
scoped[AlgebraicGeometry] notation "ℙ(" n "; " S ")" => ProjectiveSpace n S

variable (n : Type u) (S : Scheme.{u})

@[simps -isSimp]
instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the projective `n`-space over `S` to the integral model `ℙⁿ_ℤ`. -/
def toProjInt : ℙ(n; S) ⟶ Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ) := pullback.snd _ _

/-- A morphism into `ℙ(n; S)` is determined by its composites with the structure morphism to
`S` and with the map to the integral model `ℙⁿ_ℤ`. -/
@[ext 1100]
lemma hom_ext {X : Scheme.{u}} {f g : X ⟶ ℙ(n; S)}
    (h₁ : f ≫ ℙ(n; S) ↘ S = g ≫ ℙ(n; S) ↘ S)
    (h₂ : f ≫ toProjInt n S = g ≫ toProjInt n S) : f = g :=
  pullback.hom_ext h₁ h₂

/-- **`ℙ(n; S)` is proper over `S`**: for a finite index type `n`, the structure morphism
`ℙ(n; S) ↘ S` is proper, being a base change of the proper morphism `ℙⁿ_ℤ ⟶ Spec ℤ`. -/
instance instIsProper [Finite n] : IsProper (ℙ(n; S) ↘ S) := by
  have hZ : terminal.from (Spec (.of (ULift.{u} ℤ))) =
      (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).hom := terminal.hom_ext _ _
  have hP : terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)) =
      Proj.projectiveSpaceOverAffineToSpec n (ULift.{u} ℤ) ≫ terminal.from _ := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) := hZ ▸ inferInstance
  have : IsProper (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ))) :=
    hP ▸ inferInstance
  exact inferInstanceAs (IsProper (pullback.fst _ _))

/-- `ℙ(n; S)` is functorial in the base `S`: `map n f` is the unique morphism making

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
     |                   |
     | ↘                 | ↘
     ↓                   ↓
     S ------- f ------> T
```

commute and compatible with the maps to the integral model, i.e. making

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
        ╲             ╱
    toProjInt     toProjInt
          ╲       ╱
           ↘ ℙⁿ_ℤ ↙
```

commute as well. -/
def map {S T : Scheme.{u}} (f : S ⟶ T) : ℙ(n; S) ⟶ ℙ(n; T) :=
  pullback.lift (ℙ(n; S) ↘ S ≫ f) (toProjInt n S) (terminal.hom_ext _ _)

/-- `map n f` is a morphism over `f`:

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
     |                   |
     | ↘                 | ↘
     ↓                   ↓
     S ------- f ------> T
```

commutes. -/
@[reassoc (attr := simp)]
lemma map_over {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ ℙ(n; T) ↘ T = ℙ(n; S) ↘ S ≫ f :=
  pullback.lift_fst _ _ _

/-- `map n f` is compatible with the maps to the integral model `ℙⁿ_ℤ`:

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
        ╲             ╱
    toProjInt     toProjInt
          ╲       ╱
           ↘ ℙⁿ_ℤ ↙
```

commutes. -/
@[reassoc (attr := simp)]
lemma map_toProjInt {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ toProjInt n T = toProjInt n S :=
  pullback.lift_snd _ _ _

@[simp]
lemma map_id : map n (𝟙 S) = 𝟙 ℙ(n; S) := by
  ext1 <;> simp

@[reassoc, simp]
lemma map_comp {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    map n (f ≫ g) = map n f ≫ map n g := by
  ext1 <;> simp

end ProjectiveSpace

end AlgebraicGeometry
