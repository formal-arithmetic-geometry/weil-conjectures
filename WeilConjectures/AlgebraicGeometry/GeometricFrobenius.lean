/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import WeilConjectures.AlgebraicGeometry.SpecAlgebraicClosure
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

/-!

# The geometric fiber of a scheme over a finite field and its Galois Frobenius

Let `k` be a field with algebraic closure `k̄`. For a scheme `X₀` over `k` with structure
morphism `f : X₀ ⟶ Spec k`, this file constructs the geometric fiber

`X := X₀ ×_{Spec k} Spec k̄`

with its projection `p_X : X ⟶ X₀` to the model over `k` and its structure morphism
`a_X : X ⟶ Spec k̄` over the algebraic closure, and the base change
`X₀ ×_{Spec k} Spec k̄ ⟶ Y₀ ×_{Spec k} Spec k̄` of a morphism `X₀ ⟶ Y₀` over `k`.

If `k` is finite, the geometric Frobenius `σ⁻¹ : x ↦ x ^ (1 / #k)` of `k̄`
(`FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`) induces an automorphism `σ` of `Spec k̄`
over `Spec k`, and the *geometric Galois Frobenius* of the geometric fiber is the base change

`g_X := 𝟙 X₀ × σ : X ≅ X`.

It commutes with the projection to the model, `g_X ≫ p_X = p_X`, and is *semilinear* over
`k̄`: it does not commute with the structure morphism `a_X` but satisfies
`g_X ≫ a_X = a_X ≫ σ`, and the resulting Frobenius square

```
        g_X
  X ---------> X
  |            |
a_X          a_X
  v            v
Spec k̄ --σ--> Spec k̄
```

is Cartesian (`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius`). This
square is the input for the compact-support base change isomorphisms which transport Weil
structures through `Rf_!` later on. The base change of a morphism over `k` commutes with the
geometric Galois Frobenii
(`AlgebraicGeometry.Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius`), which is
what transports Weil structures through pullbacks.

## Implementation notes

The classical Frobenius dictionary distinguishes several Frobenii. The one constructed
here is the *geometric Galois Frobenius* `𝟙 X₀ × σ`, which acts through the coefficients
only and is not a morphism of `k̄`-schemes. It is not the relative `#k`-power Frobenius
`Fr_{X₀} × 𝟙` of `X` over `k̄`. Since the absolute Frobenius acts as the identity on the
étale topos and `Fr^{abs}_X = (Fr_{X₀} × 𝟙) ∘ (𝟙 X₀ × σ⁻¹)`, the two induce canonically
isomorphic pullback endofunctors `(𝟙 X₀ × σ)^* ≅ (Fr_{X₀} × 𝟙)^*`, so they define
equivalent categories of Weil sheaves; the Galois version is used here because its
Frobenius square is Cartesian, which is what the compact-support base change needs.
Constructing the comparison isomorphism with `(Fr_{X₀} × 𝟙)^*` — needed for the Lefschetz
trace formula, whose intersection-theoretic side requires the `k̄`-linear endomorphism
`Fr_{X₀} × 𝟙` — is left as a TODO.

The automorphism `σ` is `Spec` of the ring automorphism `x ↦ x ^ (1 / #k)` of `k̄`, so pulling
back a function along `g_X = 𝟙 X₀ × σ` applies the geometric Frobenius to its coefficients; this
is the automorphism `γ_X` of the blueprint, induced by `σ_geom`, and not its inverse.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.geometricFiber`: the geometric fiber
  `X = X₀ ×_{Spec k} Spec k̄` of a scheme over `k`, with its projection
  `geometricFiberProj` to the model and its structure morphism
  `geometricFiberToAlgebraicClosure` over `k̄`.
- `AlgebraicGeometry.Scheme.Hom.geometricFiberMap`: the base change to `k̄` of a morphism of
  schemes over `k`.
- `AlgebraicGeometry.specGeometricFrobenius`: the automorphism `σ` of `Spec k̄` induced by
  the geometric Frobenius of the algebraic closure of a finite field.
- `AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`: the geometric Galois Frobenius
  `g_X = 𝟙 X₀ × σ` of the geometric fiber.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius`: the Frobenius square
  is Cartesian.
- `AlgebraicGeometry.Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius`: base change
  to `k̄` commutes with the geometric Galois Frobenii.
- `AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`: the
  square formed by the base change `φ̄` and the geometric Galois Frobenii is cartesian.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

open FiniteField Scheme

section AlgebraicClosure

variable {k : Type u} [Field k]

namespace Scheme.Hom

variable {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The geometric fiber `X := X₀ ×_{Spec k} Spec k̄` of a scheme `X₀` over a field `k`
with structure morphism `f : X₀ ⟶ Spec k`. -/
def geometricFiber : Scheme.{u} :=
  pullback f (Scheme.specAlgebraicClosure k).hom

/-- The projection `p_X : X ⟶ X₀` from the geometric fiber to the model over the base
field. -/
def geometricFiberProj : f.geometricFiber ⟶ X₀ :=
  pullback.fst f (Scheme.specAlgebraicClosure k).hom

/-- The structure morphism `a_X : X ⟶ Spec k̄` of the geometric fiber over the algebraic
closure. -/
def geometricFiberToAlgebraicClosure :
    f.geometricFiber ⟶ Spec (.of (AlgebraicClosure k)) :=
  pullback.snd f (Scheme.specAlgebraicClosure k).hom

/-- The defining square of the geometric fiber commutes:

```
        p_X
    X ──────▶ X₀
    │          │
  a_X          f
    ▼          ▼
  Spec k̄ ───▶ Spec k
```

that is `p_X ≫ f = a_X ≫ (Spec k̄ ⟶ Spec k)`. -/
@[reassoc]
theorem geometricFiber_condition :
    f.geometricFiberProj ≫ f =
      f.geometricFiberToAlgebraicClosure ≫ (Scheme.specAlgebraicClosure k).hom :=
  pullback.condition

variable {f} {Y₀ Z₀ : Scheme.{u}} {g : Y₀ ⟶ Spec (.of k)} {e : Z₀ ⟶ Spec (.of k)}

/-- The base change `φ × 𝟙 : X₀ ×_{Spec k} Spec k̄ ⟶ Y₀ ×_{Spec k} Spec k̄` of a morphism
`φ : X₀ ⟶ Y₀` of schemes over `k` to the algebraic closure. -/
def geometricFiberMap (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) : f.geometricFiber ⟶ g.geometricFiber :=
  pullback.map _ _ _ _ φ (𝟙 _) (𝟙 _) (by simp [h]) (by simp)

/-- The base change `φ × 𝟙` lies over `φ`: `(φ × 𝟙) ≫ p_Y = p_X ≫ φ`. -/
@[reassoc (attr := simp)]
theorem geometricFiberMap_comp_geometricFiberProj (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) :
    geometricFiberMap φ h ≫ g.geometricFiberProj = f.geometricFiberProj ≫ φ :=
  pullback.lift_fst _ _ _

/-- The base change `φ × 𝟙` is a morphism over `k̄`: `(φ × 𝟙) ≫ a_Y = a_X`. -/
@[reassoc (attr := simp)]
theorem geometricFiberMap_comp_geometricFiberToAlgebraicClosure (φ : X₀ ⟶ Y₀)
    (h : φ ≫ g = f) :
    geometricFiberMap φ h ≫ g.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure := by
  simp [geometricFiberMap, geometricFiberToAlgebraicClosure]

/-- The base change of the identity is the identity. -/
@[simp]
theorem geometricFiberMap_id : geometricFiberMap (𝟙 X₀) (Category.id_comp f) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [geometricFiberMap, geometricFiber]

/-- Base change to `k̄` is functorial: `(φ ≫ ψ) × 𝟙 = (φ × 𝟙) ≫ (ψ × 𝟙)`. -/
@[reassoc]
theorem geometricFiberMap_comp (φ : X₀ ⟶ Y₀) (ψ : Y₀ ⟶ Z₀) (h : φ ≫ g = f) (h' : ψ ≫ e = g) :
    geometricFiberMap (φ ≫ ψ) (by rw [Category.assoc, h', h]) =
      geometricFiberMap φ h ≫ geometricFiberMap ψ h' := by
  apply pullback.hom_ext <;> simp [geometricFiberMap]

/-- The base change square of `φ` to the algebraic closure is Cartesian:

```
        φ × 𝟙
    X ──────────▶ Y
    │             │
  p_X           p_Y
    ▼             ▼
    X₀ ─────────▶ Y₀
           φ
```
-/
theorem isPullback_geometricFiberMap (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) :
    IsPullback (geometricFiberMap φ h) f.geometricFiberProj g.geometricFiberProj φ := by
  subst h
  refine IsPullback.of_right (h₁₂ := g.geometricFiberToAlgebraicClosure) (h₂₂ := g)
    (v₁₃ := (Scheme.specAlgebraicClosure k).hom) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback g _).flip
  rw [geometricFiberMap_comp_geometricFiberToAlgebraicClosure]
  exact (IsPullback.of_hasPullback (φ ≫ g) _).flip

/-- The base change `φ × 𝟙` of a morphism `φ` with a property stable under base change has
the same property. -/
theorem geometricFiberMap_of_isStableUnderBaseChange {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) (hφ : P φ) :
    P (geometricFiberMap φ h) :=
  P.of_isPullback (isPullback_geometricFiberMap φ h).flip hφ

/-! The base change to `k̄` of an open immersion, separated, quasi-compact or locally of finite
type morphism is again one, these properties being stable under base change. -/

instance (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [IsOpenImmersion φ] :
    IsOpenImmersion (geometricFiberMap φ h) :=
  geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion) φ h ‹_›

instance (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [IsSeparated φ] :
    IsSeparated (geometricFiberMap φ h) :=
  geometricFiberMap_of_isStableUnderBaseChange (P := @IsSeparated) φ h ‹_›

instance (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [QuasiCompact φ] :
    QuasiCompact (geometricFiberMap φ h) :=
  geometricFiberMap_of_isStableUnderBaseChange (P := @QuasiCompact) φ h ‹_›

instance (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [LocallyOfFiniteType φ] :
    LocallyOfFiniteType (geometricFiberMap φ h) :=
  geometricFiberMap_of_isStableUnderBaseChange (P := @LocallyOfFiniteType) φ h ‹_›

end Scheme.Hom

end AlgebraicClosure

section Frobenius

variable (k : Type u) [Field k] [Finite k]

/-- The automorphism `σ` of `Spec k̄` induced by the geometric Frobenius of the algebraic
closure of a finite field `k`, the image under `Spec` of the ring isomorphism
`FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`. All Frobenius operators of the Weil
formalism are built from this single automorphism. -/
def specGeometricFrobenius :
    Spec (.of (AlgebraicClosure k)) ≅ Spec (.of (AlgebraicClosure k)) :=
  letI := Fintype.ofFinite k
  Scheme.Spec.mapIso
    (geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)).toRingEquiv.toCommRingCatIso.op

/-- The underlying morphism of the automorphism `σ` of `Spec k̄` is the image under `Spec`
of the geometric Frobenius. This is not a `simp` lemma: the composites of `σ` are
simplified by `specGeometricFrobenius_hom_comp_specAlgebraicClosure` and by the
`Scheme.Hom.geometricGaloisFrobenius` lemmas instead. -/
theorem specGeometricFrobenius_hom :
    letI := Fintype.ofFinite k
    (specGeometricFrobenius k).hom =
      Spec.map (CommRingCat.ofHom
        (geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)).toRingEquiv.toRingHom) :=
  rfl

/-- The geometric Frobenius on `Spec k̄` is an automorphism over `Spec k`: the geometric
Frobenius of the algebraic closure fixes the finite base field pointwise. -/
@[reassoc (attr := simp)]
theorem specGeometricFrobenius_hom_comp_specAlgebraicClosure :
    (specGeometricFrobenius k).hom ≫ (Scheme.specAlgebraicClosure k).hom =
      (Scheme.specAlgebraicClosure k).hom := by
  let := Fintype.ofFinite k
  simp only [specGeometricFrobenius_hom, Scheme.specAlgebraicClosure, Over.mk_hom,
    ← Spec.map_comp]
  congr 1
  ext x
  simp

namespace Scheme.Hom

variable {k} {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The geometric Galois Frobenius `g_X := 𝟙 X₀ × σ` of the geometric fiber
`X = X₀ ×_{Spec k} Spec k̄` of a scheme over a finite field, acting through the geometric
Frobenius on the coefficients only. It is an automorphism of `X` semilinear over `k̄`: it
commutes with the projection to the model `X₀`
(`geometricGaloisFrobenius_hom_comp_geometricFiberProj`) but commutes with the structure
morphism `a_X` only up to `σ`
(`geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure`). It is not the
relative `#k`-power Frobenius of `X` over `k̄`, see the module implementation notes. -/
def geometricGaloisFrobenius : f.geometricFiber ≅ f.geometricFiber :=
  asIso (pullback.map f (Scheme.specAlgebraicClosure k).hom f
    (Scheme.specAlgebraicClosure k).hom (𝟙 X₀) (specGeometricFrobenius k).hom
    (𝟙 (Spec (.of k))) (by simp) (by simp))

/-- The geometric Galois Frobenius of the geometric fiber commutes with the projection to
the model:

```
        g_X          p_X
    X ──────▶ X ──────▶ X₀   =   X ──────▶ X₀
                                      p_X
```

that is `g_X ≫ p_X = p_X`. -/
@[reassoc (attr := simp)]
theorem geometricGaloisFrobenius_hom_comp_geometricFiberProj :
    f.geometricGaloisFrobenius.hom ≫ f.geometricFiberProj = f.geometricFiberProj := by
  simp [geometricGaloisFrobenius, geometricFiberProj]

/-- The geometric Galois Frobenius of the geometric fiber is semilinear over `k̄`: the
square

```
        g_X
  X ---------> X
  |            |
a_X          a_X
  v            v
Spec k̄ --σ--> Spec k̄
```

commutes, that is `g_X ≫ a_X = a_X ≫ σ`. -/
@[reassoc (attr := simp)]
theorem geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure :
    f.geometricGaloisFrobenius.hom ≫ f.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure ≫ (specGeometricFrobenius k).hom := by
  simp [geometricGaloisFrobenius, geometricFiberToAlgebraicClosure]

/-- The Frobenius square

```
        g_X
  X ---------> X
  |            |
a_X          a_X
  v            v
Spec k̄ --σ--> Spec k̄
```

is Cartesian: the geometric Galois Frobenius of the geometric fiber is the base change of
the geometric Frobenius of `Spec k̄`. This is the square whose compact-support base change
isomorphism transports Weil structures through `Rf_!`. -/
theorem isPullback_geometricGaloisFrobenius :
    IsPullback f.geometricGaloisFrobenius.hom f.geometricFiberToAlgebraicClosure
      f.geometricFiberToAlgebraicClosure (specGeometricFrobenius k).hom :=
  have h : IsPullback (f.geometricGaloisFrobenius.hom ≫ f.geometricFiberProj)
      f.geometricFiberToAlgebraicClosure f
      ((specGeometricFrobenius k).hom ≫ (Scheme.specAlgebraicClosure k).hom) := by
    rw [f.geometricGaloisFrobenius_hom_comp_geometricFiberProj,
      specGeometricFrobenius_hom_comp_specAlgebraicClosure]
    exact IsPullback.of_hasPullback f (Scheme.specAlgebraicClosure k).hom
  h.of_right f.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure
    (IsPullback.of_hasPullback f (Scheme.specAlgebraicClosure k).hom)

variable {f} {Y₀ : Scheme.{u}} {g : Y₀ ⟶ Spec (.of k)}

/-- The base change to `k̄` of a morphism over `k` commutes with the geometric Galois
Frobenii:

```
        φ × 𝟙
    X ──────────▶ Y
    │             │
  g_X           g_Y
    ▼             ▼
    X ──────────▶ Y
        φ × 𝟙
```

that is `(φ × 𝟙) ≫ g_Y = g_X ≫ (φ × 𝟙)`. -/
@[reassoc]
theorem geometricFiberMap_comp_geometricGaloisFrobenius (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) :
    geometricFiberMap φ h ≫ g.geometricGaloisFrobenius.hom =
      f.geometricGaloisFrobenius.hom ≫ geometricFiberMap φ h := by
  apply pullback.hom_ext <;> simp [geometricFiberMap, geometricGaloisFrobenius]

/-- The base change `φ̄ = φ × 𝟙` of a morphism over `k` and the geometric Galois Frobenii form
a commutative square:

```
          Fr_X
     X ────────▶ X
     │           │
   φ̄ │           │ φ̄
     ▼           ▼
     Y ────────▶ Y
          Fr_Y
```
-/
theorem commSq_geometricGaloisFrobenius (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) :
    CommSq f.geometricGaloisFrobenius.hom (geometricFiberMap φ h) (geometricFiberMap φ h)
      g.geometricGaloisFrobenius.hom :=
  ⟨(geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm⟩

/-- The square

```
          Fr_X
     X ────────▶ X
     │           │
   φ̄ │           │ φ̄
     ▼           ▼
     Y ────────▶ Y
          Fr_Y
```

of the base change `φ̄ = φ × 𝟙` of a morphism over `k` and the geometric Galois Frobenii is
cartesian, its horizontal maps being isomorphisms. -/
theorem isPullback_geometricGaloisFrobenius_geometricFiberMap (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) :
    IsPullback f.geometricGaloisFrobenius.hom (geometricFiberMap φ h) (geometricFiberMap φ h)
      g.geometricGaloisFrobenius.hom :=
  .of_horiz_isIso (commSq_geometricGaloisFrobenius φ h)

end Scheme.Hom

end Frobenius

end AlgebraicGeometry

end
