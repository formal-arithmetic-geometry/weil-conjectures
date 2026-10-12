/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionBase
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechSectionsBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.QuasiIsoSections
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexOfMatrix
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.FreeAwayBaseChange

/-!
# Comparison of a free model of the Čech complex with the higher direct images

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` affine, a finite affine cover `U` of `X` and a quasi-coherent `𝒪_X`-module `ℱ`.
Let `R` be an `A`-algebra with a ring map `τ : R ⟶ Γ(T, ⊤)` over `A`, `P` a complex of free
`R`-modules of finite rank (with chosen bases) and `Φ : P ⟶ R ⊗[A] Č(U, ℱ)` a morphism which is
a quasi-isomorphism after every base change `R ⟶ B`. Then the complex of free `𝒪_T`-modules with
the matrices of the differentials of `P` (mapped by `τ`) computes the higher direct images
`R^q f'_* g'^* ℱ` (`AlgebraicGeometry.Scheme.Modules.nonempty_homology_freeComplex_iso`).

The comparison morphism to the Čech resolution `f'_* Č(g'⁻¹ U, g'^* ℱ)` is given on the basis
vectors by the images of the basis of `P` under `Φ` and the base change of Čech cochains; over an
affine open `W` of `T` it is identified with `Γ(T, W) ⊗[R] Φ`, hence a quasi-isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  {R : Type u} [CommRing R] [Algebra Γ(S, ⊤) R]

/-- The sheafified Čech complex `f'_* Č(g'⁻¹ U, g'^* ℱ)` of the base change. -/
noncomputable abbrev mumfordCech : CochainComplex T.Modules ℕ :=
  ((pushforward f').mapHomologicalComplex _).obj
    (cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ))

section Sections

variable (W : T.Opens) [Algebra Γ(S, ⊤) Γ(T, W)] [Algebra R Γ(T, W)]
  [IsScalarTower Γ(S, ⊤) R Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

/-- The base change map `Γ(T, W) ⊗[R] (R ⊗[A] Č^k(U, ℱ)) ⟶ Γ(W, f'_* Č^k(g'⁻¹ U, g'^* ℱ))`. -/
noncomputable def mumfordSectionsMap (k : ℕ) :
    Γ(T, W) ⊗[R] (R ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) →+
      Γ((mumfordCech (f' := f') (g' := g') ℱ U).X k, W) :=
  ((sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)
      (f' ⁻¹ᵁ W)).inv.f k).hom.comp
    ((cechSectionsBaseChangeX H ℱ U W hg k).comp
      (AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) R Γ(T, W) Γ(T, W)
        (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))).toAddMonoidHom)

lemma mumfordSectionsMap_apply (k : ℕ) (x) :
    mumfordSectionsMap H ℱ U W hg k x =
      (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)).inv.f k
        (cechSectionsBaseChangeX H ℱ U W hg k
          (AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) R Γ(T, W) Γ(T, W) _ x)) :=
  rfl

/-- `mumfordSectionsMap` is bijective over an affine open. -/
lemma bijective_mumfordSectionsMap [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι] (hW : IsAffineOpen W)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (k : ℕ) :
    Function.Bijective (mumfordSectionsMap (R := R) H ℱ U W hg k) :=
  ((ConcreteCategory.bijective_of_isIso _).comp
    (bijective_cechSectionsBaseChangeX H ℱ U W hg hW hU k)).comp
      (AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) R Γ(T, W) Γ(T, W) _).bijective

end Sections

end AlgebraicGeometry.Scheme.Modules
