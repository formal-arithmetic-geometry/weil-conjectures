/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite

/-!
# Finiteness of the sections of the higher direct images

For a proper morphism `f : X ⟶ T` to an affine scheme with Noetherian ring of global sections and
a coherent sheaf `ℱ` on `X`, the global sections of the higher direct images `R^q f_* ℱ` are
finite `Γ(T, ⊤)`-modules (`AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`).
Their coherence is in `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section Coherence

variable [IsProper f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

/-- **Finiteness of the cohomology of a proper morphism over a Noetherian affine base.** With
`f : X ⟶ T` proper, `T` affine with Noetherian ring of global sections `Γ(T, ⊤)` and `ℱ` a coherent
`𝒪_X`-module, the global sections `Γ(T, R^q f_* ℱ) = H^q(X, ℱ)` of the higher direct image form a
finite `Γ(T, ⊤)`-module for every `q` [Stacks, Tag 02O6], [EGA III₁, 3.2.1].

This is the affine clause of the blueprint lemma `lem-pc-coherent-hi`. Since `T` is affine,
`Γ(T, R^q f_* ℱ) ≅ H^q(X, ℱ)`, and the finiteness of `H^q(X, ℱ)` is
`AlgebraicGeometry.Scheme.Modules.hasFiniteH_of_isProper` (Chow's lemma, the projective case
and noetherian induction, Stacks 02O6). It is the only input to
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage` beyond the formal
properties of the higher direct images.

(blueprint: `lem-pc-coherent-hi`) -/
theorem finite_sections_higherDirectImage [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj ℱ, ⊤) := by
  let p : X ⟶ Spec (.of Γ(T, ⊤)) := f ≫ T.isoSpec.hom
  have h := hasFiniteH_of_isProper p ℱ q
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  exact Module.Finite.of_bijective_semilinearMap e he
    ((Scheme.ΓSpecIso (.of Γ(T, ⊤))).inv ≫ T.isoSpec.hom.appTop).hom h

end Coherence

end AlgebraicGeometry.Scheme.Modules
