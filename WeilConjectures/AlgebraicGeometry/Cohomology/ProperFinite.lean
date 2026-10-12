/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.ChowLemma
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.Comparison
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.Leray
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.Nilpotent
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.RelativeProjective
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.TwistSection

/-!
# Finiteness of the cohomology of a proper scheme over a noetherian ring

Let `A` be a noetherian ring and `p : X ⟶ Spec A` proper. For every coherent `𝒪_X`-module `ℱ`,
the cohomology groups `H^q(X, ℱ)` are finite `A`-modules
(`AlgebraicGeometry.Scheme.Modules.finiteH_of_isProper`) [Stacks, Tag 02O5], [EGA III₁, 3.2.1].
Consequently, for `f : X ⟶ T` proper over an affine `T` with noetherian `Γ(T, ⊤)`, the sections
of the higher direct images are finite
(`AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`).

The proof is a noetherian induction on the closed subsets of `X` containing the image of a
closed subscheme `Y` carrying the module. By Chow's lemma there is `π : Y' ⟶ Y` proper, with
`Y'` closed in `ℙ(N; Spec A)`, which is an isomorphism over a dense open `U`. For `n ≫ 0` the
higher direct images of `G = π^* 𝒢 ⊗ 𝒪(n)` along `π` vanish, so `π_* G` has the cohomology of
`G`, finite by the projective case. A section of `𝒪(n)` not vanishing at a point over `U` gives
`𝒢 ⟶ π_* G`, an isomorphism near that point; its kernel and cokernel are supported on a smaller
closed subset, so are handled by induction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- **Finiteness of the cohomology of a proper scheme over a noetherian ring.** For `A`
noetherian, `p : X ⟶ Spec A` proper and `ℱ` a coherent `𝒪_X`-module, every `H^q(X, ℱ)` is a
finite `A`-module.

(blueprint: `lem-pc-coherent-hi`) -/
theorem finiteH_of_isProper {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) [IsProper p] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] : FiniteH p ℱ :=
  sorry

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section Coherence

variable [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

/-- **Finiteness of the cohomology of a proper morphism over a Noetherian affine base.** With
`f : X ⟶ T` proper, `T` affine with Noetherian ring of global sections `Γ(T, ⊤)` and `ℱ` a coherent
`𝒪_X`-module, the global sections `Γ(T, R^q f_* ℱ) = H^q(X, ℱ)` of the higher direct image form a
finite `Γ(T, ⊤)`-module for every `q` [Stacks, Tag 02O6], [EGA III₁, 3.2.1].

This is the affine clause of the blueprint lemma `lem-pc-coherent-hi`; it is deduced from
`AlgebraicGeometry.Scheme.Modules.finiteH_of_isProper` (Chow's lemma and the projective case,
Stacks 02O5/02O6). It is the only input to
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage` beyond the formal
properties of the higher direct images.

(blueprint: `lem-pc-coherent-hi`) -/
theorem finite_sections_higherDirectImage [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj ℱ, ⊤) :=
  sorry

end Coherence

end AlgebraicGeometry.Scheme.Modules
