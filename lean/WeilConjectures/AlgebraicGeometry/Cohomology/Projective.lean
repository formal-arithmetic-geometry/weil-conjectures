/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Coherent cohomology of projective schemes

Let `A` be a noetherian ring. The cohomology of a coherent sheaf on a closed subscheme of
`ℙⁿ_A` consists of finite `A`-modules, and vanishes above `n`. In relative form, the higher
direct images of a coherent sheaf along a projective morphism `f : X ⟶ S` to a locally noetherian
scheme are coherent, and vanish above the dimension of the ambient projective space. For a
quasi-compact and quasi-separated morphism to a quasi-compact base, the higher direct images of
quasi-coherent sheaves vanish in degrees bounded uniformly in the sheaf and the base change.

A projective morphism `f : X ⟶ S` is presented through a closed immersion `i : X ⟶ ℙ(n; S)` over
`S`, as in the blueprint's definition of (H-)projective morphisms. The cohomology `ℱ.H q` of a
sheaf on a scheme `X` over `Spec A` is an `A`-module through the structure morphism; this is
`AlgebraicGeometry.Scheme.Modules.moduleHOfSpec`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_of_isPullback`: the uniform
  vanishing bound for a quasi-compact quasi-separated morphism over a quasi-compact base.
- `AlgebraicGeometry.ProjectiveSpace.finite_H`: the cohomology of a coherent sheaf on `ℙⁿ_A` is
  finite over `A`.
- `AlgebraicGeometry.Scheme.Modules.finite_H_of_isClosedImmersion` and
  `subsingleton_H_of_isClosedImmersion`: the same for a closed subscheme of `ℙⁿ_A`, together with
  the vanishing above `n`.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_of_isClosedImmersion`
  and `isZero_higherDirectImage_of_isClosedImmersion`: coherence and vanishing of the higher
  direct images along a projective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X T : Scheme.{u}}

/-- **Uniform vanishing of the higher direct images.** Let `f : X ⟶ T` be quasi-compact and
quasi-separated, with `T` quasi-compact. There is an integer `n` such that `R^p f'_* ℱ' = 0` for
all `p ≥ n`, all base changes `f' : X' ⟶ T'` of `f` along morphisms `g : T' ⟶ T`, and all
quasi-coherent `𝒪_{X'}`-modules `ℱ'`.

Over an affine open of `T`, cover `X` by `t` affine opens with affine pairwise intersections
refined as necessary; induction on `t` with the Mayer–Vietoris sequence for `U₁` and
`U₂ ∪ ⋯ ∪ U_t` gives `n = t`, and the base change of the covering is again such a covering
of `X'` [Stacks, Tag 01XJ]. Quasi-coherence of the `R^p f_* ℱ`, the first part of the blueprint
lemma, is `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`.

(blueprint: `lem-pc-finite-support-hi`) -/
theorem exists_isZero_higherDirectImage_of_isPullback [CompactSpace T] (f : X ⟶ T)
    [QuasiCompact f] [QuasiSeparated f] :
    ∃ n : ℕ, ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
      [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g →
      ∀ (ℱ' : X'.Modules) [SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) ℱ'],
      ∀ p ≥ n, IsZero ((higherDirectImage f' p).obj ℱ') :=
  sorry

/-- The cohomology of a sheaf of modules on a scheme `X` with a morphism `f : X ⟶ Spec A` is an
`A`-module, by restriction of scalars of the `Γ(X, ⊤)`-module structure along
`A ≅ Γ(Spec A, ⊤) ⟶ Γ(X, ⊤)`.

This is not an instance, since `f` cannot be inferred. -/
abbrev moduleHOfSpec {A : Type u} [CommRing A] (f : X ⟶ Spec (.of A)) (M : X.Modules) (q : ℕ) :
    Module A (M.H q) :=
  Module.compHom (M.H q) ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

end Scheme.Modules

open Scheme.Modules

variable {n : Type u} [Finite n]

/-- **Coherent cohomology of projective space over a noetherian ring.** Let `A` be noetherian
and `ℱ` a coherent module on `ℙⁿ_A`. Then each `H^q(ℙⁿ_A, ℱ)` is a finite `A`-module.

By descending induction on `q`, for all coherent modules at once: for `q > n` the cohomology
vanishes; in general, a surjection `ℰ ⟶ ℱ` from a finite sum `ℰ` of twists `𝒪(m)` with coherent
kernel `𝒦` gives an exact sequence `H^q(ℰ) ⟶ H^q(ℱ) ⟶ H^{q+1}(𝒦)` whose outer terms are finite.

(blueprint: `lem-pc-projective-space-coherent-finiteness`) -/
theorem ProjectiveSpace.finite_H (A : Type u) [CommRing A] [IsNoetherianRing A]
    (ℱ : (ℙ(n; Spec (.of A))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := (ℙ(n; Spec (.of A))).ringCatSheaf) ℱ] (q : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ℱ q
    Module.Finite A (ℱ.H q) :=
  sorry

variable {X : Scheme.{u}}

/-- **Coherent cohomology of a projective scheme over a noetherian ring.** Let `A` be
noetherian, `i : X ⟶ ℙⁿ_A` a closed immersion and `ℱ` a coherent `𝒪_X`-module. Then each
`H^q(X, ℱ)` is a finite `A`-module: `i_* ℱ` is coherent with the same cohomology as `ℱ`, and
`AlgebraicGeometry.ProjectiveSpace.finite_H` applies to it.

(blueprint: `lem-pc-projective-coherent-finiteness`) -/
theorem Scheme.Modules.finite_H_of_isClosedImmersion (A : Type u) [CommRing A]
    [IsNoetherianRing A] (i : X ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    letI := moduleHOfSpec (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ℱ q
    Module.Finite A (ℱ.H q) :=
  sorry

/-- **Vanishing of the cohomology of a projective scheme above the dimension.** Let
`i : X ⟶ ℙᵈ_A` be a closed immersion, `ℙᵈ_A = ℙ(n; Spec A)` with `Nat.card n = d + 1`, and
`ℱ` a quasi-coherent `𝒪_X`-module. Then `H^q(X, ℱ) = 0` for `q > d`: the cohomology of `ℱ` is
that of `i_* ℱ`, computed by the Čech complex of the `d + 1` standard affine opens.

This is the vanishing clause of the blueprint lemma.

(blueprint: `lem-pc-projective-coherent-finiteness`) -/
theorem Scheme.Modules.subsingleton_H_of_isClosedImmersion (A : Type u) [CommRing A]
    (i : X ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {d : ℕ} (hn : Nat.card n = d + 1)
    {q : ℕ} (hq : d < q) : Subsingleton (ℱ.H q) :=
  sorry

namespace Scheme.Modules

variable {S : Scheme.{u}} (f : X ⟶ S) (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i]
  (hi : i ≫ ℙ(n; S) ↘ S = f) [HasInjectiveResolutions X.Modules] (ℱ : X.Modules)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hi in
/-- **Coherence of the higher direct images of a projective morphism.** Let `S` be locally
noetherian, `f : X ⟶ S` projective, i.e. `f = π ∘ i` for a closed immersion `i : X ⟶ ℙⁿ_S`,
and `ℱ` a coherent `𝒪_X`-module. Then every `R^q f_* ℱ` is coherent.

A projective morphism is proper, so this is a case of
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`. (The blueprint proves
it directly, as the input of the proper case: over an affine open `Spec A` of `S`, the Čech
complex of a finite affine cover of `f⁻¹(Spec A)` localises, so `R^q f_* ℱ` is the sheaf
associated with the finite `A`-module `H^q(f⁻¹(Spec A), ℱ)`.)

(blueprint: `lem-pc-projective-coherent-higher-images`) -/
theorem isFinitePresentation_higherDirectImage_of_isClosedImmersion [IsLocallyNoetherian S]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation := by
  subst hi
  have : LocallyOfFinitePresentation (i ≫ ℙ(n; S) ↘ S) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  exact isFinitePresentation_higherDirectImage _ ℱ q

include hi in
/-- **Vanishing of the higher direct images of a projective morphism.** In the situation of
`isFinitePresentation_higherDirectImage_of_isClosedImmersion`, with `Nat.card n = d + 1`, the
higher direct images `R^q f_* ℱ` vanish for `q > d`: over an affine open `Spec A` of `S`, they
are the sheaves associated with the `H^q(f⁻¹(Spec A), ℱ)`, which vanish by
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_isClosedImmersion`.

(blueprint: `lem-pc-projective-coherent-higher-images`) -/
theorem isZero_higherDirectImage_of_isClosedImmersion {d : ℕ} (hn : Nat.card n = d + 1)
    {q : ℕ} (hq : d < q) : IsZero ((higherDirectImage f q).obj ℱ) :=
  sorry

end Scheme.Modules

end AlgebraicGeometry
