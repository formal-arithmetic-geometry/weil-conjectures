/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.ConstructibleSheaf.RestrictScalars
public import WeilConjectures.ConstructibleSheaf.SubobjectNoetherian

/-!
# Constructible sheaves on curves

On a curve `X` over a field (`AlgebraicGeometry.IsCurve`), which is a noetherian scheme,
subsheaves and quotients of constructible sheaves of modules over a noetherian ring are
constructible (`AlgebraicGeometry.IsCurve.isConstructibleSheaf_of_shortExact`).

A sheaf of `Λ`-modules killed by an ideal `J` of finite index is constructible if and only if it
is constructible as a sheaf of `Λ ⧸ J`-modules
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_coextendScalars_iff`); for `Λ = ℤ` and `J = (n)`
this compares the constructibility of an abelian sheaf killed by `n` with that of the
corresponding sheaf of `ℤ ⧸ n`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] {J : Ideal Λ}

/-- **Constructibility of a sheaf killed by an ideal of finite index can be tested over the
quotient ring.** Let `J` be an ideal of `Λ` with `Λ ⧸ J` finite and `F` a sheaf of `Λ`-modules
on the small étale site of `X` killed by `J`. Then `F` carries the structure of a sheaf of
`Λ ⧸ J`-modules (its coextension of scalars, whose restriction of scalars is `F`,
`CategoryTheory.Sheaf.restrictScalarsCoextendScalarsIso`), and `F` is constructible as a sheaf of
`Λ`-modules if and only if it is constructible as a sheaf of `Λ ⧸ J`-modules, with the same
stratifications. For `Λ = ℤ` (abelian sheaves) and `J = (n)` this says that an abelian sheaf
killed by `n` is constructible if and only if it is constructible as a sheaf of
`ℤ ⧸ n`-modules. (blueprint: `lem-weil-pbc-constructible-torsion-modules-agree`) -/
theorem isConstructibleSheaf_coextendScalars_iff [Finite (Λ ⧸ J)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : ∀ r ∈ J, r • 𝟙 F = 0) :
    IsConstructibleSheaf ((Sheaf.coextendScalars X.smallEtaleTopology J).obj F) ↔
      IsConstructibleSheaf F := by
  rw [← isConstructibleSheaf_restrictScalars_iff J]
  exact ⟨fun _ ↦ IsConstructibleSheaf.of_iso (Sheaf.restrictScalarsCoextendScalarsIso F hF),
    fun _ ↦ IsConstructibleSheaf.of_iso (Sheaf.restrictScalarsCoextendScalarsIso F hF).symm⟩

end Scheme

namespace IsCurve

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ] {k : Type u} [Field k]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]

include f in
/-- A curve over a field is a noetherian scheme. -/
lemma isNoetherian : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

include f in
/-- **Subsheaves and quotients of a constructible sheaf on a curve are constructible.** Let `X`
be a curve over a field `k` and `0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` a short exact sequence of étale sheaves of
modules over a noetherian ring `Λ` on `X`. If `F` is constructible, so are `F₁` and `F₂`: `X` is
noetherian, so the subsheaf `F₁` is constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono`), and `F₂` is the cokernel of a
morphism between constructible sheaves (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.cokernel`).
(blueprint: `lem-weil-pbc-curve-constructible-sub-quotient`) -/
theorem isConstructibleSheaf_of_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [Scheme.IsConstructibleSheaf S.X₂] :
    Scheme.IsConstructibleSheaf S.X₁ ∧ Scheme.IsConstructibleSheaf S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have := isNoetherian f
  have h₁ : Scheme.IsConstructibleSheaf S.X₁ := Scheme.IsConstructibleSheaf.of_mono S.f
  have := Scheme.IsConstructibleSheaf.cokernel S.f
  exact ⟨h₁, Scheme.IsConstructibleSheaf.of_iso (F := cokernel S.f)
    (hS.exact.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)).symm⟩

end IsCurve

end AlgebraicGeometry
