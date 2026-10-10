/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Cokernels of quasi-coherent modules

Let `X` be a scheme. The cokernel of a morphism of quasi-coherent `𝒪_X`-modules is
quasi-coherent, and on a locally Noetherian scheme the cokernel of a morphism into a module of
finite presentation is of finite presentation.

On `Spec R` a quasi-coherent module is `M^~` for its global sections `M`, and `M ↦ M^~` preserves
cokernels, so the cokernel of `M^~ ⟶ N^~` is the quasi-coherent module `(N / M)^~`. The general
case reduces to affine opens, restriction along an open immersion preserving cokernels.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`: the cokernel of a morphism of
  quasi-coherent modules is quasi-coherent.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_cokernel`: on a locally Noetherian
  scheme, the cokernel of a morphism from a quasi-coherent module to a module of finite
  presentation is of finite presentation.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- On `Spec R`, the cokernel of a morphism `φ : M ⟶ N` of quasi-coherent modules is
`Γ(coker Γ(φ))^~`. -/
noncomputable def tildeCokernelIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (tilde.functor R).obj (cokernel (moduleSpecΓFunctor.map φ)) ≅ cokernel φ :=
  haveI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  haveI : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map φ) ≪≫
    cokernel.mapIso _ φ (asIso M.fromTildeΓ) (asIso N.fromTildeΓ)
      ((fromTildeΓNatTrans (R := R)).naturality φ)

/-- On `Spec R`, the cokernel of a morphism of quasi-coherent modules is quasi-coherent. -/
theorem isQuasicoherent_cokernel_of_spec {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) : (cokernel φ).IsQuasicoherent := by
  have : ((tilde.functor R).obj (cokernel (moduleSpecΓFunctor.map φ))).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (tildeCokernelIso φ) this

/-- **The cokernel of a morphism of quasi-coherent modules is quasi-coherent.** On an affine
open `U`, restriction along `Spec Γ(X, U) ⟶ X` commutes with cokernels, and on `Spec Γ(X, U)`
the cokernel of a morphism of quasi-coherent modules is quasi-coherent
(`isQuasicoherent_cokernel_of_spec`). -/
theorem isQuasicoherent_cokernel {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (cokernel φ) := by
  refine isQuasicoherent_of_iSup_opensRange_eq_top (cokernel φ)
    (fun U : {U : X.Opens // IsAffineOpen U} ↦ U.2.fromSpec) iSup_opensRange_fromSpec_eq_top
    fun U ↦ ?_
  have := isQuasicoherent_cokernel_of_spec ((restrictFunctor U.2.fromSpec).map φ)
  have : IsIso (cokernel ((restrictFunctor U.2.fromSpec).map φ)).fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent _
  let e := PreservesCokernel.iso (restrictFunctor U.2.fromSpec) φ
  have : IsIso (C := SheafOfModules.{u} (Spec Γ(X, U.1)).ringCatSheaf) e.inv :=
    (inferInstance : IsIso e.inv)
  exact (presentationOfIsIsoFromTildeΓ _).ofIsIso e.inv

/-- On the spectrum of a Noetherian ring, the cokernel of a morphism from a quasi-coherent module
to a module of finite presentation has a finite presentation: its global sections are generated
by the images of finitely many generators of the target. -/
theorem exists_presentation_isFinite_cokernel_of_spec {R : CommRingCat.{u}} [IsNoetherianRing R]
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFinitePresentation]
    (φ : M ⟶ N) : ∃ P : (cokernel φ).Presentation, P.IsFinite := by
  have := isQuasicoherent_cokernel_of_spec φ
  have := finite_sections_of_isFinitePresentation N (isAffineOpen_top (Spec R))
  have := finite_sections_top_of_finite N
  obtain ⟨P, _⟩ := exists_presentation_isFinite N
  have : IsIso (cokernel φ).fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent _
  have := finite_sections_top_of_isIso_fromTildeΓ (cokernel φ)
    (P.generators.ofEpi (cokernel.π φ))
  exact exists_presentation_isFinite (cokernel φ)

/-- **Cokernels of modules of finite presentation on a locally Noetherian scheme.** Let `X` be
locally Noetherian and `φ : M ⟶ N` a morphism from a quasi-coherent module to a module of finite
presentation. Then `cokernel φ` is of finite presentation: on every affine open this is
`exists_presentation_isFinite_cokernel_of_spec`. -/
theorem isFinitePresentation_cokernel [IsLocallyNoetherian X] {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (cokernel φ) := by
  have hex (U : {U : X.Opens // IsAffineOpen U}) :
      ∃ P : ((cokernel φ).restrict U.2.fromSpec).Presentation, P.IsFinite := by
    have := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
    obtain ⟨P, hP⟩ :=
      exists_presentation_isFinite_cokernel_of_spec ((restrictFunctor U.2.fromSpec).map φ)
    let e := PreservesCokernel.iso (restrictFunctor U.2.fromSpec) φ
    have : IsIso (C := SheafOfModules.{u} (Spec Γ(X, U.1)).ringCatSheaf) e.inv :=
      (inferInstance : IsIso e.inv)
    exact ⟨P.ofIsIso e.inv, inferInstance⟩
  choose P hP using hex
  exact isFinitePresentation_of_iSup_opensRange_eq_top (cokernel φ) _
    iSup_opensRange_fromSpec_eq_top P

end AlgebraicGeometry.Scheme.Modules
