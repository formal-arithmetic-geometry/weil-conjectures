/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.RfPerfect

/-!
# Perfectness of the Čech complex of a proper flat family

Over an affine base `S = Spec A`, the derived direct image `Rf_* ℱ` of a module `ℱ` of finite
presentation, flat over `S`, along a proper morphism of finite presentation is represented by
the Čech complex `Č(U, ℱ)` of a finite affine cover, and it is a perfect object of `D(A)`
(`AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_of_isProper`).
-/

@[expose] public section

universe u

open CategoryTheory DerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)

/-- **The Čech complex of a proper flat family is perfect.** Let `f : X ⟶ S` be proper and of
finite presentation over an affine scheme `S = Spec A`, let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite presentation which is flat over `S`, and let `U` be a finite cover of `X`
by affine opens. Then the Čech complex `Č(U, ℱ)` is a perfect object of `D(A)`: it is
isomorphic in `D(A)` to a bounded complex of finitely generated projective `A`-modules.

Over the affine base, `Č(U, ℱ)` represents `Rf_* ℱ`
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechModuleComplex_linearEquiv`), it is a
bounded complex of flat modules up to quasi-isomorphism, and its formation commutes with every
affine base change
(`AlgebraicGeometry.Scheme.Modules.nonempty_Q_baseChange_iso_cechModuleComplex`). So this is
part (a) of `sk-thm-picard-coherence` over an affine base: `Rf_* ℱ` is perfect, represented by a
bounded complex of finite projective `A`-modules (finite free locally on `Spec A`) whose
formation commutes with base change. It is not a consequence of the non-canonical statement
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`, which does not
relate its finite free complexes to the Čech complex.

Over a noetherian ring this is proved in
`AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_of_isNoetherianRing` (modulo the
finiteness of the cohomology). In general it is [Stacks, Tag 0B91] (`Rf_* ℱ` is perfect, `ℱ` being
`S`-perfect as it is of finite presentation and flat over `S`), together with the description of
perfect objects of `D(𝒪_S)` on an affine scheme as perfect complexes of `A`-modules
[Stacks, Tag 08EB]; alternatively it follows from the noetherian case by noetherian
approximation of `(f, ℱ)` [EGA IV₃, §8 and §11.2], since the formation of the Čech complex of a
flat module commutes with base change.

(blueprint: `sk-thm-picard-coherence`) -/
theorem isPerfect_Q_cechModuleComplex_of_isProper [IsAffine S] [IsProper f]
    [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (hℱ : ℱ.IsFlatOver f)
    {ι : Type u} (U : ι → X.Opens) [Finite ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) :
    (Q.obj (cechModuleComplex f ℱ U)).IsPerfect :=
  sorry

end AlgebraicGeometry.Scheme.Modules
