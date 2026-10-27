/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChangeMap
import Sheaf.AlgebraicGeometry.CechResolution
import Sheaf.AlgebraicGeometry.BaseChangeMapCech

/-! # Semicontinuity and base change for the Picard framework

Source: the current blueprint, sec-picard-framework/sk-thm-picard-perfect,
node det-thm-picard-semicon (blueprint: det-thm-picard-semicon).

The integer-degree dimension is zero in negative degrees, and otherwise is the existing
`Scheme.Modules.hFiber`. Higher direct images use `schemeModuleHigherDirectImage`, so negative
degrees are retained. The canonical maps are the existing `Scheme.Modules.cechBaseChangeMap`:
they send `b ⊗ [z]` to `b • [p^*z]`, through `ShortComplex.homologyBaseChange` and the canonical
Čech tensor comparison. The second statement applies to every affine neighbourhood and every
finite affine cover of its inverse image, including an empty cover when the inverse image is
empty. The Čech resolution identifies source and target with higher direct image fibre and
fibre cohomology, respectively; no arbitrary comparison map is chosen.

## Main statements

* `Scheme.Modules.picard_semicontinuity`: upper semicontinuity and reduced-base local freeness.
* `Scheme.Modules.picard_cechBaseChange_bijective`: the locally Noetherian base-change clause.
-/

@[expose] public section

set_option autoImplicit false

universe u wX wT

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Semicontinuity and local freeness, in every integer degree.
Source: blueprint sec-picard-framework/sk-thm-picard-perfect/det-thm-picard-semicon.md
(blueprint: det-thm-picard-semicon).

Proof: apply `thm-pc-semicontinuity-base-change` to the proper finitely presented morphism
and the finitely presented module flat over its base. The bounded finite free local model
computes fibre cohomology; ranks of differentials are lower semicontinuous, so its cohomology
dimensions are upper semicontinuous. If the base is reduced and this dimension is locally
constant, the two adjacent differential ranks are locally constant. Vanishing of larger minors
on a reduced ring gives local split normal forms, making cohomology finite locally free and
hence flat. These are local ranks, with no global constancy assumption. In negative degrees
both the cohomology of a module and its higher direct image vanish, and the assertions are
those for the zero function and zero module. -/
theorem picard_semicontinuity {X T : Scheme.{u}} (f : X ⟶ T)
    [IsProper f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wT} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (q : ℤ) :
    UpperSemicontinuous (fun t : T ↦ if 0 ≤ q then F.hFiber f q.toNat t else 0) ∧
      (IsReduced T →
        IsLocallyConstant (fun t : T ↦ if 0 ≤ q then F.hFiber f q.toNat t else 0) →
        SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          ((schemeModuleHigherDirectImage f q).obj F) ∧
          IsFlatOver (X := T) ((schemeModuleHigherDirectImage f q).obj F) (𝟙 T)) := by
  sorry

/-- The canonical Čech base-change map at a point of any affine neighbourhood is an
isomorphism under the additional reduced, locally constant, locally Noetherian hypotheses.
Source: blueprint sec-picard-framework/sk-thm-picard-perfect/det-thm-picard-semicon.md
(blueprint: det-thm-picard-semicon).

Proof: over the affine neighbourhood, `lem-pc-cech-resolution` computes higher direct images
and fibre cohomology from the finite affine cover and its pullback. The existing
`cechBaseChangeMap` is homology base change followed by the Čech tensor comparison, sending
`b ⊗ [z]` to `b • [p^*z]`. By `lem-pc-base-change-map-cech` this is the canonical comparison,
independent of the chosen cover and neighbourhood. Local constancy implies equality on all
generizations of the point. The Grauert clause of `thm-pc-semicontinuity-base-change` therefore
gives bijectivity over the reduced Noetherian affine neighbourhood. Equivalently use the
finite projective model of the Čech complex, whose quasi-isomorphism survives base change,
and the split normal form over the reduced local ring at the point. For negative degrees
both homologies vanish, so the map is bijective. Empty inverse images and empty covers also
have zero Čech cohomology. -/
theorem picard_cechBaseChange_bijective {X T : Scheme.{u}} (f : X ⟶ T)
    [IsProper f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f)
    [IsReduced T] [IsLocallyNoetherian T] (q : ℤ)
    (hq : IsLocallyConstant (fun t : T ↦ if 0 ≤ q then F.hFiber f q.toNat t else 0))
    (V : T.affineOpens) (t : V.1.toScheme)
    [Algebra Γ(V.1.toScheme, ⊤) Γ(Spec (V.1.toScheme.residueField t), ⊤)]
    (hg : algebraMap Γ(V.1.toScheme, ⊤) Γ(Spec (V.1.toScheme.residueField t), ⊤) =
      (V.1.toScheme.fromSpecResidueField t).appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → (Limits.pullback f V.1.ι).Opens)
    (hU : ∀ i : ι, IsAffineOpen (U i)) (hcover : iSup U = ⊤) :
    Function.Bijective
      (cechBaseChangeMap
        (IsPullback.of_hasPullback (Limits.pullback.snd f V.1.ι)
          (V.1.toScheme.fromSpecResidueField t))
        ((Scheme.Modules.pullback (Limits.pullback.fst f V.1.ι)).obj F) hg U
        (isAffineOpen_iInf_of_isSeparated (Limits.pullback.snd f V.1.ι) U hU) q) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
