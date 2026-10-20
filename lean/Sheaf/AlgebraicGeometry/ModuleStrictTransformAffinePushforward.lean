/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackQCoh
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.Blowup.Principalization
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Span

/-!
# Strict transform commutes with affine pushforward

Source: Stacks Project, Divisors, Tag 080G, Lemma `lemma-strict-transform-affine`,
restricted to finite-type centres (blueprint: lem-trf-strict-transform-affine-pushforward).

The structure map of `Y` is `f`, and that of `X` is `g ≫ f`. The base change of `g`
is Mathlib's canonical `pullback.map`, with identities on the blowup and the base.
The quotient-map equation specifies the canonical comparison, not just its isomorphism class.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Affine pushforward commutes canonically with module strict transform for the retained
finite-type quasi-coherent centre `I`. The comparison is the unique isomorphism whose
composite with the pushed-forward quotient map is the quotient map on `Y` after the
canonical affine base-change identification.
Source: Stacks Project, Divisors, Tag 080G
(blueprint: lem-trf-strict-transform-affine-pushforward).

Proof:
1. The fibre-product square with `g` is cartesian. By affine-morphism permanence its base
   change is affine. `lem-weil-pbc-affine-pushforward-base-change` identifies `pY^*(g_*F)`
   with `gb_*(pX^*F)` and gives quasi-coherence of `g* F`. Tensor pullback preserves
   quasi-coherence by `lem-pc-ringed-space-tensor-pullback-qcoh`.
2. By `thm-nagata-blowup-principalizes-center` the extended centre is locally principal.
   Its complement after pullback is quasi-compact: refine to affine opens, take a finite
   subcover on each affine, and use that each principal complement is a localization
   spectrum and hence quasi-compact (`lem-weil-pbc-affine-opens-basis`,
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`, and
   `lem-weil-pbc-spec-localization-away-basic-open`). The open immersion is also
   quasi-separated (`def-weil-quasi-separated-morphism`). No regularity after pullback
   is asserted.
3. The support subsheaf `KX` is the kernel of the open-restriction unit. Its target is
   quasi-coherent by `pqf-lem-pushforward-qcoh`; the kernel and quotient are quasi-coherent
   by `lem-weil-pbc-quasi-coherent-module-kernel` and
   `lem-weil-pbc-quasi-coherent-module-cokernel-image`.
4. The exceptional support on `X` is the inverse image of that on `Y`. Sectionwise,
   vanishing off this support identifies `gb* KX` with `KY` under affine base change.
5. On each affine open of the modified `Y`, the preimage is affine. The affine-section
   cokernel formula (`lem-weil-pbc-quasi-coherent-module-cokernel-image`) shows that
   `gb* (pX* F / KX)` is the quotient of `gb* pX* F` by `gb* KX`. Affine opens form a basis.
6. Affine base change therefore induces the displayed quotient isomorphism, with the
   displayed equation. Its inverse is induced by the inverse base-change isomorphism.
   The quotient map is epic, so this equation determines the comparison uniquely. -/
theorem existsUnique_moduleStrictTransform_affinePushforward
    {X Y S : Scheme.{u}} (f : Y ⟶ S) (g : X ⟶ Y) [IsAffineHom g]
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃! e : (pushforward
        (pullback.map (g ≫ f) I.blowupMap f I.blowupMap g (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))).obj
          (moduleStrictTransform (g ≫ f) I F) ≅
        @moduleStrictTransform Y S f I _ ((pushforward g).obj F)
          (isQuasicoherent_pushforward_of_isAffineHom g F),
      moduleBaseChangeMap g
          (pullback.map (g ≫ f) I.blowupMap f I.blowupMap g (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))
          (pullback.fst f I.blowupMap) (pullback.fst (g ≫ f) I.blowupMap)
          (by simp [pullback.map]) F ≫
        (pushforward
          (pullback.map (g ≫ f) I.blowupMap f I.blowupMap g (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))).map
          (cokernel.π (kernel.ι (moduleStrictTransformRestriction (g ≫ f) I F))) ≫
        e.hom = cokernel.π
          (kernel.ι (moduleStrictTransformRestriction f I ((pushforward g).obj F))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
