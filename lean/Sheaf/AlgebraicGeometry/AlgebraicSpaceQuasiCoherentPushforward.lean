/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule

import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpacePushforwardAtlasEqualizer
import Sheaf.AlgebraicGeometry.SmallEtaleQuasiCoherentKernel

/-!
# Quasi-coherence of algebraic-space direct images

Source: Stacks Project, Morphisms of Algebraic Spaces, Tag 03M9 (lemma-pushforward),
restricted to separated morphisms; Properties of Spaces, equation-push-pull before Tag 03LV
(blueprint: lem-trf-space-qc-separated-quasi-coherent-pushforward).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Direct image under a quasi-compact separated morphism preserves quasi-coherence.
The scalar action is the regular-function action in `moduleDirectImage`.
Source: Stacks Project, Morphisms of Algebraic Spaces, Tag 03M9; Properties of Spaces,
equation-push-pull (blueprint: lem-trf-space-qc-separated-quasi-coherent-pushforward).

Proof:
1. Test on affine étale schemes V over Y. Étale locality of quasi-compactness and
   separatedness (lem-trf-space-qc-separated-etale-local) gives these properties after
   base change. The canonical module restriction isomorphism
   (lem-trf-space-etale-module-pushforward-restriction) reduces the claim to affine Y.
   Affine étale tests cover the site, so their local presentations suffice.
2. Choose an affine surjective étale atlas U of X. Its overlap R = U ×_X U is a scheme
   by lem-trf-space-fibre-products-etale-covers. The atlas equalizer
   (lem-trf-space-pushforward-atlas-equalizer) realizes f_*F as the kernel of the
   difference a_*F_U → b_*F_R, for a : U → Y and b : R → Y.
3. The map R → U ×_Y U is a base change of the closed diagonal of f; closed immersions
   are stable under base change (lem-weil-pbc-closed-immersion-base-change). Thus R is
   affine. Both a and b are morphisms between affine schemes, hence quasi-compact and
   separated. Restricting the local presentations of F gives quasi-coherence on U and R.
4. The scheme Zariski/étale equivalence and direct-image comparison
   (lem-trf-scheme-zariski-etale-quasi-coherent-equivalence) make a_*F_U and b_*F_R
   quasi-coherent. Their kernel is quasi-coherent by
   lem-trf-scheme-etale-quasi-coherent-kernel. The atlas equalizer identifies it with
   f_*F. Applying the affine-test reduction proves the assertion on Y_et. -/
theorem isQuasicoherent_moduleDirectImage_of_quasiCompact_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hsep : IsSeparatedPresheafMap f.hom.hom)
    (F : X.Modules) [F.IsQuasicoherent] :
    ((moduleDirectImage f).obj F).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
