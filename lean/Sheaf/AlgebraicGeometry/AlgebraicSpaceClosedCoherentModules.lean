/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Coherent direct images under closed immersions of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 0DK1, 06ED and 04ZK;
Spaces Cohomology, Tags 08AM, 07UH and 07UB
(blueprint: lem-sfb-space-closed-coherent-modules).

Noetherian means locally Noetherian on every étale scheme chart, quasi-compact on
points, and absolutely quasi-separated. The last property is tested on fibre products
of pairs of affine scheme maps to the space. On locally Noetherian spaces the existing
finite-presentation predicate is exactly coherence, including the chartwise formulation
in the node (07UB). Support uses actual nonzero geometric germs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A closed subspace of a Noetherian algebraic space is Noetherian, and its direct
image preserves coherent modules and carries their supports to their point images.
Source: Stacks Project, Tags 0DK1 (stalks, with the transposed subscripts corrected),
08AM and 07UH (coherence), 06ED and 04ZK (Noetherian inheritance), 07UB (coherence test)
(blueprint: lem-sfb-space-closed-coherent-modules).

Proof:
1. Choose an affine surjective étale atlas U → X (lem-sfb-qc-space-affine-etale-atlas).
   Its pullback V → Z is an atlas and V → U a scheme closed immersion
   (lem-trf-space-fibre-products-etale-covers). Closed immersions are locally finite
   type (lem-weil-pbc-immersion-base-change-lft), so V is locally Noetherian by
   pqf-lem-locnoeth-lft. For any chart W → Z, the cover W ×_Z V → W has locally
   Noetherian source, since its map to V is étale, hence locally finite type.
   Apply lem-trf-etale-local-noetherian-descent to obtain local Noetherianity of W.
2. Since U is affine, its closed subscheme V is affine, hence quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs. Its surjective atlas map makes |Z| quasi-compact
   (lem-a1-space-finite-affine-subatlas).
3. The relative diagonal of the closed immersion is a closed immersion and thus
   quasi-compact on scheme tests (lem-sfb-space-closed-subspace-proper). The absolute
   diagonal factors through this diagonal and the base change of the diagonal of X.
   Quasi-compactness persists under base change and composition, so Z is absolutely
   quasi-separated (lem-sfb-space-quasicompact-affine-tests and
   lem-sfb-space-qcqs-source-products).
4. The direct image of a quasi-coherent module is quasi-coherent by
   lem-sfb-space-closed-immersion-quasi-coherent-modules, with the structural scalar
   action built into moduleDirectImage.
5. On an étale chart T → X, the direct image restricts to that under the scheme
   closed immersion Z ×_X T → T (lem-trf-space-etale-module-pushforward-restriction).
   The Zariski/étale comparison commutes with that direct image
   (lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). The scheme theorem
   lem-weil-pbc-closed-immersion-coherent-equivalence gives coherence on T.
   Testing every chart, equivalently applying 07UB, gives coherence on X.
6. The same comparisons identify support on U with the support of the scheme
   direct image from V. By lem-sfb-space-etale-chart-support and the scheme support
   formula this is the image of the support on V. The surjectivity of points of
   fibre products (lem-a1-space-point-open-calculus) identifies it with the inverse
   image of |i|(Supp M). Surjectivity of U → X then proves the support equality.
   Equivalently 0DK1 identifies stalks on the image and they vanish off that image. -/
theorem closedImmersion_noetherian_coherent_support
    {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b))) :
    (∀ T : Z.EtaleSite, IsLocallyNoetherian (Z.etaleForget.obj T)) ∧
    CompactSpace (Point Z.obj.obj) ∧
    (∀ (U V : Over S) (a : yoneda.obj U ⟶ Z.obj.obj)
      (b : yoneda.obj V ⟶ Z.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b))) ∧
    ∀ M : Z.Modules, M.IsFinitePresentation →
      ((moduleDirectImage i).obj M).IsFinitePresentation ∧
      moduleSupport ((moduleDirectImage i).obj M) =
        mapPoint i.hom.hom '' moduleSupport M := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
