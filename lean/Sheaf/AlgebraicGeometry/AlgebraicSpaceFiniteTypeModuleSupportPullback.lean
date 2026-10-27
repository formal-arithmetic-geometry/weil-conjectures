/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Closed support and pullback of finite type modules on algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 07TZ, lemma-support-finite-type,
parts (1) and (3) (blueprint: lem-sfb-space-finite-type-support-pullback).

Support, finite type, quasi-coherence, tensor pullback, the point map and the atlas
topology are the existing constructions. Pullback is along an arbitrary space morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite type quasi-coherent module has closed support, and arbitrary tensor pullback
preserves finite type and quasi-coherence and takes support to its inverse image.
Source: Stacks Project, Morphisms of Spaces, Tag 07TZ, lemma-support-finite-type (1), (3)
(blueprint: lem-sfb-space-finite-type-support-pullback).

Proof:
1. On any etale scheme chart e : U to X, restrict the local presentations and finite
   generators. The Zariski/etale equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence gives a Zariski module N_U.
   The finite-type equivalence of lem-sfb-scheme-etale-module-exact-finiteness-comparison
   makes N_U finite type, without a Noetherian assumption.
2. Its support is closed by lem-weil-pbc-support-pullback-finite-type (1). By
   lem-sfb-space-etale-chart-support this is the inverse image of moduleSupport M.
   The final topology of def-a1-space-point-topology therefore makes that support closed.
3. For g : Y to X choose a surjective etale atlas U to X. Form Z = Y times_X U by
   lem-trf-space-fibre-products-etale-covers and choose an etale scheme atlas V to Z.
   The composite p : V to Y is surjective etale by
   lem-trf-space-representable-etale-scheme-tests. The other projection gives a : V to U
   with gp = ea. The scheme map a is arbitrary.
4. The tensor composition and etale restriction identifications of
   lem-trf-space-chart-adjunction-tensor-realization give p^*g^*M = a^*e^*M up to
   isomorphism. The Zariski/etale pullback comparison identifies this with (a^*N_U)_et.
   On local tensors the comparison multiplies the two scalar coefficients; this uses
   right exactness, with no assertion that arbitrary pullback preserves kernels.
5. By lem-weil-pbc-module-pullback-quasi-coherent and
   lem-weil-pbc-support-pullback-finite-type (3), a^*N_U is quasi-coherent and finite type.
   The finite-type comparison transfers these properties to its etale module. Descent
   of local presentations and finite generating families along p gives them for g^*M:
   pull p back to every scheme chart and refine by the etale scheme covers supplied by
   lem-trf-space-representable-etale-scheme-tests.
6. By lem-sfb-space-etale-chart-support and the scheme support pullback equality,
   p^{-1}Supp(g^*M) = Supp(a^*N_U) = a^{-1}Supp(N_U)
   = a^{-1}e^{-1}Supp(M) = p^{-1}g^{-1}Supp(M).
   Surjectivity of p on point classes proves the required equality. Empty spaces and
   the zero module give empty supports in the same calculation. -/
theorem finiteType_moduleSupport_pullback {S : Scheme.{u}} {X : AlgebraicSpace S}
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    IsClosed (moduleSupport M) ∧
      ∀ (Y : AlgebraicSpace S) (g : Y ⟶ X),
        ((moduleTensorPullback g).obj M).IsFiniteType ∧
        ((moduleTensorPullback g).obj M).IsQuasicoherent ∧
        moduleSupport ((moduleTensorPullback g).obj M) =
          mapPoint g.hom.hom ⁻¹' moduleSupport M := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
