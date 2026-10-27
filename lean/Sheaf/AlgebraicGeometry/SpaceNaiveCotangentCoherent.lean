module

public import Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.AffineTopTensorSections

/-! # Coherent cohomology of the naive cotangent complex

Source: Stacks Project, More on Morphisms of Spaces, Tags 0D0Y and 0D0Z;
Morphisms of Spaces, Tag 04ZK; Quot, Tag 0D1K
(blueprint: lem-sfb-space-naive-cotangent-coherent).

On a locally Noetherian algebraic space, coherent modules are exactly finitely
presented modules on the small etale ringed site (Stacks 07UB). On a Noetherian
affine etale chart these are precisely the sheaves associated to finite modules,
with sections B tensor_R N on affine etale R-algebras B. We use the existing
finite-presentation predicate, the existing small ringed model, and its derived
category at arbitrary localization size. The last conjunct spells out membership
of both specified objects in the full subcategory with bounded coherent cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finitely presented morphism over a locally Noetherian space has
locally Noetherian source, coherent structure sheaf, and coherent naive cotangent
cohomology supported in degrees -1 and 0. Both the naive cotangent object and the
structure sheaf in degree zero have bounded coherent cohomology.

Source: Stacks Project, Tags 0D0Y, 0D0Z, 04ZK and 0D1K; coherence criterion 07UB
(blueprint: lem-sfb-space-naive-cotangent-coherent).

Proof:
1. Choose a locally Noetherian scheme atlas V of Y and an atlas U0 of X. Their
   fibre product over Y is a scheme by the representable diagonal, and is a
   surjective etale atlas U of X. The chart map U to V is locally of finite
   presentation, hence locally of finite type. Apply pqf-lem-locnoeth-lft to
   conclude that U is locally Noetherian.
2. Use lem-sfb-space-naive-cotangent-finite-local-model and refine its charts by U
   and by Noetherian affine opens. Etale maps are locally of finite type, so the
   refined charts remain locally Noetherian. Exact slice restriction, from
   lem-pur-site-restriction-module-adjunction-exact, commutes with cohomology and
   quasi-isomorphisms. The local complex has two quasi-coherent finite-type terms
   and cohomology ker d and coker d in degrees -1 and 0.
3. Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
   lem-sfb-scheme-etale-module-exact-finiteness-comparison to pass to Zariski
   quasi-coherent finite-type modules. The affine finite-type criterion and
   tilde/Gamma adjunction identify the terms and differential with finite modules
   and a linear map. Tilde preserves kernels by lem-sc-tilde-preserves-finite-limits
   and cokernels by its adjunction; the etale comparison is exact.
4. Over a Noetherian ring the kernel of a map from a finite module is finite by
   lem-trf-noetherian-submodule-finitely-presented. The cokernel is finite because
   the target is finite. Thus the two local cohomology sheaves are coherent.
5. Local presentations glue on the etale site. On any Noetherian affine chart,
   the quasi-coherent module comes from its finite section module, and
   lem-sc-affine-top-tensor-sections gives B tensor_R N on every affine etale
   subchart. This is exactly the stated coherence criterion, equivalently finite
   presentation on this ringed site. Outside -1 and 0 the two-term complex has
   zero cohomology, also after derived localization.
6. The structure sheaf is associated to the cyclic module R on every such chart.
   It is therefore coherent. Its single complex has only degree-zero cohomology;
   together with step 5 this gives bounded coherent cohomology of both objects. -/
theorem naiveCotangent_coherent_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules]
    (hY : ∃ V : Y.EtaleSite,
      IsSurjective V.obj.hom ∧ IsLocallyNoetherian (Y.etaleForget.obj V))
    (hf : MapIsLocallyOfFinitePresentation f) :
    (∃ U : X.EtaleSite,
      IsSurjective U.obj.hom ∧ IsLocallyNoetherian (X.etaleForget.obj U)) ∧
    (SheafOfModules.unit X.smallStructureRings).IsFinitePresentation ∧
    (∀ n : ℤ,
      ((DerivedCategory.homologyFunctor X.SmallModules n).obj
        (naiveCotangent f)).IsFinitePresentation) ∧
    (∀ n : ℤ, n ≠ -1 → n ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules n).obj (naiveCotangent f))) ∧
    (∀ K : X.DerivedModules, K = naiveCotangent f ∨ K = X.derivedStructure →
      (∀ n : ℤ,
        ((DerivedCategory.homologyFunctor X.SmallModules n).obj K).IsFinitePresentation) ∧
      ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
        IsZero ((DerivedCategory.homologyFunctor X.SmallModules n).obj K)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
