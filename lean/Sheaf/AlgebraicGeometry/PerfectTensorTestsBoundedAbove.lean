module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import WeilConjectures.AlgebraicGeometry.AffineKoszulGeometricProperties
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import WeilConjectures.AlgebraicGeometry.DerivedOpenUnitRestrictionIso
import WeilConjectures.AlgebraicGeometry.OpenImmersionRestrictionDerivedProperties
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforward
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction
import WeilConjectures.AlgebraicGeometry.PerfectHomGap
import WeilConjectures.AlgebraicGeometry.PerfectSupportedMapLift
import WeilConjectures.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.AffineKoszulUpperLocalization
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison

/-! # Perfect tensor tests detect upper boundedness

Source: Stacks Project, Derived Categories of Schemes, Tag 0GEN,
`proposition-detecting-bounded-above`, implication (7)(b) to (1)
(blueprint: lem-sfb-perfect-tensor-tests-bounded-above).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wΓ

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- On a qcqs scheme, eventual vanishing of the cohomology of every perfect tensor's
unbounded derived global sections forces a quasi-coherent derived object to be bounded
above. Each perfect object has its own bound.

Source: Stacks Project, Tag 0GEN, `proposition-detecting-bounded-above`, (7)(b) to (1)
(blueprint: lem-sfb-perfect-tensor-tests-bounded-above).

Proof:
1. Duals of perfect objects are perfect. Perfect RHom duality, tensor symmetry, and the
shifted-global-Hom comparison identify the tensor tests for Q-dual with Hom(Q[-i],K).
Use lem-pc-perfect-rhom-tensor-comparison, lem-sc-derived-internal-hom-adjunction,
def-pc-global-derived-rhom and lem-sc-restricted-global-hom-shifted-equiv.
2. Apply qcqs-open induction (lem-sc-invert-s-cohomology-induction) to the resulting
all-perfect-Hom criterion. On an affine, test with O[0]. Internal Hom from O[0] is the
original complex by evaluation at 1 on an injective representative. The affine derived
equivalence and tilde-homology comparison reconstruct its cohomology from derived sections
(lem-pc-affine-qcoh-derived-equivalence, new-affine-derived-tilde-homology-comparison).
3. For T = U union V with U quasi-compact open and V affine, quasi-separatedness and a
finite affine cover make U intersect V quasi-compact. Choose finitely many principal opens
covering that intersection. Their Koszul complex C is perfect and supported on T minus U
(lem-weil-pbc-qcqs-finite-affine-open-cover,
lem-weil-pbc-quasi-separated-affine-cover-criterion,
lem-pc-affine-koszul-geometric-properties).
4. Extend C from V by the supported open-pushforward theorem; its direct image C' is
perfect and equals extension by zero. The extension adjunction converts the test for C'
into eventual Hom vanishing on V. Apply lem-sfb-affine-koszul-upper-localization to get
the canonical upper-truncation isomorphism with the pushforward from U intersect V
(lem-pc-supported-open-pushforward, lem-sc-derived-open-shriek-derived-adjunction).
5. Put F = Rj_*(E restricted to U). The actual adjunction unit E to F is an isomorphism
on U, and in high degrees on V by step 4 and open base change. It is therefore an
isomorphism on cohomology in degrees at least a. Its cone B is bounded above and has
quasi-coherent cohomology (lem-pc-derived-open-unit-restriction-iso,
lem-pc-restrict-derived-direct-image-open,
lem-pc-open-immersion-restriction-derived-properties,
lem-sf-derived-homology-long-exact, lem-weil-pbc-qcqs-morphism-permanence,
lem-pc-derived-direct-image-preserves-qcoh, lem-pc-supported-qcoh-triangulated).
6. For each perfect Q, the perfect-gap vanishing interval gives eventual vanishing of
Hom(Q[-i],B) and Hom(Q[-i],B[-1]). Exactness for E to F to B transfers the eventual
Hom tests from E to F (lem-sc-perfect-ext-bounded-qcoh-vanishing,
lem-weil-pbc-hom-into-triangle-exact).
7. Apply lem-sc-perfect-support-map-lift with full support and target zero: every perfect
P on U is a retract of the restriction of a perfect Q on T. Derived restriction agrees
with derived pullback along an open immersion. The derived adjunction transfers the tests
for F to E restricted to U, and retracts give all perfect tests on U. Induction bounds
E restricted to U above (lem-pc-ringed-spaces-derived-adjoint,
lem-weil-pbc-open-immersion-module-pullback-restriction,
lem-sc-derived-open-restriction-adjunction-exact, def-pc-derived-pullback).
8. The uniform direct-image truncation bound makes F bounded above. The high-degree
unit isomorphism from step 5 then bounds E above, completing the induction
(lem-pc-derived-direct-image-uniform-truncation-bound). No bound uniform in P is used. -/
theorem isBoundedAbove_of_perfect_tensor_tests
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{wΓ}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (hTests : ∀ P : schemeDerivedCategory X, Scheme.IsPerfect X P →
      ∃ bP : ℤ, ∀ i : ℤ, bP < i →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) i).obj
            ((schemeDerivedGlobalSections X).obj (P ⊗ K)))) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj K) := by
  sorry

end AlgebraicGeometry
