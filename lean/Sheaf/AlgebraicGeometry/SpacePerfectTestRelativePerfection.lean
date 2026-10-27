module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativePerfect
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses

import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
import WeilConjectures.RingTheory.RingPseudoCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpacePerfectWeakGenerator
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import Sheaf.Paper.StrictPerfectRingedPullbackModel
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.SpaceAffinePerfectHomBaseChange
import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarExtension

/-! # Perfect tensor tests detect relative perfection on algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 0GFL,
lemma-characterize-relatively-perfect; Tag 0GFK for local lower boundedness.
(blueprint: lem-sfb-space-perfect-test-relative-perfection).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Perfect scalar sections of every perfect tensor test imply relative perfection.
The affine target is presented by an isomorphism to Spec A. Finite presentation is
local finite presentation together with quasi-compactness; separatedness already
implies quasi-separatedness. The final covering-sieve clause expresses local lower
boundedness, with a bound allowed to vary on each covering member.

Source: Stacks Project, More on Morphisms of Spaces, Tags 0GFL and 0GFK
(blueprint: lem-sfb-space-perfect-test-relative-perfection).

Proof:
1. Each perfect A-valued test has a bounded finite-projective model. The finite-free
model lemma lem-pc-finite-projective-complex-free-model makes it pseudo-coherent
(def-pc-ring-pseudo-coherent-complex). Apply
lem-sfb-space-perfect-tests-pseudocoherence to obtain pseudo-coherence of K.
2. Finite presentation over the affine target makes X qcqs. Choose a perfect weak
generator G by lem-sfb-space-perfect-weak-generator. Its dual is perfect by
lem-sfb-ringed-site-perfect-duality. The hypothesis for its dual makes RΓ of its
tensor with K perfect, hence bounded below. Apply condition (iii) of
lem-sfb-space-generator-detects-lower-bound to deduce that K is bounded below.
3. For each prime p of A, let i:Y_p→X be the fibre projection. It is affine.
By lem-sfb-space-derived-qcoh-pullback-tensor the pullbacks of K and G are
quasi-coherent. By lem-sfb-space-derived-etale-chart-calculus and
lem-weil-pbc-strict-perfect-ringed-pullback-model, Li*G is perfect.
4. Derived adjunction identifies Hom(Li*G[n],F) with Hom(G[n],Ri*F). The generator
property and lem-sfb-space-affine-derived-pushforward-conservative imply F=0
when all these groups vanish. Thus Li*G is a perfect generator on the fibre.
5. By lem-sfb-space-affine-perfect-hom-base-change, RHom(Li*G,Li*K) is
RHom(G,K) tensor_A^L κ(p). Perfect duality identifies RHom(G,K) with the test
for G-dual. It is perfect, and remains perfect by
lem-sc-perfect-pullback-perfect-residue. Its negative cohomology eventually
vanishes. Condition (ii) of lem-sfb-space-generator-detects-lower-bound implies
that Li*K is bounded below, with no common bound required as p varies.
6. Apply lem-sfb-space-relative-perfect-fibre-criterion using pseudo-coherence,
flatness, local finite presentation, and both lower-boundedness assertions.
It gives locally finite Tor amplitude over the inverse-image base ring sheaf,
hence the stated relative perfection. Step 2 gives the last clause. -/
theorem isPerfectRelativeToScheme_of_perfect_tensor_tests
    {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (hsep : MapIsSeparated f) (hflat : MapIsFlat f)
    (hfp : MapIsLocallyOfFinitePresentation f) (hqc : MapIsQuasiCompact f.hom.hom)
    [HasDerivedCategory.{w} X.SmallModules] (K : X.DerivedQCoh)
    (htest : ∀ E : X.DerivedModules,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf E →
      DerivedCategory.IsPerfectRingComplex
        ((affineDerivedSections A Y e X f).obj
          (X.derivedDualityModel.closed.tensor.obj (E, K.obj)))) :
    IsPerfectRelativeToScheme Y f K.obj ∧
      ∀ V : X.SmallEtaleModel, ∃ T : Sieve V, T ∈ X.smallEtaleModelTopology V ∧
        ∀ (U : X.SmallEtaleModel) (g : U ⟶ V), T g →
          ∃ c : ℤ, ∀ n : ℤ, n < c →
            IsZero ((SheafOfModules.overFunctor.{u} X.smallStructureRings U).obj
              ((DerivedCategory.homologyFunctor X.SmallModules n).obj K.obj)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
