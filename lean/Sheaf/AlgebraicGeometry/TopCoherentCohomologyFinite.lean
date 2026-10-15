/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Paper.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.CohomologyFiniteExtension
import Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop
import WeilConjectures.AlgebraicGeometry.ChowLemma
import Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.RelativeSerreVanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison
import WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import Sheaf.AlgebraicGeometry.TopDegreeOpenRestrictionSurjective

/-! # Finite-dimensional top coherent cohomology

Source: Stacks Project, Étale Cohomology, Tag 0A3M, lemma-top-cohomology-coherent
(blueprint: lem-weil-pbc-top-coherent-cohomology-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The top coherent cohomology of a separated finite-type scheme over a field is
finite-dimensional over that field. The scalar action is restriction along the canonical
map `k → Γ(X, ⊤)` induced by the structure morphism.
Source: Stacks Project, Étale Cohomology, Tag 0A3M, lemma-top-cohomology-coherent
(blueprint: lem-weil-pbc-top-coherent-cohomology-finite).

Proof:
1. Induct strongly on `d`. Finite-type algebras over a field are Noetherian
(lem-weil-pbc-finite-type-algebra-noetherian). In dimension zero, the identity closed
immersion and lem-pc-zero-dimensional-closed-subscheme-finite make X finite over k.
By pqf-lem-coherent-ft-locnoeth and lem-weil-pbc-quasi-coherent-finite-type-affine,
global sections are finite over its finite k-algebra, hence finite over k.
2. The long exact sequence (pqf-def-cohomology) and
lem-pc-e2-cohomology-finite-extension preserve finiteness under extensions. Apply
lem-weil-pbc-coherent-filtration-integral-subschemes and
lem-pc-closed-immersion-coherent-cohomology to reduce to nonzero coherent ideals on
integral closed subschemes. Smaller-dimensional terms vanish by
lem-sc-noetherian-cohomology-above-dimension.
3. The same filtration proves finiteness of degree d-1 cohomology for coherent modules
supported in dimension at most d-1. Exact stalks (lem-weil-pbc-module-stalk-exact),
lem-weil-pbc-closed-pushforward-stalks and
lem-weil-pbc-finite-type-module-support-closed identify and bound quotient supports;
apply induction or above-dimension vanishing on each integral support, then extension
closure. This works for nonpure supports and the zero module.
4. For a nonzero ideal I on integral X, O_X/I is coherent by
lem-weil-pbc-coherent-kernel-cokernel-locnoeth. Its support misses the generic point;
lem-sc-hilbert-nowhere-dense-dimension-drop bounds it by d-1. Step 3 and the ideal
long exact sequence reduce finiteness for I to finiteness for O_X.
5. Use lem-weil-pbc-chow-noetherian and
lem-weil-pbc-integral-chow-relatively-ample to obtain a proper modification Y → X,
with Y integral and immersed in projective space, and a relatively ample L. The common
nonempty open has dimension d by lem-sc-integral-locally-algebraic-opens-dimension.
Choose n with all positive higher images of L^n zero by lem-pc-relative-kill-by-twisting.
6. The pushforward G of L^n is coherent (lem-pc-coherent-hi). A projective coordinate
nonzero generically gives a nonzero section of L^n, using the transition functions of
def-pc-projective-space-twist (take 1 when n=0). It induces an injection O_X → G,
isomorphic on a smaller nonempty open where the section is nonvanishing. Its coherent
cokernel Q has support of dimension at most d-1, by the coherence, closed-support and
dimension-drop lemmas above.
7. Step 3 makes H^(d-1)(Q) finite. The long exact sequence reduces to H^d(G), and
lem-pc-m1-leray-acyclic-pushforward-linear-comparison identifies this k-linearly with
H^d(Y,L^n), since all positive higher images vanish.
8. By lem-chow-closed-model embed Y as a dense open in its integral projective closure,
of dimension d by lem-sc-integral-locally-algebraic-opens-dimension. Projective twists
restrict to L^n by their coordinate transition functions. Apply
lem-weil-pbc-top-degree-open-restriction-surjective: H^d(Y,L^n) is a quotient of the
closure's twist cohomology, finite over k by lem-pc-projective-coherent-finiteness.
9. Return through steps 7 and 4 to every coherent ideal, then through the filtration
of step 2 to every coherent module. The zero module and empty scheme have zero cohomology.
This closes the strong induction. -/
theorem finiteDimensional_top_coherent_cohomology (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    FiniteDimensional k
      ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (X ↘ Spec (.of k)).appTop).hom).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace d).obj F)) := by
  sorry

end AlgebraicGeometry
