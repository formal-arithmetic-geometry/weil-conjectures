/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram
import Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible
import Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometry
import Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule
import Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition
import Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Constructible compact support for constant finite coefficients on affine smooth curves

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, specialized to
finite commutative coefficients and affine bases of finite type over the integers.
(blueprint: lem-weil-pbc-etale-constant-shriek-rel-dim-1)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Compact support of a finite constant module on an affine smooth relative curve over
an affine base of finite type over the integers has constructible cohomology in every degree,
for every compactification with quasi-compact open immersion.
Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`.
(blueprint: lem-weil-pbc-etale-constant-shriek-rel-dim-1)

Proof plan:

1. Fix a compactification c. The base S is Noetherian by the finite-type-over-Noetherian lemma. We
use Noetherian induction on its closed subsets, rather than induction on its numerical dimension:
prove the conclusion after base change to every reduced closed subscheme E of S, using the
conclusion for proper closed subsets of E. Such E is affine of finite type over Z: on rings it is
A/I. It is Noetherian by the same finite-type lemma. The smooth relative-dimension permanence
lemma gives a smooth relative-dimension-one morphism X_E to E; affineness follows directly by
tensoring its affine coordinate algebra with A/I, and separatedness is preserved by base change.
These morphisms are of finite presentation, since smoothness gives local finite presentation and
qcqs permanence gives quasi-compactness and quasi-separatedness. Base change and exact inverse
image identify the restriction of the original cohomology sheaves with those of this new compact-
support object, whose input is again constant by the constant-pullback lemma. The minimal-closed-
subset lemma licenses the induction, and the empty closed subset is the immediate base case.
Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-scheme-closed-subsets-
minimal, lem-sbc-smooth-relative-dimension-permanence, lem-pod-separated-finite-type-base-change,
lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-etale-compact-support-base-change-qcqs, prop-
weil-pbc-inverse-image-modules-exact, lemma-constructible-pullback-constant, def-sbc-smooth-
morphisms, lem-weil-pbc-reduced-induced-closed-subscheme.

2. For a nonempty induction base E, choose a generic point eta of an irreducible component. Apply
the good-curves diagram to X_E to E. All schemes in this diagram are Noetherian and qcqs: U is an
open of the Noetherian affine E, V is finite over U, T_i is finite etale over V, and the remaining
schemes are of finite type over these. By shrinking U to an affine neighbourhood of eta and base
changing the whole diagram, we may take U affine; all the displayed properties persist. Let a:X_V
to V. By compact-support base change, constant pullback, and exactness of inverse image, the
pullback to V of each cohomology sheaf on U is the cohomology of Ra_! constant M. Since V to U is
surjective, the surjective-pullback constructibility criterion reduces constructibility on U to
constructibility on V.
Uses: lem-weil-pbc-good-curves-generic-diagram, lem-weil-pbc-finite-type-over-noetherian, lem-
weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-etale-compact-support-base-change-
qcqs, lemma-constructible-pullback-constant, prop-weil-pbc-inverse-image-modules-exact, lem-weil-
pbc-etale-constructible-surjective-pullback.

3. Write Z=(X_V minus W)_red. Every nonempty fibre of X_V to V has dimension one; empty fibres are
allowed. The open W is dense in every fibre. Consequently the closed complement has dimension at
most zero in each fibre: a dimension-one component cannot be contained in the complement.
Explicitly, a chain of two distinct irreducible closed subsets in that complement would have its
larger member contained in an irreducible component of the fibre; if this containment were strict
it would give a chain of length two in the dimension-one fibre. The larger member must therefore
be a whole component, contrary to density of W. There are no such chains, so the complement has
dimension at most zero. By the finite-type dimension-zero lemma these fibres are finite discrete
spaces. Thus Z to V is quasi-finite by the definition (finite type and isolated fibre points). It
is separated and of finite presentation, since it is a closed subscheme of the Noetherian
separated finite-type X_V. The constant finite module sheaf on Z is constructible using the one-
stratum partition. The quasi-finite shriek lemma makes its compact-support cohomology
constructible. Apply the open-closed compact-support triangle to W in X_V. Its long exact sequence
gives the short exact sequence 0 to coker(H^(q-1)(RZ_!) to H^q(RW_!)) to H^q(Ra_! constant M) to
ker(H^q(RZ_!) to H^(q+1)(RW_!)) to 0. The Serre theorem therefore reduces the assertion to compact
support on W.
Uses: lem-weil-pbc-good-curves-generic-diagram, lem-weil-pbc-finite-type-dim-zero-artinian, pqf-
def-quasifinite, lem-weil-pbc-finite-type-noetherian-finite-presentation, lem-weil-pbc-reduced-
induced-closed-subscheme, def-weil-pbc-etale-constructible-sheaf, lem-weil-pbc-etale-quasifinite-
shriek-constructible, lem-weil-pbc-etale-compact-support-open-closed-triangle, thm-constructible-
serre, lemma-constructible-pullback-constant.

4. Put i:nu inverse W to W. This is a closed immersion with empty open complement, since it is a
thickening. Apply the cited open-closed compact-support triangle to W to V with this closed
complement and K=constant M: its first term is compact support on the empty scheme, hence zero, so
its middle-to-last map identifies R(W to V)_! constant M with R(nu inverse W to V)_! i inverse
constant M. Constant pullback identifies this last input with constant M. This three-line
consequence replaces a separate thickening-invariance lemma. Put Ybar=coproduct_i Ybar_i and
Zprime=(Ybar minus j(nu inverse W))_red. The inverse image of W is dense in each fibre of Y_i to
T_i; since Y_i is open in a smooth geometrically connected fibre of Ybar_i, it is dense in that
fibre as well (apply the smooth-connected generic-geometry lemma over the spectrum of its residue
field, an integral normal base whose generic point is its only point, to conclude the fibre is
integral; every nonempty open in an irreducible space is dense). In an integral fibre of dimension
at most one, a proper closed subset has dimension at most zero: a positive-dimensional irreducible
closed subset would have to be the whole fibre, by the chain definition of dimension. Hence each
closed complement in a Ybar_i fibre has dimension at most zero, and in dimension zero it is empty.
For v in V, the etale-fibre discrete-separable-points lemma identifies the fibre of each T_i to V
as a disjoint union of spectra of finite separable extensions of kappa(v). This union is finite:
T_i to V is finite, hence its fibre is affine and quasi-compact, and the singleton open cover of
this discrete fibre has a finite subcover. The fibre of Zprime is the corresponding finite
disjoint union of the zero-dimensional closed complements in the Ybar_i fibres. The dimension-zero
lemma makes this finite and discrete. Since Zprime is a closed subscheme of the Noetherian
separated finite-type Ybar, the finite-type-Noetherian-finite-presentation lemma gives finite
presentation on affine charts; the definition of quasi-finite then applies. Its constant finite
module sheaf is constructible by the one-stratum partition, so the quasi-finite shriek lemma gives
constructible cohomology for D=R(Zprime to V)_! constant M. Write A=R(nu inverse W to V)_!
constant M and B=R(Ybar to V)_! constant M. The open-closed triangle is A to B to D to A[1]. Its
long exact sequence gives 0 to coker(H^(q-1)(B) to H^(q-1)(D)) to H^q(A) to ker(H^q(B) to H^q(D))
to 0. Thus constructibility of B and D implies that of A by the Serre theorem, and it suffices to
prove constructibility of B.
Uses: lem-weil-pbc-good-curves-generic-diagram, lemma-constructible-pullback-constant, lem-sbc-
smooth-connected-generic-geometry, lem-weil-pbc-finite-type-noetherian-finite-presentation, lem-
weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-finite-type-dim-zero-artinian, pqf-def-
quasifinite, def-weil-pbc-etale-constructible-sheaf, lem-weil-pbc-etale-quasifinite-shriek-
constructible, lem-weil-pbc-etale-compact-support-open-closed-triangle, thm-constructible-serre,
lem-weil-pbc-etale-fibre-discrete-separable-points.

5. For each i let b_i:Ybar_i to T_i and t_i:T_i to V. Properness allows the compactification
(identity,b_i), so Rb_i,! is Rb_i,* (extension by zero for the identity is the identity, by its
definition). The proper-smooth-curves finite-module lemma gives constructible cohomology for
Rb_i,* constant M; it applies without an invertibility assumption on M, because Lambda and M are
finite. Since t_i is finite etale, the quasi-finite shriek constructibility lemma applies to this
bounded-below complex. Composition identifies Rt_i,! Rb_i,! with R(t_i b_i)_! and hence gives
constructible cohomology for every summand. To assemble the finite disjoint union, successively
use the relative Mayer-Vietoris triangle with U a union of previous components and V the next
component. Their intersection is empty, whose compact-support object is zero, so the triangle
gives the finite direct sum of the summands. The Serre theorem closes constructible sheaves under
finite sums (each binary sum is a split extension); the empty family gives zero. Independence of
compactification permits every comparison just made for the original chosen candidates.
Uses: lem-weil-pbc-etale-proper-smooth-curves-finite-module, lem-weil-pbc-etale-quasifinite-
shriek-constructible, lem-weil-pbc-etale-shriek-qcqs-composition, def-weil-pbc-projection-
compactification, def-weil-pbc-extension-by-zero, lem-weil-pbc-etale-shriek-relative-mayer-
vietoris, thm-constructible-serre, lem-weil-pbc-etale-shriek-compactification-independence.

6. Steps 2 to 5 prove constructibility on the nonempty open U of E for every degree. Let Eprime=(E
minus U)_red. It is a proper closed subset of E, so the induction hypothesis applies there. Base
change, constant pullback, and exactness of inverse image identify the restriction to Eprime of
each cohomology sheaf with the constructible sheaf given by induction. For each fixed degree, take
the finite constructible immersed stratification on U and the one on Eprime. Their composite
immersions into E give a finite constructible immersed stratification of E: subsets locally closed
in an open or closed subset are locally closed in E, and constructible subsets remain
constructible because these immersions are quasi-compact on the Noetherian scheme E. On each
resulting stratum the inverse image is the same finite locally constant sheaf as before. This
proves constructibility directly from its definition and completes Noetherian induction. This
yields constructibility on S_red. If S has nilpotents, apply compact-support base change to the
surjection S_red to S and use exact inverse image and constant pullback to identify the pullbacks
of the original cohomology sheaves with those just proved constructible. The surjective-pullback
criterion then gives constructibility on S itself; it requires only qcqs, not flatness or
etaleness of this reduction map. Finally use compactification independence to obtain the assertion
for every compactification c.
Uses: lem-weil-pbc-etale-compact-support-base-change-qcqs, lemma-constructible-pullback-constant,
prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-constructible-stratification-assembly,
def-weil-constructible-subset, def-weil-pbc-etale-constructible-sheaf, lem-weil-pbc-etale-shriek-
compactification-independence, lem-weil-pbc-etale-constructible-surjective-pullback.
-/
theorem constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A]
    {X : Scheme.{u}} (h : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated h] [IsAffineHom h] [SmoothOfRelativeDimension 1 h]
    (M : ModuleCat.{u + 1} Λ) [Finite M]
    (c : Compactification h) [QuasiCompact c.i] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  sorry

end AlgebraicGeometry.Etale
