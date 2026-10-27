/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.ProfiniteFiniteConstantLocalModel
public import Sheaf.Paper.ContinuousIntegralCoefficientData
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.QcqsLisseStratifiedIntegralLattices
import Sheaf.Paper.QcqsConstructibleIntegralLatticeTree
import Sheaf.Paper.ContinuousLocallyFreePullback
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.InternalExtensionInverseImage
import Sheaf.Paper.FiniteAffineProEtaleRefinement
import Sheaf.Paper.ContinuousFiniteFreeDenominators
import Sheaf.Paper.IntegralRationalizationExact
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.CategoryTheory.ScalarLocalizationModuleColimit
import Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Sheaf.CategoryTheory.CoefficientRestrictionSectionsAcyclic
import Sheaf.Paper.CondensedOpenClosedRecollement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Integral approximation of supported rational image section complexes

Source: Hemo--Richarz--Scholbach, Sections 6.3, 7.2 and 8; the eight-step
supported-image argument recorded in the DAG
(blueprint: lem-sfb-supported-rational-image-integral-approximation).

The conclusion is membership in the extension and isomorphism closure of localized
integral image section complexes, all over the original affine base and evaluated
on the same fixed test object U. The support
chains are paths in the existing finite open-closed trees. Every allowed chain over
an affine base extends to such a tree by adding complementary siblings as leaves.
The path may stop at any vertex, and its root path is the empty chain.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Ordinary inversion of ell on abelian section complexes, constructed as the total
right derived functor of tensoring with the flat abelian group `Z[1/ell]`.
This tensor is exact, so its total right derived functor is its termwise functor.
For a complex with the constant scalar action of B and E = B[1/ell], the underlying
abelian complex of `C tensor_B^L E` is canonically `C tensor_Z Z[1/ell]`.
Thus no choice of an action or of an integral lattice enters this construction.
Source: HRS Section 7.2, ordinary scalar localization; Stacks Tag 00HT
(blueprint: lem-sfb-supported-rational-image-integral-approximation). -/
def abelianPrimeLocalization (ℓ : ℕ) :
    DerivedCategory Ab.{u + 1} ⥤ DerivedCategory Ab.{u + 1} :=
  (MonoidalCategory.tensorRight
    (AddCommGrpCat.of (ULift.{u + 1} (Localization.Away (ℓ : ℤ))))).rightDerivedFunctor

/-- Apply the actual path functor, then coefficient pullback along the test object,
then ordinary module-derived sections of the actual abelian image in degree zero.
Source: HRS Lemma 5.3(1), and the supported-image argument, notation F and I_f
(blueprint: lem-sfb-supported-rational-image-integral-approximation). -/
def supportedImageSections
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X S : Scheme.{u}} {tree : QcqsOpenClosedTree X} (p : tree.Path S)
    (U : X.ProEt)
    {L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj R S)}
    (f : L ⟶ M) : DerivedCategory Ab.{u + 1} :=
  (condensedModuleSections R U.left).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.upperStar R U.hom).obj ((p.extension R).obj (image f))))

/-- The generators are localized integral image section complexes, with arbitrary
finite scalar local models, arbitrary actual module maps, and arbitrary support
paths over this same X, evaluated on the fixed test object U.
Source: HRS Sections 7.2 and 8, the supported-image argument's definition of R_X
(blueprint: lem-sfb-supported-rational-image-integral-approximation). -/
def supportedIntegralImageGenerator (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) (U : X.ProEt) :
    ObjectProperty (DerivedCategory Ab.{u + 1}) :=
  fun K ↦ ∃ (S : Scheme.{u}) (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff ℓ E) S)) (g : L ⟶ M),
      HasFiniteConstantLocalModel (CondensedRing.integralCoeff ℓ E) S L ∧
      HasFiniteConstantLocalModel (CondensedRing.integralCoeff ℓ E) S M ∧
      K = (abelianPrimeLocalization ℓ).obj
        (supportedImageSections (CondensedRing.integralCoeff ℓ E) p U g)

/-- The smallest isomorphism-closed, extension-closed class containing the integral
image generators for the fixed test object U. `IsTriangulatedClosed₂` only closes the
middle of a distinguished
triangle with both outer terms in the class; shifts or arbitrary cones are not required.
Together with isomorphism closure this is exactly distinguished-triangle extension closure.
Source: HRS Sections 7.2 and 8, supported-image argument's definition of R_X
(blueprint: lem-sfb-supported-rational-image-integral-approximation). -/
def supportedIntegralImageExtensionClosure (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) (U : X.ProEt) :
    ObjectProperty (DerivedCategory Ab.{u + 1}) :=
  fun K ↦ ∀ P : ObjectProperty (DerivedCategory Ab.{u + 1}),
    P.IsClosedUnderIsomorphisms → P.IsTriangulatedClosed₂ →
    (∀ C, supportedIntegralImageGenerator ℓ E X U C → P C) → P K

/-- Supported rational image section complexes belong to the extension closure
of ordinary scalar localizations of integral image section complexes over the same X
and on the same fixed affine pro-etale test object U.

Source: HRS Theorem 7.7, Corollary 6.13, Lemma 5.3(1) and the proof of Lemma 8.6;
the precise supported-image assertion is the following eight-step DAG assembly.
(blueprint: lem-sfb-supported-rational-image-integral-approximation).

Proof plan:
1. All schemes in the given support chain are qcqs. Indeed an affine scheme has a finite affine
cover with quasi-compact affine intersections; an open subscheme inherits the affine-intersection
criterion for quasi-separatedness, and a closed subscheme does also, by intersecting affine charts
with the closed subscheme. A quasi-compact open of a quasi-compact scheme is quasi-compact, and a
closed subscheme of a quasi-compact scheme is quasi-compact. Induct along the given finite chain.
A finite scalar model over the field $E$ is finite free: choose a basis of the finitely presented
$E$-vector space $P$ and tensor that basis with $E_T$. Thus $L,M$ are lisse, allowing varying
finite ranks. Write $I=\operatorname{im}f$.
Dependencies: lem-weil-pbc-quasi-separated-affine-cover-criterion, def-weil-closed-immersion,
sk-def-sfb-constructible.
2. Apply the qcqs stratified-lattice theorem in its finite-extension case to $L$ on $S$. Starting
with the one-vertex tree, apply the refinement clause of the constructible lattice-tree theorem to
its finite constructible lattice partition. This gives a finite open–closed tree on whose leaves
$L$ has integral lisse lattices. On each such leaf apply the same two results to $M$ and attach
the resulting finite trees. The previous $L$-lattices pull back to lisse lattices: coefficient
pullback is exact, preserves their inclusions, and commutes with scalar extension. We obtain one
finite tree $\mathscr T$ with root $S$ and, on every nonempty leaf $W$, embeddings $A_W\subset
L|_W$, $B_W\subset M|_W$ of lisse $B_W^{\mathrm{coeff}}=p_W^*B$-modules whose rationalizations are
$L|_W,M|_W$. (Here $B_W$ denotes the lattice in $M$, and $B_W^{\mathrm{coeff}}$ the ring.) Every
refinement uses the actual factoring scheme morphisms supplied by the tree theorem. All vertices
are qcqs and every new edge has precisely the support-chain form. Empty leaves receive zero
lattices.
Dependencies: lem-sfb-qcqs-lisse-stratified-integral-lattices,
lem-sfb-qcqs-constructible-integral-lattice-tree, lem-weil-pbc-continuous-locally-free-pullback,
sk-prop-sfb-cartesian-coefficients, lem-sfb-internal-extension-inverse-image.
3. Fix a nonempty leaf $W$. Take a common pro-étale trivializing cover of the two lattices, by
pulling back the two covers. The finite affine refinement lemma gives finitely many affine charts
$V_a\to W$ refining it. On each chart the chosen bases identify $f|_{V_a}$ with a map from the
rationalization of a standard finite free integral module to another. Apply the compact
finite-free denominator lemma on $V_a$: there are $n_a\geq0$ and an integral matrix map whose
rationalization is $\ell^{n_a}f|_{V_a}$. Put $N=\max_a n_a$ and multiply each numerator by
$\ell^{N-n_a}$. These maps agree on all overlaps, since their composites with the embedded target
lattice inclusion agree with the single map $\ell^Nf$, and that inclusion is monic. The sheaf
condition therefore glues them to an actual integral module map $g_W:A_W\to B_W$. Its
rationalization is $\ell^Nf|_W$. This proves the uniform numerator assertion without a Noetherian
hypothesis or a constant-matrix hypothesis on $f$.
Dependencies: lem-sfb-finite-affine-cover-refinement-general,
lem-weil-pbc-continuous-finite-free-denominators.
4. Put $H_W=\operatorname{im}g_W$ in the integral abelian module category. Exact coefficient
pullback identifies $I|_W$ with $\operatorname{im}(f|_W)$. Exact integral rationalization
identifies $H_W[1/\ell]$ with $\operatorname{im}(\ell^Nf|_W)$: apply the exact functor to the
kernel-cokernel definition of image. Multiplication by $\ell^N$ is an automorphism of the rational
target, and its image is the same submodule as the image of $f|_W$. Hence $I|_W\cong H_W[1/\ell]$.
The lattices are finite scalar local models, since locally they are finite free. For an empty leaf
use $g_W:0\to0$.
Dependencies: sk-prop-sfb-cartesian-coefficients, lem-sfb-integral-rationalization-exact.
5. For any support chain $\mathscr P$ from a leaf $W$ to the original $X$, let
$G_R=v^*J_R^{\mathscr P}$. These functors are exact: open and allowed closed edge functors are
exact by ringed open–closed recollement, and $v^*$ is exact by Cartesian coefficients. They
preserve the repeated-$\ell$ colimit: $v^*$ and $j_!$ are left adjoints, and closed $i_*$
preserves filtered colimits because every ambient vertex is qcqs. The underlying sheaf
constructions commute with forgetting the $E$-action to $B$: open extension by zero and direct
image have the same underlying abelian functors for both coefficients, and inverse image has the
Cartesian coefficient identification. The continuous coefficient inclusion is localization at
$\ell$ on compact profinite sets; its pullback remains this localization, since inverse image
preserves its colimit. The scalar-localization module-colimit theorem thus gives, with its
normalized legs, an isomorphism
$$\operatorname{Res}G_E(H_W[1/\ell])\cong
\varinjlim(G_BH_W\xrightarrow{\ell}G_BH_W\xrightarrow{\ell}\cdots).$$
The $n$th leg is the unit followed by multiplication by $\ell^{-n}$.
Dependencies: lem-weil-pbc-proetale-ringed-open-closed, sk-prop-sfb-cartesian-coefficients,
def-sfb-module-open-lower-shriek, def-sfb-module-lower-star,
def-weil-pbc-continuous-integral-coefficients, lem-weil-pbc-scalar-localization-module-colimit.
6. Set $C_W=R\Gamma(U,G_BH_W[0])$. The sheaf telescope in step 5 is a strict diagram with every
term concentrated in degree zero. Apply the derived-global-sections clause of qcqs pushforward
continuity on the affine scheme $U$, with common lower bound zero. Its normalized comparison
identifies the termwise colimit of bounded-below representatives of
$C_W\xrightarrow{\ell}C_W\to\cdots$ with $R\Gamma(U,\operatorname{Res}G_E(H_W[1/\ell])[0])$. The
complex-localization colimit theorem, also on the one-object site with scalar ring $B$, identifies
that colimit with $C_W[1/\ell]$; scalar localization is exact, so this is $C_W\otimes_B^L E$.
Restriction of scalars does not change the resulting abelian section complex, by
restriction-sections acyclicity. Consequently $$C_W[1/\ell]\cong
R\Gamma(U,G_E(I|_W)[0])\quad\text{in }D(\mathbf{Ab}).$$ This uses only uniformly bounded-below
diagrams, not a finite cohomological dimension bound.
Dependencies: lem-weil-pbc-condensed-qcqs-pushforward-continuity,
lem-weil-pbc-scalar-localization-complex-colimit, lem-weil-pbc-scalar-localization-sheaf-exact,
lem-coef-restriction-sections-acyclic.
7. At each vertex $T$ of $\mathscr T$ apply condensed open–closed recollement to $(I|_T)[0]$. It
gives the triangle with outer terms $j_!(I|_{T_{\rm open}})[0]$ and $i_*(I|_{T_{\rm closed}})[0]$.
Compose with the path edge functors from $T$ to $S$, the original $J_E$, and $v^*$. They are exact
by step 5, so their termwise derived functors preserve this triangle. Apply the triangulated
functor $R\Gamma(U,-)$. The resulting middle term is the section complex for the path ending at
$T$; its outer terms are the corresponding section complexes for the two children. For a leaf the
path is the original support chain with that tree branch appended, so step 6 places its section
complex in $\mathcal R_X$.
Dependencies: lem-weil-pbc-condensed-open-closed-recollement,
lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated.
8. Induct upwards on the finite tree. A leaf section complex is isomorphic to the rationalization
of the integral image section complex for $g_W$, on an allowed chain over the same original $X$,
and is therefore a generator of $\mathcal R_X$. At a binary vertex the two child terms lie in
$\mathcal R_X$ by induction, so its middle term lies there by extension closure. At the root this
middle term is $R\Gamma(U,F_{E,v}(I_f)[0])$, as required. The zero object is itself a generator,
using $0\to0$ on the empty support chain; thus empty schemes, empty leaves and zero maps cause no
exception. A one-vertex tree and the empty original support chain are included. No splitting of
any connecting map has been used.
-/
theorem supported_rational_image_integral_approximation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [IsAffine X]
    {S : Scheme.{u}} (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) S))
    (hL : HasFiniteConstantLocalModel (Profinite.continuousMapRingObj E) S L)
    (hM : HasFiniteConstantLocalModel (Profinite.continuousMapRingObj E) S M)
    (f : L ⟶ M) (U : X.ProEt) [IsAffine U.left] :
    supportedIntegralImageExtensionClosure ℓ E X U
      (supportedImageSections (Profinite.continuousMapRingObj E) p U f) := by
  sorry

end AlgebraicGeometry.ProEtale
