/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.Paper.CanonicalPointScalarComparison
public import Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData
public import Sheaf.AlgebraicGeometry.FieldActionTransportData
public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.Paper.CoefficientHeartFiltration
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedOpenClosedRecollement
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Algebra.Basic
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.Paper.CoefficientHeartGeneration
import Sheaf.Paper.ContinuousQbarConstructibleGenerators
import Sheaf.Paper.ContinuousAlgClConstructibleTor
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.ContinuousAlgClProperFiniteness
import Sheaf.Paper.ConstructibleNormedGeometricFibres
import Sheaf.Paper.CondensedCoefficientIsoConstructible
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.NumberTheory.Padics.CountableClosedFiniteCover
import Sheaf.Analysis.NormedSpace.CountableUltrametricBasis
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.LinearAlgebra.CountableEndomorphismModuleReconstruction
import Sheaf.Paper.RingedProjectionFirstShift
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Paper.RationalOpenDirectImageConstructible
import Sheaf.Paper.TameBoundaryScalarComparison
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.Compactification.Dense
import Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Norm coefficient projection on supported rationalized lattices

Source: main-20261015 blueprint, six-functors direct-images proof paragraph (3),
agent-formulated ordinary norm-topology generator comparison.
(blueprint: lem-sfb-supported-lattice-norm-projection).

All coefficient rings use all continuous functions. The algebraic closure is
not completed. The map is the canonical counit-adjoint point projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
open CondensedGalois FieldActionTransport

/-- The integral condensed coefficient ring, with its subspace topology and
canonical pointwise ring structure.
Source: direct-images proof (3), O(P) = C(P,O_E)
(blueprint: lem-sfb-supported-lattice-norm-projection). -/
def supportedLatticeIntegralRing (ℓ : ℕ) [Fact ℓ.Prime]
    {Ω : Type u} [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E] :
    Coefficients.{u} where
  X := Profinite.continuousMapRingObjOfUniverse (Padic.coefficientExtensionIntegers ℓ E)
  mon := Profinite.continuousMapRingObjOfUniverseMonObj _
  comm := Profinite.isCommMonObj_continuousMapRingObjOfUniverse _

/-- Postcomposition by the valuation-subring inclusion O_E to E, using every
continuous function and the actual internal ring-object structures.
Source: direct-images proof (3), rationalization map O to A
(blueprint: lem-sfb-supported-lattice-norm-projection). -/
def supportedLatticeRationalization (ℓ : ℕ) [Fact ℓ.Prime]
    {Ω : Type u} [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E] :
    supportedLatticeIntegralRing ℓ E ⟶ normCoefficients E :=
  letI := Profinite.isMonHom_continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val
  CommMon.homMk ⟨Profinite.continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val⟩

/-- The coefficient map A to B is postcomposition by the embedded E to Omega.
Source: direct-images proof (3), inclusion A(P) to B(P)
(blueprint: lem-sfb-supported-lattice-norm-projection). -/
def supportedLatticeNormInclusion (ℓ : ℕ) [Fact ℓ.Prime]
    {Ω : Type u} [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) : normCoefficients E ⟶ normCoefficients Ω :=
  letI := Profinite.isMonHom_continuousMapRingObjMapOfUniverse
    (algebraMap E Ω) continuous_subtype_val
  CommMon.homMk ⟨Profinite.continuousMapRingObjMapOfUniverse
    (algebraMap E Ω) continuous_subtype_val⟩

/-- The actual Q = A_T tensor_{O_T} a_! L_0, placed in degree zero.
Extension by zero is the recorded open extension into the scheme-theoretic closure
followed by closed direct image. Rationalization here is ordinary scalar extension.
Source: direct-images proof (3), displayed definition of Q
(blueprint: lem-sfb-supported-lattice-norm-projection). -/
def supportedRationalizedLattice (ℓ : ℕ) [Fact ℓ.Prime]
    {Ω : Type u} [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    {K : Type u} [Field K] (T : Over (Spec (.of K)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    {S : Scheme.{u}} (a : S ⟶ T.left) (ha : IsImmersion a)
    (L₀ : Modules (supportedLatticeIntegralRing ℓ E).toMon S) :
    DerivedCategory.{u + 2} (Modules (normCoefficients E).toMon T.left) :=
  letI : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  letI : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  letI : IsNoetherian T.left := ⟨⟩
  (DerivedCategory.singleFunctor _ 0).obj
    ((extend (supportedLatticeRationalization ℓ E) T.left).obj
      ((coefficientHeartLocallyClosedExtension (supportedLatticeIntegralRing ℓ E).X a ha).obj L₀))

/-- The specified coefficient-projection map is invertible on every supported
rationalized integral lisse lattice, including the empty schemes and zero lattice.
Source: main-20261015 direct-images proof paragraph (3), explicit agent generator
obligation; an exact ordinary all-continuous incomplete-coefficient literature proof
is WANTED, and this is not attributed to HRS Lemma 7.9.
(blueprint: lem-sfb-supported-lattice-norm-projection).

Proof plan:

1. All schemes in the argument are separated of finite type over the given field, hence Noetherian
by [lem-weil-pbc-finite-type-over-noetherian]. By [det-prop-sfb-qlbar-colimit-x-invert-ell],
$A_Y=O_Y[1/\ell]$ is flat over $O_Y$. Put $L=A_S\otimes_{O_S}L_0$. Locally where $L_0=O_S^r$, this
is $A_S^r$ in degree zero, including $r=0$. The open and closed tensor projection isomorphisms
[lem-sfb-condensed-support-projection-formula] identify the actual $Q$ with $a_!L[0]$, not just
their restrictions to $S$. The unit-normalized inverse-image/tensor maps are those of
[lem-sfb-kflat-scalar-comparison-normalization]. Thus
[lem-sfb-coefficient-heart-lisse-extension-constructible] makes $Q$ bounded constructible over
$A_T$.

2. For every scheme $Z$ in this setting write $T_Z=B_Z\otimes^L_{A_Z}-$ and denote the
counit-adjoint coefficient projection for $h:X\to Y$ by $\beta_{h,K}$. Scalar extension takes
every bounded constructible $A_Z$-complex to a bounded constructible $B_Z$-complex. Indeed
[det-cor-coefficient-heart-ii-generation] gives a finite cone-and-shift construction from $c_!N$
with $N$ finite-rank lisse over $A$. On a trivializing cover $T_SN=B_S^r[0]$; no flatness of $A\to
B$ is used. The support tensor isomorphisms identify $T_Zc_!N$ with $c_!T_SN$. These are
generators of the triangulated category in [lem-sfb-continuous-qbar-constructible-generators], so
the finite construction remains bounded constructible. By
[det-sf-comp-continuous-algcl-constructible-tor] it has finite Tor amplitude. The same
finite-local-model reasoning applies to $T_Y$ of any bounded constructible output over $A$.

3. First establish $\beta_{h,K}$ for an arbitrary proper $h:X\to Y$ in the setting and bounded
constructible $A_X$-complex $K$. By [det-thm-sfb-proper-base-change-rational](2), $Rh_{*,A}K$ is
bounded constructible. By step 2 and [det-sf-comp-continuous-algcl-finiteness], every cohomology
sheaf of $Rh_{*,B}T_XK$ has finite constant local models on a constructible stratification. Only
this cohomological constructibility is needed here, not a uniform upper bound. For every geometric
$y$, [lem-sfb-constructible-normed-geometric-fibres] therefore makes the degree-$q$ fibre of this
target a finite-dimensional $\Omega$-vector space, for each $q$. Its source has bounded
constructible cohomology by step 2. The recorded finiteness theorem's representative
$\operatorname{PadicAlgCl}(\ell)$ can be replaced by $\Omega$: choose the algebraic-closure
isomorphism of [lem-pc-algebraic-closure-exists-unique]. It is isometric on each finite
subextension by [lem-weil-l-adic-extension-absolute-value], hence on the algebraic union. It
induces isomorphic continuous-function rings; [lem-sfb-condensed-coefficient-iso-constructible]
preserves the finite-Tor constructible input, and the induced exact module equivalences identify
the underlying direct images and their cohomology.

4. The inclusion $A\to B$ need not be flat. Nevertheless scalar restriction commutes with these
derived direct images: the two functors $\operatorname{Res}_Y Rh_{*,B}$ and
$Rh_{*,A}\operatorname{Res}_X$ are right adjoints of the canonically isomorphic left functors
$h_B^*T_Y$ and $T_Xh_A^*$. The scalar adjunction is
[lem-pur-sheaf-ring-derived-coefficient-adjunction] and the left-functor comparison is
[lem-sfb-kflat-scalar-comparison-normalization]. Their Hom adjunctions give a natural bijection
for every test object and hence the unique comparison isomorphism, preserving the adjunction
units. Consequently the transpose defining $\beta$ is the direct image of the insertion
$K\to\operatorname{Res}T_XK$, with insertion $k\mapsto1\otimes k$ on a flat-term K-flat
representative. This argument does not invoke the flat-only underived-restriction lemmas.

5. By [lem-sfb-algcl-countable-closed-finite-cover], $\Omega$ has at most countable algebraic
dimension over $E$. Apply [lem-sfb-countable-normed-orthogonal-basis] to $V=\Omega$ with
prescribed $b_0=1$. Write $D=\operatorname{End}^{\mathrm{cts}}_E(\Omega)$, $\lambda_0$ for its
first coordinate and $e(v)=\lambda_0(v)1$. Each $d\in D$ induces an $A$-linear endomorphism of $B$
by postcomposition on every profinite test, and hence of $B_X$ and $T_XK$ after forgetting
$B$-linearity. These maps preserve composition and addition. Also $eB$ is the actual copy of $A$;
its inclusion and retraction are induced by $E\hookrightarrow\Omega$ and $\lambda_0$, with
composite the identity. Tensoring, derived direct image and the exact fibre functor preserve this
split summand. The underlying derived tensor and the scalar adjunction use the same flat-term
representative [lem-sfb-internal-section-scalar-adjunction].

6. Fix $y,q$ and put $H=H^q\Phi_{y,A}(Rh_{*,A}\operatorname{Res}T_XK)$. Step 4 and the
fibre/restriction compatibility identify it with the underlying $E$-space of
$H^q\Phi_{y,B}(Rh_{*,B}T_XK)$. It is a unital $D$-module by step 5. Its $E$-dimension is at most
countable: by step 3 it is finite-dimensional over $\Omega$, which is countable-dimensional over
$E$. The split idempotent identifies $eH$ with $H^q\Phi_{y,A}(Rh_{*,A}K)$. Apply
[lem-sfb-countable-endomorphism-module-reconstruction]. Its isomorphism is $v\otimes
h\mapsto\theta_vh$, where $\theta_v(w)=\lambda_0(w)v$. Since $b_0=1$, $\theta_v=m_v e$, with $m_v$
multiplication by $v\in\Omega$. It follows that this is exactly $v\otimes h\mapsto
v\,H^q\Phi_y(Rh_*(\eta_K))(h)$.

7. The derived scalar/fibre comparison in [lem-sfb-constructible-normed-geometric-fibres]
identifies the degree-$q$ geometric fibre of the source of $\beta$ with $\Omega\otimes_E
H^q\Phi_{y,A}(Rh_{*,A}K)$: scalar tensor over the abstract field $E$ is exact. By the
insertion-of-one normalization in step 4 its map to the target is precisely the isomorphism in
step 6. Thus all cohomology-fibre maps are invertible. Conservativity on bounded constructible
complexes applies after truncating the target to any finite interval containing the source's
cohomology: its cohomology in every other degree has all fibres zero, so is zero by the
degree-zero constructible detection assertion of [lem-sfb-constructible-normed-geometric-fibres].
Both objects are therefore bounded constructible, and the same assertion proves $\beta_{h,K}$
invertible. This proves the proper comparison without a base-change assertion for $B$.

8. For a quasi-compact open $j:U\hookrightarrow X$, consider bounded constructible $C$ over $A_U$
for which $\beta_{j,C}$ is invertible. The two functors defining $\beta$ are exact and its
transformation commutes with shifts by [lem-sfb-ringed-projection-first-shift];
[lem-sf-triangle-two-out-of-three] makes this class closed under cones and shifts. It is also
closed under finite sums and retracts. Explicitly, if $C\xrightarrow{i}H\xrightarrow{r}C$ has
$ri=1$ and $\beta_H$ is invertible, then $F(r)\beta_H^{-1}G(i)$ is the inverse of $\beta_C$ by the
two naturality squares, where $F=T_XRj_{*,A}$ and $G=Rj_{*,B}T_U$.

9. Use [lem-sfb-tame-pair-proper-generators] for this $j$. A generator is $G=Rq_{*,A}K$, with
$p:Y\to X$ proper, $V=p^{-1}U$, $q:V\to U$ proper, $j':V\hookrightarrow Y$, and $K=b_!L[0]$ for
the stated tame normal-crossings pair. Here $K$ is bounded constructible by
[lem-sfb-coefficient-heart-lisse-extension-constructible]. The complex $Rj'_{*,A}K$ is bounded
constructible by [lem-sfb-rational-open-direct-image-constructible], so the proper comparisons
proved in steps 3--7 apply both to $(p,Rj'_{*,A}K)$ and $(q,K)$. The normal-crossings boundary
comparison [lem-sfb-continuous-algcl-tame-boundary-comparison] applies to the actual $K$,
including its inner extension by zero, and gives invertibility of $\beta_{j',K}$.

10. The equality $jq=pj'$ gives $Rj_*Rq_*\cong Rp_*Rj'_*$ in each coefficient category by
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. Along this equality, the coefficient
projection for the composite equals the two successive projections, by the counit-compatible
composition of [lem-sfb-ringed-derived-monoidal-comparisons] and [lem-weil-pbc-mate-pasting]. The
$p,j'$ route is invertible by step 9. In the $j,q$ route the $q$ projection is invertible, so
cancellation proves $\beta_{j,G}$ invertible for this generator. All comparisons use the canonical
inverse-image/tensor maps, so this is the specified transformation of step 8. Finite thick
generation and step 8 now give invertibility of $\beta_{j,C}$ for every bounded constructible
$A_U$-complex $C$.

11. Apply [sk-thm-nagata-compactification] to $t:T\to\operatorname{Spec}K$. Obtain
$T\xrightarrow{j}\overline T\xrightarrow{p}\operatorname{Spec}K$ with $j$ a quasi-compact open and
$p$ proper, all still separated of finite type over $K$. For the $Q$ of step 1, $Rj_{*,A}Q$ is
bounded constructible by [lem-sfb-rational-open-direct-image-constructible]. Step 10 gives the $j$
comparison and steps 3--7 give the $p$ comparison on that object. Derived composition and the same
counit-pasting equations identify their invertible composite with $\beta_{t,Q}$.

12. For the separably closed $K$, [lem-sfb-field-action-derived-section-transport] has trivial
Galois group. Its exact equivalence identifies the module derived category over
$\operatorname{Spec}K$ with the condensed coefficient module category, and $Rt_*$ with $Rp_{T*}$;
it preserves scalar extension, units, counits and their coefficient projections. Consequently step
11 is precisely the stated $\pi_Q$, including the K-flat formula $q\mapsto1\otimes q$. For empty
$T$ or $S$, or $L_0=0$, $Q=0$ and both functors give zero; all comparisons above are their unique
isomorphism on zero. No step used an arithmetic action, completion, a finite-subextension-valued
replacement of $B$, or flatness of $A\to B$.
-/
theorem supportedLatticeNormProjection_isIso
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (K : Type u) [Field K] [IsSepClosed K] [CharP K p]
    (Ω : Type u) [NormedField Ω]
    [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (T : Over (Spec (.of K))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    {S : Scheme.{u}} (a : S ⟶ T.left) (ha : IsImmersion a)
    (_hconstructible : Topology.IsConstructible (Set.range a))
    (L₀ : Modules (supportedLatticeIntegralRing ℓ E).toMon S)
    (_hL₀ : IsLisseCoefficientModule (supportedLatticeIntegralRing ℓ E).X L₀) :
    IsIso (pointProjection (supportedLatticeNormInclusion ℓ E) T.left
      (canonicalPointScalar (supportedLatticeNormInclusion ℓ E) T.left)
      (supportedRationalizedLattice ℓ E T a ha L₀)) := by
  sorry

end AlgebraicGeometry.ProEtale
