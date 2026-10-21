/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFiniteCohomologyComplexes
public import Sheaf.Paper.PointFgCompleteComplexes
public import Sheaf.Paper.PointFdComplexes
public import Sheaf.Paper.PointFdQbarCategory
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.PointProEtaleSectionsExact
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.Paper.PointSectionsFiniteness
import WeilConjectures.RingTheory.FiniteFreeResolution
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import Sheaf.Algebra.Homology.BaseChangeRHomPerfect
import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Sheaf.Paper.PointSectionsScalarExtension
import Mathlib.Algebra.Colimit.Module
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.CompletedScalarShift
import Sheaf.Paper.PointSectionsTensorShift
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Exact equivalences given by the four geometric-point fibre functors

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509;
main-20261015, sec-six-functors-basics/sk-def-sf-admissible, order 1868
(blueprint: lem-weil-point-fibre-equivalence).

For the three full-subcategory targets, shifts and distinguished triangles are
expressed after their fully faithful inclusions into the ambient derived categories.
This is precisely the inherited shift and distinguished-triangle convention.
The fourth target uses its recorded common-stage distinguished-triangle predicate.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Expose the existing inherited torsion-source triangulation, without choosing a
new structure. Source: blueprint order 1454, bounded constructible subcategory;
order 1509, torsion fibre (blueprint: lem-weil-point-fibre-equivalence). -/
noncomputable instance pointFibreTorsionSourceTriangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty.IsTriangulated (intrinsicFiniteTorsionConstructible l E n hn Y) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (proEtale_bounded_constructible_isTriangulated Y
    (Padic.coefficientExtensionRing l E n)).2

/-- Expose the existing strict fullness of the torsion source.
Source: blueprint order 1454, full triangulated subcategory; order 1509, torsion fibre
(blueprint: lem-weil-point-fibre-equivalence). -/
noncomputable instance pointFibreTorsionSourceIsoClosed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E n hn Y) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (proEtale_bounded_constructible_isTriangulated Y
    (Padic.coefficientExtensionRing l E n)).1

/-- Each of the four specified fibre functors is an equivalence, commutes with all
integer shifts and preserves distinguished triangles. The first three exactness
clauses use the inherited structures through the full-subcategory inclusions.
Source: blueprint order 1509; main-20261015 order 1868
(blueprint: lem-weil-point-fibre-equivalence).

Proof:
1. Write $A=\mathcal O_E$, $\pi=\varpi_E$, $A_n=A/\pi^n$ and $B=\widehat{\mathcal O}_{E,s}$. The
coefficient DVR theorem makes $A$ a domain with every ideal principal, hence Noetherian, and
with finite residue field. Choosing a finite set of residue representatives and successively
writing $x=r_0+\pi x_1$ shows that every element of $A_n$ is represented by
$\sum_{j=0}^{n-1}r_j\pi^j$; thus $A_n$ is finite and Noetherian. The continuous-coefficient
description, applied to the noetherian scheme $s$, identifies $\Gamma(s,B)$ canonically with
$C(\{*\},A)=A$, preserving constants and all quotient projections. The completed-constant
reduction theorem gives flatness of $B$ over $\underline A$ and $B\otimes^L_{\underline
A}\underline{A_n}\simeq\underline{A_n}$. Indeed the resolution $[A\xrightarrow{\pi^n}A]$ of
$A_n$ becomes $[B\xrightarrow{\pi^n}B]$. Constant-sheaf exactness and this flatness make its
negative cohomology zero. Exactness of sections therefore gives $\Gamma(s,\underline{A_n})=A_n$,
with the canonical map from constant values as the identification. No identification of $B$ with
the discrete constant sheaf $\underline A$ is made.
Uses: lem-weil-l-adic-extension-integers-dvr,
lem-weil-pbc-continuous-coefficients-immersion-restriction,
lem-weil-pbc-completed-constant-sheaf-reduction,
lem-weil-pbc-constant-module-section-properties, lem-weil-point-proetale-sections-exact.

2. For either $(R,\mathcal R)=(A_n,\underline{A_n})$ or $(A,B)$ define $L_{\mathcal
R}(M)=\mathcal R\otimes_{\underline R}\underline M$ for an $R$-module $M$. Here constant sheaves
and sheaf tensor products have exactly their existing definitions. There is an adjunction
$L_{\mathcal R}\dashv\Gamma(s,-)$: a sheaf map $u:L_{\mathcal R}M\to F$ gives $m\mapsto
u_s(1\otimes m)$; conversely $t:M\to F(s)$ gives, before sheafification, $b\otimes m\mapsto
b\,t(m)|_U$ on every object $U$, and then extends uniquely to the sheaf tensor product. These
constructions are inverse and natural; the balancing relation is precisely $R$-linearity of $t$.
Constant sheafification is exact by the arbitrary-site module-sheafification theorem. Thus
$L_{\underline{A_n}}$ is exact, and $L_B$ is exact by flatness in step 1. Both right adjoints
are exact by the point-sections theorem. For any finitely presented $R$-module $M$, a
presentation $R^a\to R^b\to M\to0$ and exactness give $\Gamma(s,L_{\mathcal
R}M)\cong\operatorname{coker}(R^a\to R^b)=M$. On free generators this is $m\mapsto1\otimes m$,
so the isomorphism is precisely the adjunction unit, not an arbitrary identification.
Uses: def-weil-pbc-constant-sheaf, def-pur-sheaf-tensor-product,
lem-weil-pbc-site-r-module-presheaf-sheafification-exact,
lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-point-proetale-sections-exact.

3. Apply the exact-functor derived factorization to the two exact adjoints in step 2. They act
termwise, commute with every shift and preserve distinguished triangles. Their termwise unit and
counit are chain maps; naturality makes them commute with differentials, and the two triangle
identities hold degree by degree. They descend through the localization, with the same
identities, to an adjunction on the unbounded derived categories. Exact-functor preservation of
homology identifies the cohomology of the unit $M\to\Gamma(s,L_{\mathcal R}M)$ with the
underived unit at $H^i(M)$. Consequently this derived unit is an isomorphism whenever all
$H^i(M)$ are finitely presented, by the cohomological isomorphism criterion. In particular it is
an isomorphism on $D^b_{\mathrm{fin}}(A_n)$ and on $D^b_{\mathrm{fg}}(A)$: finite modules over
the finite Noetherian ring $A_n$, and finitely generated modules over the Noetherian ring $A$,
are finitely presented. This argument uses the descended termwise unit and counit themselves, so
their normalization is fixed.
Uses: lem-weil-pbc-exact-functor-derived-factorization, lem-sp-exact-functor-preserves-homology,
lem-weil-pbc-unbounded-derived-iso-cohomology,
lem-sc-noetherian-finite-module-finite-presentation, def-weil-point-finite-cohomology-complexes,
def-weil-point-fg-complete-complexes.

4. For a constructible $A_n$-module sheaf $F$ on $s_{\mathrm{proet}}$, finite-ring constructible
origin gives $F\cong\nu_s^*G$ with $G$ constructible on $s_{\mathrm{et}}$. Every nonempty
locally closed subscheme of $s$ is $s$, since a field has no nontrivial ideals and its spectrum
has one point. Thus $G$ is finite locally constant. The algebraically closed etale-point theorem
identifies $G$ naturally with the constant sheaf of $G(s)$; the same isomorphism respects
addition and every scalar action, by its naturality in maps of underlying sheaves. Its identity
stalk is $G(s)$, and the finite-locally-constant module-values theorem explicitly turns its
finite constant-value trivializations into finite geometric stalks. Hence $G(s)$ is finite.
Pullback $\nu_s^*$ carries constant module sheaves to constant module sheaves: both composites
are left adjoint to sections, since sections of $\nu_{s,*}F$ are $F(s)$ by the
comparison-morphism definition; equivalently their maps send each constant value to that same
value. The finite comparison unit gives $G(s)\cong(\nu_s^*G)(s)=F(s)$. It follows that the
canonical evaluation counit $\underline{F(s)}\to F$ is an isomorphism. Conversely a constant
finite module sheaf is locally constant and has finite geometric stalks by the constant-stalk
theorem, so is constructible. In particular sections detect zero sheaves within this
constructible subcategory.
Uses: lem-weil-pbc-finite-ring-constructible-sheaf-origin,
def-weil-pbc-etale-constructible-sheaf, lem-weil-pbc-finite-locally-constant-module-values,
lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant,
def-weil-pbc-site-comparison-morphism, prop-weil-pbc-site-comparison-finite-level,
def-weil-pbc-constant-sheaf, lem-weil-proetale-constant-sheaf-stalk.

5. For $M\in D^b_{\mathrm{fin}}(A_n)$, exactness of $L_{\underline{A_n}}$ identifies its
cohomology sheaves with the constant finite modules $\underline{H^i(M)}$; these vanish outside a
finite interval and are constructible by step 4. Thus $L_{\underline{A_n}}M\in D^b_c(s,A_n)$.
Conversely sections have the asserted target by point-sections finiteness. For $K\in
D^b_c(s,A_n)$, the cohomology maps of the derived counit $L_{\underline{A_n}}\Gamma(s,K)\to K$
are exactly the evaluation counits of its cohomology sheaves, by exact-functor homology
compatibility. Step 4 makes them isomorphisms, and the derived isomorphism criterion makes this
counit an isomorphism. Together with the unit in step 3 this proves the torsion equivalence. It
also proves the detection statement used below: a bounded constructible torsion complex with
zero section complex is zero. Its exactness and shift compatibility are already those of
termwise sections in the point-sections theorem.
Uses: def-weil-finite-torsion-constructibility, lem-weil-point-sections-finiteness,
lem-sp-exact-functor-preserves-homology, lem-weil-pbc-unbounded-derived-iso-cohomology,
lem-weil-point-proetale-sections-exact.

6. Every bounded $A$-complex with finitely generated cohomology is perfect. To verify the needed
hypotheses explicitly, take a finitely generated module $N$. The Noetherian
finite-free-resolution theorem gives $A^{r_1}\to A^{r_0}\to N\to0$. Its kernel $J\subset
A^{r_0}$ is finitely generated, being the image of the first finite free term, and is torsion
free because $A$ is a domain and $A^{r_0}$ is torsion free. The finite torsion-free DVR theorem
makes $J$ finite free. Thus $0\to J\to A^{r_0}\to N\to0$ is a bounded finite-free resolution.
The perfect-cohomology assembly theorem now gives a bounded finite-projective representative $Q$
for every $M\in D^b_{\mathrm{fg}}(A)$. The argument includes $N=0$ and does not impose finite
Tor dimension on modules over $A_n$; those rings may be singular.
Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-finite-free-resolution-noetherian,
lem-sc-dvr-fg-torsionfree-free, lem-sf-perfect-cohomology-assembly,
def-weil-point-fg-complete-complexes.

7. For any bounded finite-projective $A$-complex $Q$, $L_BQ=B\otimes_{\underline A}\underline Q$
is in $D^b_c(s,A)$ by the integral stratified-perfect characterization, using its explicit
comparison with the category of derived-complete integral coefficients in the statement. Its
hypotheses hold: $s$ is noetherian, of dimension zero, and $\ell$ is invertible in $k$ because
$\ell\ne p$; use the single stratum $s$ and the identity trivializing cover. This is its
condition (ii), with the specified completed sheaf $B$. In particular this assertion includes
completeness and the reductions required in the present definition, rather than silently
identifying two integral categories. The reduction calculation of step 1 also gives
$L_BQ\otimes_B^L\underline{A_n}\cong\underline{Q\otimes_A A_n}$: for a finite projective term
take a direct summand of a finite free term and use the same quotient map. These reductions have
bounded finite cohomology in the fixed term interval of $Q$, independent of $n$. Thus step 6
shows $L_B$ carries every object of $D^b_{\mathrm{fg}}(A)$ into the integral source.
Point-sections finiteness carries the integral source into $D^b_{\mathrm{fg}}(A)$. The
adjunction of step 3 therefore restricts to these full subcategories, and its unit is an
isomorphism there.
Uses: lem-weil-pbc-integral-stratified-perfect-characterization,
lem-weil-pbc-completed-constant-sheaf-reduction, def-weil-derived-complete-integral-detailed,
lem-weil-point-sections-finiteness.

8. Sections are conservative on the integral source as well. If $C\in D^b_c(s,A)$ and
$\Gamma(s,C)=0$, compute its $n$-th reduction using the finite free resolution
$[B\xrightarrow{\pi^n}B]\to\underline{A_n}$ from step 1. Tensoring this resolution with a K-flat
representative of $C$ gives the cone of multiplication by $\pi^n$; the K-flat property ensures
that tensoring the resolution quasi-isomorphism remains a quasi-isomorphism. Hence, after
restriction of scalars, $C\xrightarrow{\pi^n}C\to C_n\to C[1]$ is distinguished. Exact sections
show $\Gamma(s,C_n)=0$. Its actual $A_n$-coefficient reduction is bounded constructible by the
integral definition, so step 5 makes it zero (forgetting its scalar structure does not change
its cohomology). All reductions of $C$ therefore vanish. Its derived-completeness Roos triangle
is $C\to0\to0\to C[1]$, so $C=0$, for example by the long exact cohomology sequence and the
cohomological isomorphism criterion. For arbitrary integral $K$, form the cone $C$ of the
restricted counit $L_B\Gamma(s,K)\to K$. It is in the integral source by its
triangulated-subcategory theorem. Applying sections makes this counit an isomorphism by the unit
isomorphism and the adjunction triangle identity; thus $\Gamma(s,C)=0$. The preceding argument
gives $C=0$, hence the counit is an isomorphism. This proves the integral equivalence, with the
exactness and shift comparisons of sections.
Uses: def-weil-integral-derived-reduction, lem-pc-kflat-resolution, def-pc-kflat-complex,
lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-point-proetale-sections-exact,
def-weil-derived-complete-integral-detailed, def-weil-derived-complete,
lem-weil-integral-constructible-triangulated, lem-sf-derived-homology-long-exact,
lem-weil-pbc-unbounded-derived-iso-cohomology.

9. For the rational stage first check full faithfulness for the specified raw localization. Put
$M=\Gamma(s,K)$, $N=\Gamma(s,K')$ for integral objects. The integral equivalence is $A$-linear:
all its maps above are maps of $A$-modules and the section action is the canonical one. Thus it
identifies $\operatorname{Hom}(K,K')$ with $\operatorname{Hom}_{D(A)}(M,N)$ as $A$-modules. Both
$M,N$ are perfect by step 6. Apply perfect RHom base change to $A\to E$ and the first argument
$M$. Here $E=A[1/\pi]$ by the uniformizer localization theorem and is flat by localization
flatness. Consequently taking $H^0$ of that base-change isomorphism, using flat-tensor
exactness, gives the canonical bijection
$\operatorname{Hom}_{D(A)}(M,N)\otimes_AE\cong\operatorname{Hom}_{D(E)}(M\otimes_AE,N\otimes_AE)$.
The identification $H^0(R\operatorname{Hom}(M,N))=\operatorname{Hom}_{D(A)}(M,N)$ is precisely
the K-injective Hom-complex theorem applied on the one-object ringed site (and likewise for
$E$). The base-change theorem specifies its map to be the scalar extension of the
functor-induced Hom map; hence this bijection sends $f\otimes a$ to $a(f\otimes E)$, exactly the
morphism map defining the rational fibre functor. The rationalization definition gives the
left-hand Hom groups, so this proves full faithfulness without adjoining idempotents.
Uses: def-weil-rationalization-karoubi, lem-weil-l-adic-integers-localization-uniformizer,
lem-weil-pbc-localization-flat, lem-pc-base-change-rhom-perfect, lem-weil-pbc-flat-tensor-exact,
def-pur-derived-internal-hom, lem-pur-rhom-into-kinjective-local,
def-weil-finite-coefficient-point.

10. For $V\in D^b_{\mathrm{fd}}(E)$ choose a representing complex. For each of its finitely many
nonzero $H^i(V)$ choose a finite basis and lift each basis vector to a cycle in degree $i$. The
basis theorem supplies these bases; the lifts exist by the definition of cohomology as cycles
modulo boundaries. Sending the standard basis in degree $i$ to these cycles defines a chain map
from the zero-differential bounded finite free complex $P_E=\bigoplus_iE^{d_i}[-i]$ to the
representative of $V$. It induces the chosen isomorphism on every cohomology module, so is a
quasi-isomorphism. Let $P_A=\bigoplus_iA^{d_i}[-i]$ with zero differential. Step 7 puts $L_BP_A$
in the integral source, and step 3 identifies its sections with $P_A$; after rationalization its
image is $P_E\cong V$. This proves essential surjectivity, including $V=0$ by the empty sum. The
rational functor commutes with shifts and preserves distinguished triangles: sections does so,
and flat tensoring with $E$ is an exact functor and hence has the exact derived factorization.
Every distinguished triangle in the raw rationalization is isomorphic to an image of an integral
distinguished triangle by its definition. Thus the specified rational fibre functor is an exact
equivalence.
Uses: def-weil-point-fd-complexes, lem-weil-pbc-vector-space-basis-through-vector,
lem-weil-pbc-unbounded-derived-iso-cohomology, def-weil-rationalization-karoubi,
lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-flat-tensor-exact.

11. For source objects $(E,K)$ and $(E',K')$ in the common-stage category, a morphism is
represented over a finite common field $L$. The scalar-extension comparison $\varphi_{L/E}$
identifies its image under the fibre functor with conjugation by the canonical comparisons at
$E$ and $E'$. At each common field $L$, Steps 9–10 give the rational fibre equivalence and hence
a bijection on the represented Hom groups. The identity and three-field composition equations in
the section scalar-extension theorem make these bijections compatible with all transition maps.
Uses: lem-weil-point-sections-scalar-extension, def-weil-finite-coefficient-point.

12. The directed-colimit statement [def-weil-directed-colimit-abelian-groups] gives
representatives and equality after passage to a common later stage for exactly these
abelian-group Hom colimits. A target representative lifts through the rational Hom bijection at
its stage. If two images agree, they agree at a common later stage; compatibility from Step 11
and injectivity at that stage make the original representatives agree there. Thus the
Hom-colimit map is bijective. A target object $(E,V)$ has a preimage $(E,K)$ by Step 10 at the
same field $E$. Hence the common-stage functor is fully faithful and essentially surjective.
Uses: def-weil-directed-colimit-abelian-groups, def-weil-point-fd-qlbar-category,
def-weil-algebraically-closed-coefficients.

13. The section scalar-extension theorem defines
$\varphi_{L/E,K}=(\Gamma(s,\chi_{L/E,K})\circ\theta_{L/E,K})^{-1}$. The completion comparison
commutes with every integer shift by [lem-weil-point-completed-scalar-shift], and the
sections-tensor comparison does so by [lem-weil-point-sections-tensor-shift]. Exact termwise
sections preserves the first equality, so the composite and its inverse commute with the
specified shifts. Tensoring with $L$ preserves that equality at the rational stage. Naturality
and the scalar-extension theorem's identity and three-field equations make it compatible with
the common-stage transition maps. Thus the common-stage fibre functor commutes with shifts.
Uses: lem-weil-point-sections-scalar-extension, lem-weil-point-completed-scalar-shift,
lem-weil-point-sections-tensor-shift, lem-weil-point-proetale-sections-exact.

14. Finally, every distinguished source triangle in the common-stage category is represented at
one finite stage. The rational fibre functor is exact at that stage by Step 10, and the scalar
comparisons at the three vertices and the last shifted arrow are compatible by Step 13. Hence
the image triangle is distinguished in the target common-stage category. This proves the fourth
equivalence, with the exact shifts and triangles specified in the statement.
Uses: def-weil-point-fd-qlbar-category, lem-weil-point-sections-scalar-extension,
def-weil-algebraically-closed-coefficients, lem-weil-point-completed-scalar-shift,
lem-weil-point-sections-tensor-shift.
-/
theorem point_fibre_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : Padic.FiniteCoefficientFields l Ω) (n : ℕ) (hn : 1 ≤ n) :
    (pointFiniteFibre D l hl E.val n hn).IsEquivalence ∧
    (pointIntegralFibre D l hl E.val).IsEquivalence ∧
    (pointRationalFibre D l hl E.val).IsEquivalence ∧
    (pointQbarFibre D l hl Ω).IsEquivalence ∧
    (∃ c : (pointFiniteFibre D l hl E.val n hn ⋙
        (DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.val n))).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointIntegralFibre D l hl E.val ⋙
        (DerivedCategory.pointFgComplete
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E.val))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E.val)})).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointRationalFibre D l hl E.val ⋙
        (DerivedCategory.pointFiniteDimensional E.val).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointQbarFibre D l hl Ω).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        DerivedCategory.pointFdQbarDistinguished l Ω
          ((@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T)) := by
  sorry

end WeilConjectures
