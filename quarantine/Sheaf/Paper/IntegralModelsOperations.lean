/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Sites.Precoverage
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Operations on bounded constructible integral coefficient complexes

Source: blueprint main-20261015, sec-six-functors-basics, sk-lem-integral-models,
sk-lem-integral-models-operations.md (blueprint: det-lem-integral-models-operations).

Constructibility uses finite constant scalar models, as in the recorded
sk-def-sfb-constructible. The tensors and the projection formula are ambient and uncompleted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Inverse image, uncompleted relative derived tensor and locally closed extension by zero
preserve bounded constructibility over the integral coefficient ring. The projection formula
holds for arbitrary unbounded complexes. The locally closed functor is written explicitly as
open extension by zero followed by derived closed direct image; the latter is ordinary direct
image on Noetherian schemes. Finite coefficient fields are represented inside the fixed
algebraic closure, with their induced valuation and ring of integers.

Source: blueprint main-20261015, sk-lem-integral-models-operations, clauses (1)--(4)
(blueprint: det-lem-integral-models-operations).

Proof plan (the reviewed DAG proof, retaining the finite constant scalar convention):

1. Use the integral coefficient ring sheaf $R_T=\mathcal O_{E,T}$ and write $A=\mathcal O_E$.
Here $\Dbc(T,A)$ means bounded complexes with constructible cohomology, with finite constant
local models $R_V\otimes_A P$ for finitely presented scalar $A$-modules $P$, as in
[sk-def-sfb-constructible, sk-def-sfb-bounded-constructible]. Thus we can prove membership
directly from cohomology and strata; we do not assume that an arbitrary bounded complex of
finite free modules splits into its terms. No additional completeness condition is inserted into
this definition.

2. For clause (1), [sk-prop-sfb-cartesian-coefficients] identifies $f^*R_Y=R_X$ and says that
module pullback is exact inverse image. It therefore preserves kernels, images, cokernels and
cohomology, so $H^q(f^*K)=f^*H^q(K)$ with the same bounds. For each constructible $H^q(K)$ pull
its finite stratification back to $X$ using [lemma-constructible-pullback-stratification]. Pull
each pro-étale covering of a stratum back to its fibre product with $X$; it is again a covering:
weakly étale arrows remain weakly étale by [lem-weil-pbc-weakly-etale-composition-base-change],
and the family remains fpqc by [lem-galois-fpqc-covering-base-change]. The covering definition
[def-weil-pbc-proetale-site] then applies, even though the new base is not an object of the old
small site. A scalar finite presentation $A^m\to A^n\to P\to0$ gives $R_V^m\to R_V^n\to
R_V\otimes_A P\to0$; exact inverse image pulls this cokernel presentation back to the same
scalar matrix over the new coefficient ring. Thus the pulled-back cohomology has finite constant
local models. The pulled-back strata are locally closed and hence constructible on the
Noetherian scheme $X$. This proves $f^*K\in\Dbc(X,A)$ for every $f$, without any finite-type or
field-base hypothesis.

3. For clause (3), first take an open immersion $j:U\hookrightarrow T$ and its complementary
closed immersion $i:Z\hookrightarrow T$. Every open subset of a Noetherian topological space is
quasi-compact, by Noetherian induction on closed subsets: if a finite subcover did not exist,
choose a minimal closed subset on which it fails; removing one cover member containing a point
gives a proper closed subset, covered finitely by minimality, and adjoining that member
contradicts minimality. Apply this standard lemma to the underlying Noetherian spaces; the open
immersion is quasi-compact. With the inverse-image coefficient rings,
[lem-weil-pbc-proetale-ringed-open-closed] says that $j_!$ and $i_*$ are exact, restrict to the
identity on their own loci, and restrict to zero on the complementary loci. The coefficient
rings agree with $R_U,R_Z$ by [sk-prop-sfb-cartesian-coefficients]. Given a finite
stratification for a constructible sheaf on $U$ (respectively $Z$), regard its strata as locally
closed subschemes of $T$ and append the complementary closed (respectively open) locus. On the
original strata the extended sheaf has the same scalar local models; on the added locus its
model is zero. Hence both functors preserve constructible sheaves. Since they are exact, their
termwise functors commute with cohomology and preserve bounds, proving preservation of $\Dbc$.
Apply the open conclusion to $u:S\hookrightarrow\overline S$ and then the closed conclusion to
$i:\overline S\hookrightarrow X$ to obtain $a_!L=i_*u_!L\in\Dbc(X,A)$.

4. For the tensor calculation first take constructible sheaves $F,G$ in degree zero. Intersect
their finite stratifications, forming the actual fibre products of strata using
[lemma-constructible-pullback-stratification]; the intersections are locally closed, disjoint
and cover $X$. On each stratum $T$ intersect the two pro-étale trivializing covers by fibre
products $V_\alpha\times_T W_\beta$. The base-change and composition axioms of a site
[def-weil-pbc-sites-and-cohomology] make this a covering: first pull the second cover back over
each member of the first, then compose. On its objects $V$, exact inverse image and the scalar
cokernel argument of step 2 identify the two sheaves with $R_V\otimes_A P$ and $R_V\otimes_A Q$
for finitely presented scalar modules $P,Q$. By
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], the restriction of $F\otimes^{\mathbf
L}_{R_X}G$ is the derived tensor of these two models.

5. The ring $A=\mathcal O_E$ is a DVR, and each nonzero element is a unit times a power of a
uniformizer $\pi$ [lem-weil-l-adic-extension-integers-dvr]. Choose a finite free surjection
$A^n\twoheadrightarrow P$, with kernel $N\subset A^n$. By
[lem-sc-dvr-saturation-line-smith-normal-form] the inclusion of $N$ has a diagonal matrix in
finite bases, of rank at most $n$. Each diagonal entry is nonzero because the inclusion is
injective, and can be replaced by $\pi^r$ after multiplying a basis vector by a unit. Taking the
cokernel gives a finite direct sum decomposition of $P$ into copies of $A$ and $A/\pi^r$ with
$r\geq1$; unit entries give zero summands. Do the same for $Q$. Right exactness of ordinary
tensor gives decompositions of the two local models into copies of $R=R_V$ and $R/\pi^rR$.

6. The constant-to-completed coefficient map $A_V\to R_V$ is flat by clause (1) of
[det-prop-integral-criterion-constant-coefficients]. The constant presheaf map given by
multiplication $A\xrightarrow{\pi^r}A$ is injective because $A$ is a domain. Its sheafification
is multiplication on the constant ring sheaf [def-weil-pbc-constant-sheaf] and is still
injective by exact sheafification [lem-weil-pbc-sheafification-exact]. Flatness here means that
the sheaf tensor functor $-\otimes_{A_V}R_V$ is exact [def-pc-flat-sheaf-modules]. Applying that
functor to the kernel sequence $0\to A_V\xrightarrow{\pi^r}A_V$, and identifying
$A_V\otimes_{A_V}R_V=R_V$, gives the kernel sequence $0\to R_V\xrightarrow{\pi^r}R_V$. Hence
this multiplication on $R$ is injective. Consequently $[R\xrightarrow{\pi^r}R]$, placed in
degrees $-1,0$, resolves $R/\pi^rR$. It is K-flat directly from [def-pc-kflat-complex]:
tensoring it with any acyclic complex gives the cone of multiplication by $\pi^r$ on that
complex, up to the usual shift, which is acyclic by the cohomology long exact sequence
[lem-sf-derived-homology-long-exact]. Also $R[0]$ is K-flat because tensoring with it is the
identity. Thus these explicit complexes compute the derived tensors, using
[sk-def-sfb-derived-tensor-hom].

7. Tensoring a free summand with another summand leaves it in degree zero. For two torsion
summands the explicit resolution of step 6 gives $$ (R/\pi^rR)\otimes_R^{\mathbf
L}(R/\pi^sR)\simeq[R/\pi^sR\xrightarrow{\pi^r}R/\pi^sR]. $$ If $r\geq s$, the differential is
zero, so both cohomology sheaves are $R/\pi^sR$. If $r<s$, the cokernel is $R/\pi^rR$ and the
kernel is $\pi^{s-r}R/\pi^sR\cong R/\pi^rR$. To check the latter for sheaves, lift a quotient
section locally to $x\in R$. The equation $\pi^r x=0$ modulo $\pi^s$ means, after a refinement,
$\pi^r x=\pi^s y$. Cancellation using step 6 gives $x=\pi^{s-r}y$. For the map $R\to R/\pi^sR$,
$y\mapsto\pi^{s-r}y$, a section in its kernel locally satisfies $\pi^{s-r}y=\pi^s z$.
Injectivity of $\pi^{s-r}$ gives $y=\pi^r z$; conversely every $y=\pi^r z$ maps to zero. Its
kernel is therefore exactly $\pi^rR$. Thus in both cases $H^{-1}$ and $H^0$ are
$R/\pi^{\min(r,s)}R$, and other cohomology vanishes. Finite sums give the calculation for the
local models in step 5. These resulting cohomology sheaves have finite constant scalar models,
and all local tensors have amplitude in $[-1,0]$. Exact restrictions commute with cohomology. By
[lem-weil-pbc-noetherian-stratum-detection], these restrictions detect vanishing outside that
interval globally. The models themselves give constructibility by [sk-def-sfb-constructible].
Hence $F\otimes^{\mathbf L}G\in\Dbc(X,A)$.

8. Extend the sheaf calculation to clause (2) by two finite cohomological inductions. The
standard truncation triangles of [def-sbc-standard-tstructure-derived-category] give, for
bounded $K$ with cohomology in $[a,b]$, $$\tau_{\leq b-1}K\longrightarrow K\longrightarrow
H^b(K)[-b]\longrightarrow(\tau_{\leq b-1}K)[1].$$ Derived tensor is exact in each variable
[lem-weil-pbc-ringed-projection-mate-exact], and $\Dbc(X,A)$ is a triangulated subcategory on
Noetherian $X$ [sk-def-sfb-bounded-constructible]. Fix a constructible sheaf $G$. The empty
interval is the zero case and the one-degree case is step 7 shifted. Tensoring the displayed
triangle with $G$, the first term is handled by induction on $b-a$ and the third by the sheaf
case; closure under triangles gives $K\otimes^{\mathbf L}G$. Now fix such a $K$ and induct on an
interval $[c,d]$ containing the cohomology of $M$. The empty interval is again zero, the
one-degree case is the conclusion just established shifted, and the triangle for $M$ gives outer
terms $K\otimes^{\mathbf L}\tau_{\leq d-1}M$ and $(K\otimes^{\mathbf L}H^d(M))[-d]$. They belong
to $\Dbc$ by induction and the first induction. Therefore the middle term $K\otimes^{\mathbf
L}M$ belongs to $\Dbc$. All these are ambient derived tensors; no completion is taken.

9. For clause (4), prove the open projection formula on the unbounded ambient categories. For
$j:U\hookrightarrow T$, the pro-étale site of $U$ is the localized site of $T$ at $U$
[lem-weil-proetale-weakly-etale-localization], and the coefficient ring restricts to $R_U$
[sk-prop-sfb-cartesian-coefficients]. Choose a representative complex for $L$ and a K-flat
resolution $P\to M$ with flat terms [lem-pc-kflat-resolution]. The complex $j^*P$ is K-flat with
flat terms by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Thus $j_!L\otimes^{\mathbf
L}M$ is represented by $j_!L\otimes P$, and $L\otimes^{\mathbf L}j^*M$ by $L\otimes j^*P$. Apply
[lem-weil-pbc-ringed-slice-extension-tensor] in each bidegree. Since $j_!$ is left adjoint to
$j^*$ and exact [lem-weil-pbc-proetale-ringed-open-closed], it preserves the direct sums in
totalization [lem-weil-pbc-left-adjoint-preserves-colimits] and induces its termwise derived
functor. Write the bidegree isomorphism as $\theta_{p,q}:(j_!L^p)\otimes P^q\to j_!(L^p\otimes
j^*P^q)$. Naturality in its first argument makes $\theta$ commute with the maps induced by
$d_L^p$, and naturality in its second argument makes it commute with the maps induced by
$d_P^q$. Additivity then makes it commute with their signed sum $d_L\otimes1+(-1)^p1\otimes d_P$
in bidegree $(p,q)$. Summing these maps over $p+q=n$ gives an isomorphism of total complexes,
naturally $$j_!L\otimes^{\mathbf L}M\simeq j_!(L\otimes^{\mathbf L}j^*M).$$ This argument
imposes no bounds or constructibility on $L,M$.

10. For a closed immersion $i:Z\hookrightarrow T$ with open complement $j$, $i_*$ is exact since
$T$ is Noetherian [lem-weil-pbc-proetale-ringed-open-closed]. Thus $Ri_*=i_*$ termwise and
$Li^*=i^*$ because the coefficient system is Cartesian [sk-prop-sfb-cartesian-coefficients]. The
natural projection map of [lem-weil-pbc-ringed-projection-mate-exact] is $$i_*N\otimes^{\mathbf
L}M\longrightarrow i_*(N\otimes^{\mathbf L}i^*M).$$ Its restriction by $i^*$ is the identity on
$N\otimes^{\mathbf L}i^*M$: the defining mate uses the counit $i^*i_*N\to N$, which is an
isomorphism, and the monoidal pullback comparison
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Its restriction by $j^*$ is a map $0\to0$,
since $j^*i_*=0$ and pullback commutes with derived tensor. The identities and vanishings are
those of [lem-weil-pbc-proetale-ringed-open-closed]. The two strata $Z,U$ jointly detect
isomorphisms by [lem-weil-pbc-noetherian-stratum-detection], so this projection map is an
isomorphism for arbitrary $N,M$.

11. Finally apply step 10 with $N=u_!L$ and then step 9 inside $\overline S$: $$
(i_*u_!L)\otimes^{\mathbf L}M\simeq i_*(u_!L\otimes^{\mathbf L}i^*M)\simeq
i_*u_!(L\otimes^{\mathbf L}u^*i^*M)=a_!(L\otimes^{\mathbf L}a^*M). $$ Here $a^*=u^*i^*$ by
composition of inverse-image functors [lem-weil-pbc-site-morphism-composition] and the Cartesian
coefficient identifications already fixed. Both factors are the ambient, exact immersion
functors from step 3. This proves clause (4) with precisely its stated arbitrary derived objects
and is natural in both arguments.
-/
theorem integralModelsOperations (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) f).mapDerivedCategory).obj K)) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X] (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj M)) ∧
    (∀ {S Z X : Scheme.{u}} [IsNoetherian S] [IsNoetherian Z] [IsNoetherian X]
      (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) S))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) S L →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj
          (((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.val)
            j).mapDerivedCategory).obj L))) ∧
    (∀ {S Z X : Scheme.{u}} [IsNoetherian S] [IsNoetherian Z] [IsNoetherian X]
      (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
      (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) S)))
      (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      Nonempty
        ((((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj
          (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj
            (((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.val)
              j).mapDerivedCategory).obj L))).obj M) ≅
          ((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj
            (((openImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.val)
              j).mapDerivedCategory).obj
              (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) S).obj L).obj
                (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) (j ≫
                  i)).mapDerivedCategory).obj M))))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
