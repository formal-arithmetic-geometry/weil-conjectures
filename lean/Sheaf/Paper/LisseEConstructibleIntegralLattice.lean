/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.CategoryTheory.ExtOneExtensionClassification
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.EtaleStratifiedFinite
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.NumberTheory.Padics.CoefficientExtension
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.CategoryTheory.DerivedCountableSumsExact
import Sheaf.CategoryTheory.SequenceRelativeHomTelescope
import Sheaf.Paper.AdicGlobalDerivedHom
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent
import Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization

/-!
# A lisse finite-extension sheaf has a constructible integral lattice

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13,
Definitions 6.8.1, 6.8.3 and 6.8.10; Lemma 6.8.2(1)
(blueprint: lem-weil-pbc-lisse-e-constructible-integral-lattice).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- A lisse rational sheaf has a constructible integral model, with no global freeness
requirement on that model. `WithAbs` equips the field with its canonical absolute-value
topology and transports its valuation ring; `ULift` changes only the coefficient size.
Source: Bhatt--Scholze, Lemma 6.8.13
(blueprint: lem-weil-pbc-lisse-e-constructible-integral-lattice).

Proof:
1. By [lem-weil-pbc-continuous-coefficients-immersion-restriction], the rings in the statement are
precisely the completed integral and continuous rational coefficient sheaves, $E_T=A_T[1/\varpi]$,
and restriction to any locally closed subscheme identifies the two coefficient rings with the
corresponding rings there. Write $S(M)=E_T\otimes_{A_T}M=M[1/\varpi]$. As an underlying abelian
sheaf this is the filtered colimit of $M\xrightarrow{\varpi}M\xrightarrow{\varpi}\cdots$: the
class of $m$ at stage $n$ is $m/\varpi^n$, and the transition relation is precisely the fraction
relation. The two colimit nodes identify module colimits with the underlying abelian colimits and
make this functor exact. Restriction of scalars from $E_T$ to $A_T$ is exact because kernels and
cokernels have their underlying abelian sheaves.
2. For two constructible integral sheaves $P,Q$ as described in the statement, the integral
characterization places $P[0],Q[0]$ in the bounded constructible complete category. The scalar-
extension/restriction adjunction is given on sheaves by $\phi\mapsto(m\mapsto\phi(1\otimes m))$,
with inverse $\psi\mapsto(e\otimes m\mapsto e\psi(m))$. Step 1 shows that both functors are exact;
the exact-functor and derived-adjunction nodes therefore give the same adjunction on derived
categories. Apply bounded-below compactness to $P[0]$ and the copies of $Q[0]$, with common lower
bound zero. Coproducts are exact: they are filtered colimits of their finite subsums, which are
exact, so step 1 applies. Therefore termwise coproducts preserve quasi-isomorphisms and compute
the derived coproducts used here. The telescope of $Q\xrightarrow{\varpi}Q\to\cdots$ is the cone
of $1-s$ on $\bigoplus_{n\geq0}Q$, where $s$ sends summand $n$ to summand $n+1$ by $\varpi$. The
direct sum of sheaves is the sheafification of the sectionwise direct sum by the module-colimit
node. Thus every section locally has a finitely supported representative. The map $1-s$ is
injective: in such a kernel representative the first coordinate and then every successive
coordinate is zero; sheafification preserves this conclusion by exactness from step 1; its
cokernel is $Q[1/\varpi]$ by the fraction relations. To justify the use of a cone here, choose
K-injective resolutions of the two direct-sum terms by the resolution-existence node and represent
$1-s$ by a chain map between them using K-injective Hom comparison. The cone of that map is
K-injective: mapping an acyclic complex into it gives the cone of the two acyclic Hom complexes,
hence is acyclic. The defining Hom-complex formula identifies
$\operatorname{Hom}^{\bullet}(P,C(f))^q$ with
$\operatorname{Hom}^{\bullet}(P,J)^q\oplus\operatorname{Hom}^{\bullet}(P,I)^{q+1}$ for $f:I\to J$.
On a pair $(a,b)$ its differential is $(d(a)+f\circ b,-d(b))$, exactly the cone differential.
Global sections of the Hom complex therefore take this cone to the cone of the corresponding
global Hom-complex map. For a K-injective representative $I_B$ of any target $B$, K-injective Hom
comparison identifies $H^q\operatorname{Hom}^{\bullet}(P,I_B)$ with
$\operatorname{Hom}_{D(A_T)}(P,B[q])$: cocycles are chain maps and boundaries are null homotopies.
Thus compactness identifies derived Hom from $P$ of the telescope with the same telescope on
$R\operatorname{Hom}_{A_T}(P,Q)$. Exactness of filtered colimits from step 1 identifies its
cohomology with localization. Taking degree one and using the adjunction yields the natural
bijection $\operatorname{Ext}^1_{A_T}(P,Q)[1/\varpi]\cong\operatorname{Ext}^1_{E_T}(S(P),S(Q))$.
In particular every rational extension class is $S(\alpha)/\varpi^n$ for an integral class
$\alpha$ and an integer $n\geq0$.
3. Consequently the rationalizations of constructible integral sheaves are closed under
extensions. Given $0\to S(Q)\to F\to S(P)\to0$, let its class be $S(\alpha)/\varpi^n$ as in step
2. Degree-one extension classification realizes $\alpha$ by $0\to Q\to N\to P\to0$. The short-
exact-complex triangle node identifies its middle term with the shifted cone of its connecting
morphism. The integral characterization then makes $N$ constructible: its degree-zero complex is
the shifted cone of $P[0]\xrightarrow{\alpha}Q[0][1]$, hence belongs to the integral category, and
clause (iii) describes its cohomology $N$. Exact scalar extension sends this sequence to the class
$S(\alpha)$. Pushing its rational sequence out along the automorphism $\varpi^{-n}$ of $S(Q)$
changes its class to $S(\alpha)/\varpi^n$; because this is an automorphism, its middle term is
isomorphic to $S(N)$. The bijection in extension classification now identifies that sequence with
the given sequence, so $S(N)\cong F$. This is only an isomorphism of middle terms, as required;
the chosen identification of the subobject has been scaled.
4. We prove the assertion for every reduced closed subscheme $X$ of $T$, and every lisse
$E_X$-sheaf, by noetherian induction on its closed support. Such $X$ is noetherian, finite-
dimensional and $\ell$-coprime: affine rings are quotients of noetherian rings, strict chains of
closed irreducible subsets are chains in $T$, and an inverse of $\ell$ maps to an inverse in every
quotient local ring. The minimal-closed-subset node supplies the induction, with empty support
having the zero model. On a nonempty reduced $X$, use [lem-weil-pbc-lisse-lattice-etale-local] to
obtain an etale covering with lisse integral models. Choose a finite affine Zariski covering of
$X$ and apply etale affine refinement on each affine; the resulting finite disjoint union $Y$ of
affine schemes is a jointly surjective etale cover carrying a lisse integral model. Both $X$ and
$Y$ are qcqs: $X$ is noetherian, and $Y$ is a finite union of affine components. Apply etale
stratified finiteness to $Y\to X$. On each stratum the pullback is finite etale and surjective and
the integral model pulls back to a lisse integral model. The coefficient restriction of step 1
identifies these as the required coefficient sheaves. Thus [lem-weil-pbc-lisse-lattice-finite-
etale-descent] gives a lisse integral model for the restriction of $L$ to each of these strata.
5. Extract a nonempty open $U\subseteq X$ on which such a model exists. There are finitely many
irreducible components, each with a generic point. Choose a component $C$ and its generic point
$\eta$, and the stratum $Z\hookrightarrow X$ containing $\eta$. Write its image as $O\cap F$ with
$O$ open and $F$ closed. Since $F$ contains $\eta$, it contains $C$. Remove all other components
and intersect with $O$. The resulting nonempty open $U$ lies in $C\cap O$, hence in the image of
$Z$. It factors through $Z$ as a scheme: in the open part of the stratum immersion its ideal
sections vanish at every point of the reduced open subscheme $U$, so lie in its nilradical and are
zero. On affine charts this is exactly factorization of the ring map through the quotient defining
the closed immersion. Pull back the stratum model along this open immersion $U\to Z$ to get a
lisse integral model $M_U$ of $L|_U$. The open is quasi-compact by the noetherian-open node.
6. Let $i:Z_0\hookrightarrow X$ be the reduced induced closed subscheme of $X\setminus U$ and
$j:U\hookrightarrow X$ the open immersion. Its support is strictly smaller. The induction
hypothesis supplies a constructible integral model $M_Z$ for $i^{-1}L$. Put $Q=j_!M_U$ and
$P=i_*M_Z$. The ringed open-closed node gives their restrictions $(M_U,0)$ and $(0,M_Z)$ on
$U,Z_0$. Consequently adjoining the open stratum $U$ to the finitely many strata of $Z_0$ proves
both $P$ and $Q$ are constructible integral sheaves. The local modules are finite free on $U$ and
the given finitely presented modules on $Z_0$, with zero modules on the complementary pieces.
Scalar localization commutes with $i_*$ because that node gives filtered-colimit preservation for
qcqs $X$. It commutes with $j_!$ because $j_!$ is a left adjoint, hence preserves the sequential
colimit expressing localization; the scalar multiplications and the coefficient identifications in
step 1 identify these colimits as module sheaves. Therefore $S(Q)\cong j_!j^{-1}L$ and $S(P)\cong
i_*i^{-1}L$. The same node gives $0\to S(Q)\to L\to S(P)\to0$. Step 3 now provides a constructible
integral model for $L$ on $X$, completing the noetherian induction.
7. Finally let $r:T_{\mathrm{red}}\hookrightarrow T$ be the reduced induced closed subscheme with
full support. The open-closed node applied with empty complementary open gives $L\cong r_*r^{-1}L$
and $r^{-1}r_*\cong1$. By step 1 its coefficient inverse images are $A_{T_{\mathrm{red}}}$ and
$E_{T_{\mathrm{red}}}$. The preceding induction supplies a constructible integral model
$N_{\mathrm{red}}$ on $T_{\mathrm{red}}$. Set $N=r_*N_{\mathrm{red}}$. Its supporting strata,
composed with $r$, are immersions into $T$, partition the same underlying space, and restrict $N$
to the corresponding restrictions of $N_{\mathrm{red}}$ by $r^{-1}r_*\cong1$. Hence they witness
precisely the finite stratification required in the statement. Filtered-colimit preservation by
$r_*$ gives $S(N)\cong r_*S(N_{\mathrm{red}})\cong r_*r^{-1}L\cong L$. This also covers the empty
scheme, rank zero, disconnected schemes and nonreduced schemes, and asserts no global lissity of
$N$. -/
theorem exists_constructible_integral_lattice
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
    (_hℓ : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing T (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    [L.IsFiniteLocallyFree] :
    ∃ N : SheafOfModules.{u + 1} (latticeModuleRing T (latticeCoefficientIntegers l E)),
      IsContinuousConstructible T (latticeCoefficientIntegers l E) N ∧
      Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (integralLatticeCoefficientMap T l E) N ≅ L) := by
  sorry

end AlgebraicGeometry.ProEtale
