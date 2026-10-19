/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.SetTheory.Cardinal.Finite
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.ModuleLocalConstancyOfFiniteUnderlying
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Constant direct image across a strict normal crossings boundary

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XVI Corollary 3.1.3,
Theorem 3.1.1, and XIII Proposition 3.6.2
(blueprint: lem-per-regular-normal-crossings-constant-image).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical `Rj_* B` for the inclusion `j` of the open complement of `D`.
The input is the constant sheaf of the rank-one module `B`, placed in degree zero.
Source: ILO XVI Corollary 3.1.3
(blueprint: lem-per-regular-normal-crossings-constant-image). -/
def normalCrossingsConstantDirectImage (B : Type (u + 1)) [CommRing B]
    {Y : Scheme.{u}} (D : Y.IdealSheafData) : DerivedCategoryModule B Y :=
  (rightDerivedLowerStar (ModuleCat.{u + 1} B) (Scheme.Opens.ι D.support.compl)).obj
    ((_root_.DerivedCategory.singleFunctor
      (Sheaf (Scheme.Opens.toScheme D.support.compl).smallEtaleTopology
        (ModuleCat.{u + 1} B)) 0).obj
      ((constantSheaf (Scheme.Opens.toScheme D.support.compl).smallEtaleTopology
        (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B)))

/-- Constant coefficients have constructible direct image with the component-count bound.
Source: ILO XVI Corollary 3.1.3, deduced from Theorem 3.1.1; XIII Proposition 3.6.2
(blueprint: lem-per-regular-normal-crossings-constant-image).

Proof (the node's strengthened divisor-deletion induction):
1. Put $A=\mathbf F_\ell$. We prove the following strengthened induction assertion for every
$m\geq0$, simultaneously for all integers $t$: if $X$ is regular Noetherian with $\ell$
invertible and $C_1,\ldots,C_m$ are closed regular subschemes whose every nonempty indexed
intersection $C_J$ is regular with $\dim\mathcal O_{X,x}-\dim\mathcal O_{C_J,x}=|J|$ at each of
its points, then, for $u:X-\bigcup_iC_i\hookrightarrow X$, $Ru_*A(t)$ has constructible
cohomology in degrees $[0,m]$ only. Empty or disconnected $C_i$ and empty intersections are
allowed. The given boundary supplies exactly this intersection condition by
[def-trf-strict-normal-crossings-boundary]. For $m=0$, $u$ is the identity and $A_X(t)$ is a
finite locally constant rank-one sheaf by [lem-asd-etale-finite-twist-pullback]; hence the
assertion holds. For any $m$, negative higher direct images of a sheaf vanish: the bounded-below
injective resolution defining [def-weil-pbc-direct-image] can start in degree zero.

2. We will use tensor transport only for the invertible Tate line $L=A_X(t)$, whose inverse is
$A_X(-t)$: evaluation is an isomorphism since on a trivializing etale cover it is multiplication
$A\otimes_AA\to A$. For any scheme morphism $f:T\to X$ and any derived $E$, the derived
adjunction of [def-kun-projection-formula-map] and the monoidal inverse image of
[lem-kun-inverse-image-monoidal] give natural bijections $$\operatorname{Hom}(N,Rf_*E\otimes
L)\cong\operatorname{Hom}(N\otimes L^{-1},Rf_*E)\cong\operatorname{Hom}(f^{-1}N\otimes
f^{-1}L^{-1},E)\cong\operatorname{Hom}(N,Rf_*(E\otimes f^{-1}L)).$$ Thus $Rf_*E\otimes L\cong
Rf_*(E\otimes f^{-1}L)$: the maps corresponding to identities under these natural bijections are
inverse. In particular, for a closed immersion $i:Z\hookrightarrow X$ the same calculation
applies to its direct image. All tensors here are derived; tensoring by a Tate line is also
termwise exact because locally it is the identity functor.

3. For a regular codimension-one closed immersion $i:Z\hookrightarrow X$ between regular
Noetherian schemes, [lem-per-regular-lci-geometric-calculus] ensures that it is a regular
immersion; the length of a local regular sequence generating the ideal at $z$ equals
$\dim\mathcal O_{X,z}-\dim\mathcal O_{Z,z}=1$, since each element of a regular sequence lowers
the local dimension by one. So [lem-per-gabber-regular-pair-purity] with $n=1,c=1$ gives
$i^!A_X\cong A_Z(-1)[-2]$, without excellence. The exceptional functor here is the right adjoint
of $i_*$ in [lem-exc-closed-support-triangle]: in [def-amb-etale-compact-support] choose the
identity open followed by the proper closed immersion, so $Ri_!=Ri_*$. By the finite exactness
and module-forgetting comparisons in step 7, $i_*$ is exact on module sheaves. Hence for every
complex $K$ and K-injective resolution $K\to I$, termwise $i_*$ keeps the acyclic cone acyclic,
so $i_*K\to i_*I$ is a quasi-isomorphism: the unbounded $Ri_*$ is termwise $i_*$ on all of
$D(Z_{\mathrm{et}},A)$, and the two right adjoints agree. For the Tate line $L=A_X(t)$, the
preceding tensor transport and the adjunction $i_*\dashv i^!$ give
$$\operatorname{Hom}(M,i^!A_X\otimes i^{-1}L)\cong\operatorname{Hom}(i_*(M\otimes
i^{-1}L^{-1}),A_X)\cong\operatorname{Hom}(i_*M,A_X\otimes L).$$ The inverse maps represented by
identities therefore give $i^!(A_X(t))\cong A_Z(t-1)[-2]$. The pullback and tensor
identifications of Tate lines are those of [lem-asd-etale-finite-twist-pullback]. For empty $Z$,
both supported terms are zero.

4. Assume the assertion of step 1 for $m-1$ and all integer twists. Write $C=C_m$,
$V=X-\bigcup_{i<m}C_i$, $U=V-C$, and use immersions $v:V\hookrightarrow X$, $b:U\hookrightarrow
V$, $a:E=C\cap V\hookrightarrow V$, $i:C\hookrightarrow X$, $k:E\hookrightarrow C$. Then $u=vb$
and $va=ik$. The schemes $V,E$ are regular Noetherian, because their local rings are those of
$X,C$. The immersion $a$ has codimension one. On $C$, the family $C\cap C_i$ for $i<m$ satisfies
the induction hypothesis: its indexed intersections are $C_{J\cup\{m\}}$, and subtracting the
dimension equality for $C$ from that for $C_{J\cup\{m\}}$ gives codimension $|J|$ in $C$. These
intersections are regular by assumption; [lem-per-regular-lci-geometric-calculus] makes their
immersions regular. They may be disconnected, which is why the induction assertion did not
require irreducibility. Thus the induction hypothesis applies both to $v$ on $X$ and to $k$ on
$C$.

5. Apply the closed-support triangle [lem-exc-closed-support-triangle] on $V$ to $K=A_V(t)$ and
to the closed/open pair $(a,b)$. Substitute the codimension-one purity calculation of step 3.
This gives the distinguished triangle $$a_*A_E(t-1)[-2]\longrightarrow A_V(t)\longrightarrow
Rb_*A_U(t)\longrightarrow a_*A_E(t-1)[-1].$$ All objects are ordinary etale $A$-module
complexes. In particular, the purity theorem is applied to the regular pair $(V,E)$, and never
to the possibly singular union of boundary components.

6. Apply $Rv_*$ to this triangle; it preserves distinguished triangles and shifts by
[lem-pc-right-derived-functor-triangulated]. The derived direct-image composition isomorphism
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition], first for $vb=u$ and then for
$va=ik$, identifies the resulting triangle as $$i_*Rk_*A_E(t-1)[-2]\longrightarrow
Rv_*A_V(t)\longrightarrow Ru_*A_U(t)\longrightarrow i_*Rk_*A_E(t-1)[-1].$$ Here $Ra_*=a_*$ and
$Ri_*=i_*$ on the bounded-below inputs by the finite exactness and module comparison of step 7.
All indexing sites are small representatives of ordinary small etale sites, and all coefficients
are the same constant ring $A$; hence the composition theorem's ringed-topos hypotheses hold.

7. Closed immersions are finite by [lem-weil-pbc-closed-immersion-finite]. For such a map,
[lemma-weil-pbc-finite-direct-image-exact] gives exact direct image on abelian sheaves;
[lem-sbc-higher-direct-image-forget-comparison] identifies the underlying abelian higher direct
images of module sheaves with those abelian higher direct images. Consequently module higher
direct images vanish in positive degrees, and direct image is exact on modules (exactness is
checked after forgetting the action). A bounded-below resolution therefore gives $Ri_*=i_*$ and
$\mathcal H^q(i_*M)=i_*\mathcal H^q(M)$. If $F$ is a constructible $A$-module sheaf on $C$,
[lem-weil-pbc-constructible-etale-module-sheaf-comparison] puts it in the source library's
constructibility notion. Its stalks are finite, since each is a finite-dimensional vector space
over finite $A$. Thus [lem-weil-pbc-finite-pushforward-finite-stalk-module], with Noetherian
target $X$, says $i_*F$ is constructible. This proves the constructibility and degree
preservation needed for the first term of step 6, and proves the identical exactness assertion
for $a$.

8. By induction, $Rv_*A_V(t)$ and $Rk_*A_E(t-1)$ have constructible cohomology in degrees
$[0,m-1]$. Hence the first term of step 6 has constructible cohomology in degrees $[2,m+1]$ by
step 7. In the cohomology sequence of that triangle [lem-sf-derived-homology-long-exact], the
segment $$\mathcal H^q(Rv_*A_V(t))\longrightarrow\mathcal H^q(Ru_*A_U(t))\longrightarrow
i_*\mathcal H^{q-1}(Rk_*A_E(t-1))$$ shows vanishing of the middle sheaf for $q>m$. Its negative
cohomology is zero by step 1. More precisely the middle sheaf is an extension of the cokernel of
the preceding arrow into $\mathcal H^q(Rv_*A_V(t))$ by the kernel of the following arrow out of
$i_*\mathcal H^{q-1}(Rk_*A_E(t-1))$. All four surrounding terms are constructible. Kernels,
cokernels and extensions are constructible by [thm-constructible-serre]. This completes the
induction. Applying it to the $r$ boundary components and $t=0$ proves the item for $A=\mathbf
F_\ell$.

9. Finally choose an $A$-basis of the finite field $B$, of dimension $d$. The underlying abelian
sheaf of $B_U$ is $A_U^{\oplus d}$. For every integer $q$,
[lem-sbc-higher-direct-image-forget-comparison], applied once for $B$ and once for $A$,
identifies the underlying abelian sheaf of $R^qj_*B_U$ with $(R^qj_*A_U)^{\oplus d}$, because
the additive derived abelian direct image preserves finite biproducts. Thus it vanishes for
$q\notin[0,r]$. For each remaining $q$, choose the finite constructible stratification supplied
by the result over $A$. On each stratum the latter finite biproduct has finite locally constant
underlying sets. Apply [lem-pod-module-local-constancy-of-finite-underlying] to the restricted
$B$-module sheaf: it is locally constant as a module sheaf, and its values are finite because
their underlying sets are finite. Therefore $R^qj_*B_U$ is constructible in the definition of
[def-weil-pbc-constructible-complexes]. The same definition gives $Rj_*B_U\in D^b_c$ with
cohomology in $[0,r]$. For $D=\varnothing$, $j$ is the identity, so this specializes to $B_Y$ in
degree zero, including the empty ambient scheme. -/
theorem regular_normal_crossings_constant_image
    (ell : ℕ) [Fact ell.Prime] (B : Type (u + 1)) [Field B] [Finite B] [CharP B ell]
    {Y : Scheme.{u}} [IsNoetherian Y] (_hY : IsRegularScheme Y)
    (_hell : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (D : Y.IdealSheafData) (_hD : IsStrictNormalCrossingsBoundary D) :
    (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
        (normalCrossingsConstantDirectImage B D))) ∧
    (∀ q : ℤ, (Nat.card ↥(irreducibleComponents D.subscheme) : ℤ) < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
        (normalCrossingsConstantDirectImage B D))) ∧
    DerivedCategory.isBoundedConstructible B Y (normalCrossingsConstantDirectImage B D) := by
  sorry

end AlgebraicGeometry.Etale
