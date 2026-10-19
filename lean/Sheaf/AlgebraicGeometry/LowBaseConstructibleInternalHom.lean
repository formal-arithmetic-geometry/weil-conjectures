/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Ring.ULift
import Sheaf.AlgebraicGeometry.EtaleInternalHomLocalization
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.Paper.SfHomTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Constructible internal Hom over a regular base of dimension at most one

Source: Zheng, Six operations and Lefschetz-Verdier formula for Deligne-Mumford stacks,
Propositions 3.14-3.16, especially the regular-base alternative of Proposition 3.15;
ILO, Expose XIII, Theorem 2.3.1(i)
(blueprint: lem-per-low-base-constructible-internal-hom).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

/-- For a separated finite-type scheme over a Noetherian regular base of dimension at
most one, derived internal Hom preserves bounded constructible finite-field complexes.
The coefficients are the universe lift of F_ell; no dualizing object or purity is assumed.
Source: Zheng, Propositions 3.14-3.16; ILO XIII, Theorem 2.3.1(i)
(blueprint: lem-per-low-base-constructible-internal-hom).

Proof (the node's seven-step Noetherian devissage):
1. First record closure under finite derived constructions. By [thm-constructible-serre],
constructible $A$-module sheaves are closed under kernels, cokernels and extensions. Applying
[lem-sbc-cohomology-in-weak-serre-subcategory] to this subcategory shows that $D^b_c$ is
triangulated. By [lem-weil-pbc-finite-type-over-noetherian], $X$ is Noetherian. We prove the
assertion simultaneously for all closed subschemes $T\hookrightarrow X$, by induction on their
underlying closed subsets: the induction claim at a closed subset quantifies over all closed
subschemes with that support, including thickenings. The empty case is zero. Quotients of
Noetherian rings are Noetherian, and generators for a finite-type algebra still generate its
quotients; hence these closed subschemes are again Noetherian and of finite type over the same
$S$. Their diagonals are restrictions of the closed diagonal of $X/S$, so they remain separated.
Fix such a nonempty $T$, assume the assertion for every proper closed support, and fix $M,N\in
D^b_c(T_{\mathrm{et}},A)$.

2. For any open immersion $v:W\hookrightarrow T$, the input
[lem-per-low-base-open-sheaf-finiteness] gives $Rv_*F\in D^b_c(T,A)$ for every constructible
sheaf $F$ in degree zero. This extends to every $L\in D^b_c(W,A)$: its finitely many truncation
triangles [lem-weil-pbc-truncation-triangle] express it as successive extensions of $H^q(L)[-q]$.
Module-sheaf categories have enough injectives by
[lem-weil-pbc-module-sheaves-enough-injectives], so
[lem-weil-pbc-derived-direct-image-triangulated] applies to their additive left exact direct
image. Apply $Rv_*$ to those finitely many triangles and use Step 1. Only finitely many
sheaf-dependent bounds occur, so taking their maximum after shifts gives a finite bound. This
step does not require a uniform cohomological-dimension estimate for all sheaves.

3. There are finitely many nonzero $H^q(M)$. Apply [prop-constructible-generic-constancy] to each
and intersect the finitely many dense opens, obtaining a dense open $j:U\hookrightarrow T$ on
which every $H^q(M)$ is finite locally constant. The intersection is dense since $T$ is
Noetherian and each open contains every generic point of its finitely many irreducible
components. Let $i:Z\hookrightarrow T$ be the reduced closed complement; its support is proper.
By [prop-weil-pbc-inverse-image-modules-exact], restriction commutes with cohomology, and
[prop-constructible-pullback] preserves constructibility. Thus $j^*M,j^*N,i^*M$ are bounded
constructible, with the stated locally constant cohomology for $j^*M$.

4. Here is the local calculation on $U$. If $F$ is a finite locally constant $A$-module sheaf and
$G$ a constructible one, then on an etale cover trivializing $F$ it is $A^{\oplus r}$, since $A$
is a field. By [def-pur-derived-internal-hom] the Hom complex from $A^{\oplus r}[0]$ into a
K-injective representative of $G[0]$ is that representative to the finite power $r$; its only
cohomology is $G^{\oplus r}$ in degree zero. Restriction of derived Hom to these slice sites
agrees with derived Hom there by [lem-weil-pbc-ringed-internal-hom-exact-restriction]. Thus all
higher internal Ext vanish, and the degree-zero Hom is constructible: on a common stratification
trivializing $G$, further etale covers trivialize both sheaves and their Hom is a
finite-dimensional constant vector space. Descending these local identifications is exactly
finite local constancy on each stratum.

5. Apply the finite truncation triangles [lem-weil-pbc-truncation-triangle] first to $j^*N$ and
then to $j^*M$. The distinguished-triangle assertions of [lem-sf-hom-triangulated] and Step 4
express $B=R\mathcal Hom_A(j^*M,j^*N)$ as finitely many extensions of bounded constructible
objects. Explicitly, if $M$ has cohomology in $[a,b]$ and $N$ in $[c,d]$, the building block
$R\mathcal Hom_A(H^q(j^*M)[-q],H^r(j^*N)[-r])$ has its only cohomology in degree $r-q$; hence all
blocks lie in $[c-b,d-a]$. The long exact cohomology sequence and the Serre property from Step 1
give constructibility and the same finite bound for $B$. Step 2 then gives $Rj_*B\in D^b_c(T,A)$.

6. Apply [lem-per-etale-internal-hom-localization] with first argument $A_T[0]$ and second
argument $N$. The identity $R\mathcal Hom_A(A_W,L)=L$, computed directly from
[def-pur-derived-internal-hom], for $W=T,U,Z$, identifies its triangle with
$$i_*Ri^!N\longrightarrow N\longrightarrow Rj_*j^*N\longrightarrow(i_*Ri^!N)[1].$$ Both middle
and right terms are bounded constructible by Step 2, so Step 1 gives $i_*Ri^!N\in D^b_c(T,A)$.
The counit $i^*i_*\cong1$ of [prop-openclosed-lowerstar-fully-faithful] is module-linear by
naturality with respect to the $A$-actions, and applies termwise. Exactness of $i^*$
[prop-weil-pbc-inverse-image-modules-exact] and constructible pullback
[prop-constructible-pullback] therefore imply $Ri^!N\cong i^*i_*Ri^!N\in D^b_c(Z,A)$. This proves
the needed exceptional-restriction finiteness from open direct-image finiteness; no purity
theorem is invoked.

7. Since $Z$ has proper closed support, the simultaneous induction hypothesis applies to $i^*M$
and $Ri^!N$ on $Z$, giving $C=R\mathcal Hom_A(i^*M,Ri^!N)\in D^b_c(Z,A)$. The exactness of closed
direct image is part of [lem-per-etale-internal-hom-localization]. Its preservation of
constructible cohomology follows from [lem-weil-pbc-finite-pushforward-constructible-noetherian],
applied to the finite closed immersion; the underlying finite sheaves and their $A$-actions give
precisely the constant-$A$ constructibility condition. Thus $i_*C$ is bounded constructible.
Apply [lem-per-etale-internal-hom-localization] now with first argument $M$ and second argument
$N$: $$i_*C\longrightarrow R\mathcal Hom_A(M,N)\longrightarrow Rj_*B\longrightarrow(i_*C)[1].$$
Step 5 gives the right term, and Step 1 gives bounded constructibility of the middle term. This
completes the Noetherian induction, including $T=X$, and proves the exact item statement. -/
theorem isBoundedConstructible_derivedHom_of_regular_base
    {S X : Scheme.{u}} [IsNoetherian S] (_hS : IsRegularScheme S)
    (_hdim : topologicalKrullDim S ≤ 1)
    (ell : ℕ) [Fact ell.Prime]
    (_hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s))
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (M N : DerivedCategoryModule (ULift.{u + 1} (ZMod ell)) X)
    (_hM : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ell)) X M)
    (_hN : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ell)) X N) :
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ell)) X
      (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) X).obj (op M)).obj N) := by
  sorry

end AlgebraicGeometry.Etale
