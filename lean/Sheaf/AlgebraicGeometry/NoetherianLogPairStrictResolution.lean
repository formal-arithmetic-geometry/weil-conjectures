/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.MonoidalResolutionTower
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.LogBlowupNormalization
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.AlgebraicGeometry.NCMaximalBranchBlowup
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.PermissibleBoundaryPreservation
import WeilConjectures.Compactification.StrictTransform
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Mathlib.RingTheory.LocalRing.Module

/-!
# Strict boundary resolution of excellent Noetherian log regular pairs

Source: ILO, Travaux de Gabber, VII Theorem 4.3, VIII 4.1.2--4.1.8 and
Remark 4.2.2(i), and IX 2.4 (blueprint: lem-per-noetherian-log-pair-strict-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- An integral excellent Noetherian log regular pair has a proper birational regular
resolution with a strict normal crossings boundary containing the inverse image of the
closed subset. The component equations are actual sections on an affine neighbourhood;
their germs form a sublist of a regular system of parameters. The empty product is one.

Source: ILO VII Theorem 4.3, VIII 4.1.2--4.1.8 and Remark 4.2.2(i), IX 2.4
(blueprint: lem-per-noetherian-log-pair-strict-resolution).

Proof:
1. Put $U=M\setminus B$. It is a nonempty dense open since $M$ is integral and $B$ is nowhere
   dense. Give $M$ its divisorial fs log structure $\mathcal L$ from [def-trf-log-regular-pair];
   its triviality locus is exactly $U$, and its log-regularity condition is the one in
   [def-trf-fs-log-blowup]. At a geometric point the characteristic monoid $P=\overline{\mathcal
   L}$ is sharp and saturated. Its group completion is torsion free: if $ng=0$, saturation puts
   both $g$ and $-g$ in $P$, so $g$ is a unit, hence zero by sharpness. The Noetherian scheme
   $M$ is quasi-compact and locally Noetherian. Thus [lem-trf-monoidal-resolution-tower] gives a
   finite saturated log blowup tower $(X_n,\mathcal L_n)\to\cdots\to(X_0,\mathcal
   L_0)=(M,\mathcal L)$ along nonempty coherent log ideals, with free final characteristic
   monoids. Write $b_i:X_{i+1}\to X_i$ for the underlying maps.
2. We will use the following chart observation at both stages. The blowup of a nonzero
   finite-type ideal $J$ on an integral scheme $X$ is integral. On an affine domain $A$,
   [prop-nagata-affine-blowup-chart-cover] gives the nonempty charts $\operatorname{Spec}A[J/a]$
   for nonzero generators $a$. By [def-nagata-blowup-chart-ring], these are domains inside the
   same function field, each containing its generic point. The charts cover and share that
   point; the same is true across affine opens of $X$. Their union is reduced and irreducible,
   hence integral. Its normalization is integral as well: by [def-sc-normalization] its affine
   rings are integral closures of domains inside that same field, hence domains, again with a
   common generic point. A nonempty open on which the blowup or normalized blowup is an
   isomorphism is therefore dense in its source.
3. Induct on $i$ with invariant: $X_i$ is integral excellent Noetherian, $(X_i,\mathcal L_i)$ is
   log regular, and its triviality locus $U_i$ is the inverse image of $U$ and maps
   isomorphically to $U$. The case $i=0$ is the hypothesis and Step 1. Given the invariant at
   $i$, [lem-trf-log-blowup-normalization] identifies $X_{i+1}$ with the normalization of
   $Y_i=\operatorname{Bl}_{J_i}X_i$, where $J_i$ is nonzero finite-type quasi-coherent; it gives
   log regularity and $U_{i+1}=b_i^{-1}U_i\cong U_i$. Step 2 makes both $Y_i$ and $X_{i+1}$
   integral. By [lemma-nagata-blowup-proper], $Y_i\to X_i$ is proper, hence finite type by
   [def-weil-proper-morphism]; [lem-weil-pbc-finite-type-over-noetherian] makes $Y_i$
   Noetherian.
4. Over an excellent affine open $\operatorname{Spec}A\subset X_i$, the finite-type definition
   [def-weil-finite-type-morphism] covers $Y_i$ by affine spectra of finite-type $A$-algebras.
   These rings are excellent by [lem-exc-finite-type-localization-excellent]. The affine-cover
   criterion [lem-trf-excellent-scheme-affine-cover] therefore makes $Y_i$ excellent. Apply
   [lem-per-excellent-normalization-preparation] to the integral, hence reduced, excellent
   Noetherian scheme $Y_i$. On an integral scheme its componentwise normalization is precisely
   normalization in its one function field, as in Step 2. Thus $X_{i+1}\to Y_i$ is finite and
   $X_{i+1}$ is excellent Noetherian. It is proper by [lem-weil-pbc-finite-proper], so
   [lem-weil-pbc-proper-composition] makes $b_i$ proper. This closes the induction of Step 3,
   including all the excellence hypotheses needed at the next stage.
5. Put $V=X_n$ and let $p:V\to M$ be the composite tower. Repeated application of
   [lem-weil-pbc-proper-composition] makes $p$ proper; for a zero-length tower the identity is
   proper directly from [def-weil-proper-morphism]. The invariant gives $p^{-1}U\cong U$. By
   Step 1 the final characteristic monoids are free, so
   [lem-trf-free-characteristic-regular-boundary] makes $V$ regular and its reduced
   nontriviality locus $Z$ an effective Cartier normal crossings divisor. It also makes
   $p^{-1}U$ dense. Since the triviality locus is exactly $p^{-1}U$, the support of $Z$ is
   $p^{-1}B$. The scheme $V$ is integral excellent Noetherian by Steps 3--4. This proves the
   regular, possibly non-strict normal crossings stage without applying the existing
   finite-type-over-a-field resolution lemma.
6. Set $V_0=V$, $B_0=D_0=Z$, $H_0=\varnothing$, and $q_0=1_V$. We now maintain: $V_j$ is
   integral regular Noetherian; $q_j:V_j\to V$ is proper and isomorphic over $V\setminus |Z|$;
   $B_j=(q_j^{-1}Z)_{\rm red}$ is normal crossings; $D_j$ is the remaining strict transform of
   $Z$ and a reduced union of components of $B_j$; $H_j$ is a strict normal crossings union of
   components of $B_j$; and $B_j=D_j\cup H_j$. These hold at $j=0$, with the empty boundary
   understood as the unit ideal. If $D_j$ is empty we stop. Otherwise
   [lem-trf-nc-maximal-branch-blowup] supplies a finite maximum branch number $m_j\ge1$ and its
   reduced regular closed locus $C_j$, with $C_j\subset D_j\subset B_j$ and, etale locally,
   $C_j=V(t_1,\ldots,t_{m_j})$, $D_j=V(t_1\cdots t_{m_j})$ in boundary parameters for $B_j$.
7. Blow up $C_j$: let $c_j:V_{j+1}\to V_j$ and $q_{j+1}=q_jc_j$. Its center ideal is finite type
   since $V_j$ is Noetherian, and is nonzero because it is the unit ideal on the nonempty open
   identified with $U$. By [lemma-nagata-blowup-proper], $c_j$ is proper. It is an isomorphism
   off $C_j$ by [thm-nagata-global-blowup-complement], hence over that open. Step 2 makes
   $V_{j+1}$ integral. Properness implies finite type [def-weil-proper-morphism], and
   [lem-weil-pbc-finite-type-over-noetherian] makes $V_{j+1}$ Noetherian.
   [lem-weil-pbc-proper-composition] makes $q_{j+1}$ proper. Thus the scheme, properness, and
   preserved-open parts of the invariant hold at the next stage.
8. The center supplied in Step 6 is regular and is generated by a nonempty subset of the
   boundary parameters, exactly the center hypothesis of
   [lem-trf-permissible-boundary-preservation]. Apply it to $(V_j,B_j,H_j,C_j)$. It gives
   regular $V_{j+1}$, normal crossings $B_{j+1}=(c_j^{-1}B_j)_{\rm red}$, and strict normal
   crossings $H_{j+1}=(c_j^{-1}(H_j\cup C_j))_{\rm red}$, a union of components of $B_{j+1}$.
   With $E_{j+1}=(c_j^{-1}C_j)_{\rm red}$ it also gives $B_{j+1}=B_j^{\rm st}\cup E_{j+1}$ and
   $H_{j+1}=H_j^{\rm st}\cup E_{j+1}$. Meanwhile [lem-trf-nc-maximal-branch-blowup] gives that
   $D_{j+1}=D_j^{\rm st}$ is normal crossings or empty, and every one of its branch numbers is
   at most $m_j-1$.
9. The boundary identities also give $B_{j+1}=D_{j+1}\cup H_{j+1}$. Indeed strict transform is
   the scheme-theoretic closure away from the center [def-nagata-strict-transform]. Closure
   commutes with a finite scheme-theoretic union: on an affine chart its defining ideal is the
   kernel of restriction, and the kernel for a union is the intersection of the two kernels.
   Hence $B_j^{\rm st}=D_j^{\rm st}\cup H_j^{\rm st}$. Substitute the identities in Step 8.
   Reduction does not alter supports [def-weil-pbc-scheme-reduction], so $B_{j+1}$ is also
   $(q_{j+1}^{-1}Z)_{\rm red}$. Since $D_{j+1}$ is normal crossings or empty and contained in
   $B_{j+1}$, its branches are a subset of the branches of $B_{j+1}$; thus it is again a reduced
   union of components. This completes the boundary part of the induction.
10. If $Z$ is empty, take no blowups. Otherwise the positive integers $m_j$ strictly decrease
   whenever $D_j$ remains nonempty, by Step 8. Thus after at most $m_0$ steps $D_N=\varnothing$
   and $B_N=H_N$. This includes $m_j=1$: the center is then all of $D_j$, possibly a Cartier
   center with identity blowup, but its strict transform is empty since $D_j\setminus
   C_j=\varnothing$. Put $R=V_N$, $q=q_N$ and $A=B_N=H_N$. By the invariant, $R$ is integral
   regular Noetherian, $q$ is proper and isomorphic over $V\setminus|Z|$, and $A$ is a strict
   normal crossings boundary with $|A|=q^{-1}|Z|$. The latter assertion has exactly the
   regular-component and intersection meaning of [def-trf-strict-normal-crossings-boundary],
   supplied at every nonempty stage by [lem-trf-permissible-boundary-preservation].
11. We spell out the parameter clause, without interpreting etale normal crossings as strict
   normal crossings. At $x\in R$, discard the finitely many components of $A$ not containing
   $x$. In the regular local ring $(S,\mathfrak m)=\mathcal O_{R,x}$ of dimension $d$, let
   $I_1,\ldots,I_s$ be the ideals of the remaining distinct components.
   [def-trf-strict-normal-crossings-boundary] gives that every $S/I_J$ for $I_J=\sum_{a\in
   J}I_a$ is regular local of dimension $d-|J|$. By
   [lem-weil-pbc-regular-local-quotient-independent-generators], $I_a$ has generators with
   independent images in $\mathfrak m/\mathfrak m^2$. Its image there has dimension one: the
   quotient is the cotangent space of $S/I_a$, whose dimension is $d-1$, whereas that of $S$ is
   $d$, by [lem-weil-pbc-regular-local-cotangent-dimension]. Thus this independent generating
   set has exactly one member, say $I_a=(t_a)$.
12. For $I=I_1+\cdots+I_s$, the same quotient-cotangent calculation gives
   $\dim_\kappa((I+\mathfrak m^2)/\mathfrak m^2)=d-(d-s)=s$. This space is spanned by the $s$
   classes of $t_1,\ldots,t_s$, so they are independent. Extend them to a basis of $\mathfrak
   m/\mathfrak m^2$ and lift the additional basis vectors to $\mathfrak m$. Nakayama in the
   generator form [lem-weil-pbc-nakayama-local-generators], applied to the finitely generated
   $S$-module $\mathfrak m$, says that the resulting $d$ elements generate $\mathfrak m$. Thus
   they are a regular system of parameters [def-weil-pbc-regular-system-of-parameters]. By
   [lem-trf-regular-local-ufd-boundary-factorization] the $t_a$ are pairwise nonassociate prime
   elements. Their principal ideals therefore have intersection $(t_1\cdots t_s)$: divisibility
   by each distinct prime implies divisibility by their product. The reduced union of the
   components has this ideal. Represent these finitely many germs on a common neighbourhood of
   $x$; equality of their finitely generated ideal stalks persists after shrinking. The
   component equations and product equation follow there. For $s=0$ the product is $1$ and the
   boundary is empty near $x$.
13. Finally take $e=pq:R\to M$. It is proper by [lem-weil-pbc-proper-composition]. The nonempty
   open $e^{-1}U$ is isomorphic to $U$ by the two preserved-open constructions, and is dense in
   the integral $R$; $U$ is dense in $M$. Thus $e$ is birational with precisely the dense-open
   meaning in the statement. From Step 5 and the boundary recurrence,
   $e^{-1}B=q^{-1}p^{-1}B=q^{-1}|Z|=|A|$ as closed supports, which in particular proves the
   requested containment. Regularity, integrality and Noetherianity were proved in the
   induction, and Steps 11--12 give every local parameter clause. If $B$ is empty all
   conclusions still apply, with $A$ empty.
-/
theorem exists_noetherian_log_pair_strict_resolution
    (M : Scheme.{u}) [IsIntegral M] [IsNoetherian M]
    (hexc : ∀ V : M.affineOpens, IsExcellent Γ(M, V))
    (B : Closeds M) (hB : DenseRange (Scheme.Opens.ι (X := M) B.compl))
    (hlog : IsDivisorialFineSaturatedLogRegularPair M (Scheme.Opens.toScheme (X := M) B.compl)
      (Scheme.Opens.ι (X := M) B.compl) hB) :
    ∃ (R : Scheme.{u}) (e : R ⟶ M) (A : R.IdealSheafData),
      IsIntegral R ∧ IsNoetherian R ∧ IsRegularScheme R ∧ IsProper e ∧
      (∃ V : M.Opens, Dense (V : Set M) ∧
        Dense ((e ⁻¹ᵁ V) : Set R) ∧ IsIso (e ∣_ V)) ∧
      IsStrictNormalCrossingsBoundary A ∧ e ⁻¹' (B : Set M) ⊆ A.support ∧
      ∀ x : R, ∃ (W : R.affineOpens) (hx : x ∈ W.1)
        (s : ℕ) (C : Fin s → Closeds R) (t : Fin s → Γ(R, W))
        (hN : IsNoetherianRing (R.presheaf.stalk x)) (p : List (R.presheaf.stalk x)),
        Function.Injective C ∧
        Set.range (fun i ↦ (C i : Set R)) =
          {Z | Z ∈ Set.image (Set.image Subtype.val)
            (irreducibleComponents (A.support : Set R)) ∧ x ∈ Z} ∧
        (∀ i, (Scheme.IdealSheafData.vanishingIdeal (C i)).ideal W =
          Ideal.span {t i}) ∧
        (List.ofFn (fun i ↦ R.presheaf.germ W.1 x hx (t i))).Sublist p ∧
        @IsLocalRing.IsRegularSystemOfParameters (R.presheaf.stalk x) _ _ hN p ∧
        A.ideal W = Ideal.span {∏ i, t i} := by
  sorry

end AlgebraicGeometry
