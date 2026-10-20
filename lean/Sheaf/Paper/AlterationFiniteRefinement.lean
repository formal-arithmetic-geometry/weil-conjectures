/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Gluing
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentCoproduct
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.ReducedSourceFactors
import WeilConjectures.Blowup.Proper
import WeilConjectures.Compactification.StrictTransform
import WeilConjectures.Blowup.Principalization
import Sheaf.Compactification.NagataSketchClosure
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.FiniteAfterBlowup
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite refinement of an alteration

Source: Orgogozo, Modifications et cycles proches sur une base générale,
Lemma 2.5, p. 4 (blueprint: lem-trf-alteration-finite-refinement).

The refinement uses the recorded modification and alteration predicates. When the base is
integral, the same witnesses satisfy the additional reducedness and integrality clauses.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Orgogozo

/-- An alteration of reduced Noetherian schemes becomes finite and surjective after
modifications of its source and target. When the base is integral the two new schemes can
be chosen reduced, and the new base integral if the original source is integral.
Source: Orgogozo, Lemma 2.5, p. 4; the node's strict-transform and componentwise refinement.
(blueprint: lem-trf-alteration-finite-refinement)

Proof, following the ten steps of the DAG node:
1. Suppose first that $S$ is integral. The alteration definition [def-trf-orgogozo-induction-data]
   gives properness, surjectivity and a dense open over which $a$ is finite. Properness gives
   finite type [def-weil-proper-morphism]. Apply [lem-sbc-generic-flat-finite-presentation] on the
   integral base and intersect its nonempty open with the finite locus; take a nonempty affine
   open $U$ in that intersection. Then $a_U$ is finite, flat and locally of finite presentation,
   hence finite locally free [def-pc-finite-locally-free]. The Noetherian base is quasi-compact
   and quasi-separated (every open and every intersection of affine opens is quasi-compact), so
   [lem-trf-finite-after-blowup] applies. Obtain a $U$-admissible blow-up $v:S'\to S$ and a finite
   locally free strict transform $p:\widetilde T\to S'$. Let $u:\widetilde T\to T$ be the other
   projection. The fibre-product identity is $a u=v p$.
2. Write $\mathcal I$ for the admissible ideal and $W=S\setminus V(\mathcal I)$; then $U\subseteq
   W$ [def-nagata-admissible-blowup]. On an affine integral open $\operatorname{Spec}A\subseteq
   S$, the blow-up is covered by $\operatorname{Spec}A[I/f]$ for generators $f$ of $I$, by [prop-
   nagata-affine-blowup-chart-cover] and the local gluing construction [def-nagata-global-blowup-
   glue-data]. A chart with $f=0$ is empty. For $f\ne0$, its ring is the subalgebra
   $A[I/f]\subseteq A_f$ [def-nagata-blowup-chart-ring], hence a domain; the chart contains the
   lift of the generic point of $S$. Thus all nonempty charts have that common generic point, so
   $S'$ is irreducible and reduced, and is nonempty since it contains $U$. This proves that $S'$
   is integral [def-pc-integral-scheme], without assuming that $T$ is integral. The identification
   over $W$ supplied by [lemma-nagata-strict-transform-over-complement] (apply it also with
   $Y=X=S$) identifies $v^{-1}(U)$ with $U$. It is now a nonempty open of an integral scheme, so
   it is dense. Properness of $v$ follows from [lemma-nagata-blowup-proper]; hence $v$ is a
   modification.
3. By [lemma-nagata-strict-transform-over-complement], the open of $\widetilde T$ lying over $W$
   is $T_W$ and $u$ is the identity under this identification. By [lemma-nagata-strict-transform-
   closure-characterization], $\widetilde T$ is the scheme-theoretic closure of this open inside
   $T\times_S S'$. Thus it is closed there. The projection $T\times_S S'\to T$ is proper by [lem-
   pc-proper-base-change] applied to $v$; [lem-weil-pbc-closed-immersion-proper] makes $u$ proper.
   The closure theorem [sk-lem-nagata-sketch-closure] applies to the open immersion
   $T_W\hookrightarrow T\times_S S'$: the ambient scheme is Noetherian (the blow-up is of finite
   type and $T$ is Noetherian), so the immersion is quasi-compact and the ambient is quasi-
   separated. It gives an injection $\mathcal O_{\widetilde T}\hookrightarrow j_*\mathcal
   O_{T_W}$. Every nonempty open of $\widetilde T$ therefore meets $T_W$: otherwise its section
   ring injects into zero and that open is empty. Moreover $T_W$ is reduced since $T$ is reduced,
   so the same injection kills every nilpotent section. Consequently $\widetilde T$ is reduced
   [def-pc-reduced-scheme].
4. Every irreducible component of $T$ dominates $S$ by [def-trf-orgogozo-induction-data].
   Therefore its generic point maps to the generic point of $S$ and lies in $T_U$; hence $T_U$ is
   dense in $T$, and also dense in $T_W$. Since $T_W$ is dense in $\widetilde T$ and $T_U$
   identifies with its restriction over $U$, the inverse image $u^{-1}(T_U)$ is dense in
   $\widetilde T$. Together with properness and the isomorphism over $T_U$, this proves that $u$
   is a modification. The map $p$ is finite [def-pc-finite-locally-free], hence proper [lem-weil-
   pbc-finite-proper] and closed [def-weil-proper-morphism]. Its image contains $v^{-1}(U)$
   because there it is the surjective map $T_U\to U$. That open is dense in $S'$, so the closed
   image is all of $S'$. This proves the integral-base case, including both reducedness
   conclusions. Record also the following feature of this construction: for any nonempty open
   $V\subseteq U$, the same domination argument makes $T_V$ dense in $T_W$, hence its lift is
   dense in $\widetilde T$; and $v^{-1}(V)$ is dense in the integral $S'$. This permits later
   shrinking of $U$.
5. Now let $S$ be any nonempty reduced Noetherian scheme. By [lem-weil-pbc-noetherian-finitely-
   many-components], enumerate its components $S_1,\ldots,S_n$, and the components
   $C_1,\ldots,C_m$ of $T$. Give each component its reduced closed subscheme structure using [lem-
   weil-pbc-reduced-induced-closed-subscheme]; each $S_i$ is integral [def-pc-integral-scheme].
   The alteration domination clause assigns each $C_j$ to the unique component $S_{i(j)}$ it
   dominates. Properness implies that $a(C_j)$ is closed, hence it equals $S_{i(j)}$ [def-weil-
   proper-morphism]. Surjectivity and finiteness of the component covers imply that every $S_i$
   occurs: if it did not, its generic point would lie in another component. Let $T_i$ be the
   reduced induced closed subscheme on $\bigcup_{i(j)=i}C_j\subseteq T$. This is a finite closed
   union. The same reduced-source factorization lemma [lem-weil-pbc-reduced-source-factors-
   through-closed-subscheme] gives a morphism $a_i:T_i\to S_i$ satisfying $a j_i=\iota_i a_i$,
   where $j_i:T_i\hookrightarrow T$ and $\iota_i:S_i\hookrightarrow S$.
6. Each $a_i$ is an alteration of reduced Noetherian schemes with integral base. To check
   properness, the factor map $T_i\to T\times_S S_i$ is a closed immersion: it is the base change
   of $j_i$ along $T\times_S S_i\to T$, since $T_i\times_S S_i\cong T_i$ (a morphism factoring
   through a closed immersion has this pullback). Use [lem-pc-closed-imm-base-change], then [lem-
   pc-proper-base-change] for $a$, and [lem-weil-pbc-closed-immersion-proper] for the composite.
   Surjectivity follows from $a(C_j)=S_i$ for every component in this nonempty group. Its
   components are exactly these $C_j$, and all dominate $S_i$. If $F\subseteq S$ is the original
   dense finite locus, then $F\cap S_i$ contains the generic point of $S_i$. Over it the displayed
   closed immersion embeds $T_i|_F$ into the base change of the finite $T_F\to F$. This restricted
   map is finite: on an affine open its algebra is a quotient of a finite module algebra, hence
   finite [def-weil-finite-integral-morphism]. Thus every hypothesis used in the integral
   construction is satisfied by $a_i$.
7. The intermediate component-separation square has vertical arrows $\coprod_i
   a_i:\coprod_iT_i\to\coprod_iS_i$ and $a:T\to S$, and horizontal arrows $q=\coprod_i j_i$ and
   $r=\coprod_i\iota_i$; it commutes because $a j_i=\iota_i a_i$. These coproducts exist by [lem-
   weil-pbc-scheme-coproduct-family]. Both $q$ and $r$ are finite: on an affine open their inverse
   images have rings $\prod_i A/I_i$, finite modules over $A$ [def-weil-finite-integral-morphism].
   Put $W=S\setminus\bigcup_{i\ne k}(S_i\cap S_k)$. This dense open is the disjoint union of the
   component opens $W_i$. Over $W$, $r$ is an isomorphism, and over $T_W$ so is $q$: $T_i|_{W_i}$
   is the full reduced open $T|_{W_i}$, while every other summand is empty. The equality of
   reduced structures follows from uniqueness in [lem-weil-pbc-reduced-induced-closed-subscheme].
   Domination ensures that $T_W$ is dense in $T$, and $T_i|_{W_i}$ is dense in $T_i$. Likewise
   $W_i$ is dense in $S_i$. Since finite maps are proper [lem-weil-pbc-finite-proper], $q$ and $r$
   are modifications. In particular the reduction is on the full $S_i$ and $T_i$, not on the open
   strata $W_i$.
8. Apply the integral-base construction of steps 1--4 to each full morphism $a_i:T_i\to S_i$.
   Obtain $u_i:\widetilde T_i\to T_i$, $v_i:S'_i\to S_i$, and finite surjective $p_i:\widetilde
   T_i\to S'_i$ with $a_i u_i=v_i p_i$. Keep the nonempty open $U_i\subseteq S_i$ chosen there:
   $v_i$ is an isomorphism over $U_i$, $u_i$ over $a_i^{-1}(U_i)$, and both lifted opens remain
   dense after any nonempty open shrink of $U_i$ by step 4. Set $S'=\coprod_i S'_i$, $\widetilde
   T=\coprod_i\widetilde T_i$, $p=\coprod_i p_i$, $v|_{S'_i}=\iota_i v_i$, and $u|_{\widetilde
   T_i}=j_i u_i$. These maps exist uniquely by [lem-weil-pbc-scheme-coproduct-family]. On each
   summand, $a u=a j_i u_i=\iota_i a_i u_i=\iota_i v_i p_i=v p$. The map $p$ is finite and
   surjective: this is checked on the open-and-closed target summands $S'_i$, where it is exactly
   $p_i$ [def-weil-finite-integral-morphism].
9. The maps $\coprod_i u_i$ and $\coprod_i v_i$ are proper. Indeed their restrictions to the open-
   and-closed target summands are the given proper maps: after any base change the image of a
   closed set is closed on each summand, finite type is checked by the affine-open definition, and
   the diagonal has the given closed diagonals as its diagonal blocks and empty off-diagonal
   blocks [def-weil-proper-morphism]. This directly checks all three defining conditions. Since
   $u=q(\coprod_i u_i)$ and $v=r(\coprod_i v_i)$, the proper-composition theorem [lem-weil-pbc-
   proper-composition] gives properness of $u$ and $v$.
10. Apply [lem-weil-pbc-dense-open-component-coproduct] to the full component inclusions
   $S_i\hookrightarrow S$ and the dense opens $U_i$. It supplies a dense open $V\subseteq S$ over
   which $r$ is an isomorphism and whose restriction to each $S_i$ is contained in $U_i$. Replace
   $V$ by $V\cap W$, with $W$ as in step 7. It still contains every component generic point. Over
   $V$, the maps $v_i$ identify $S'|_V$ with $\coprod_i(S_i\cap V)=V$. The maps $u_i$ identify
   $\widetilde T|_V$ with $\coprod_i T_i|_V=T|_V$. Thus $v$ and $u$ are isomorphisms over $V$ and
   $T_V$, respectively. Domination makes $T_V$ dense in $T$. Each nonempty $V\cap S_i$ is an open
   shrink of $U_i$; the density property from step 4 makes its inverse image dense in both $S'_i$
   and $\widetilde T_i$. Therefore the inverse images of $V$ and $T_V$ are dense in $S'$ and
   $\widetilde T$. Along with step 9 this proves that $u,v$ are modifications [def-trf-orgogozo-
   induction-data]. If $S=\varnothing$, then $T=\varnothing$; take the two empty schemes and
   identity maps. This handles the empty case as well and completes the unchanged statement. -/
theorem exists_finite_surjective_refinement
    {T S : Scheme.{u}} [IsReduced T] [IsReduced S] [IsNoetherian T] [IsNoetherian S]
    (a : T ⟶ S) (ha : IsAlteration a) :
    ∃ (T' S' : Scheme.{u}) (u : T' ⟶ T) (v : S' ⟶ S) (p : T' ⟶ S'),
      IsModification u ∧ IsModification v ∧ IsFinite p ∧ Surjective p ∧
      u ≫ a = p ≫ v ∧
      (IsIntegral S → IsReduced S' ∧ IsReduced T' ∧ (IsIntegral T → IsIntegral S')) := by
  sorry

end AlgebraicGeometry.Orgogozo
