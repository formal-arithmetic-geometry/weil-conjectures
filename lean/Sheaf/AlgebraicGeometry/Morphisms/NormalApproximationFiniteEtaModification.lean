/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.Morphisms.NormalFiniteStageDiagram
import Sheaf.AlgebraicGeometry.Morphisms.DominantFiniteRefinementLimit
import Sheaf.AlgebraicGeometry.DescendFlatFinitePresentation
import Sheaf.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Sheaf.RingTheory.SmoothNormalRing
import Sheaf.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection
import Sheaf.RingTheory.SerreCriterionReduced
import Sheaf.RingTheory.FlatLocalDepthFormula
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import Sheaf.TraceFormula.GenericFibrePointsSmooth
import Sheaf.TraceFormula.GeometricallyReducedFibresLimitDescent

/-!
# Normal Noetherian approximation of a finite generic modification

Source: Temkin, Stable modification of relative curves, Proposition 3.5.2, printed p. 20,
and §3.1, Remark 3.1.1(i)
(blueprint: lem-trf-normal-approximation-finite-eta-modification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A finite generic modification of a flat finitely presented family with reduced geometric
fibres over a normal integral affine base has a compatible model over a normal integral
Noetherian affine base. The modification and schematic-density clauses are expanded on
both sides; the source of the modification has its induced structure map `f ≫ p`.

Source: Temkin, Proposition 3.5.2, printed p. 20, noetherian-reduction paragraph, and §3.1,
Remark 3.1.1(i) (blueprint: lem-trf-normal-approximation-finite-eta-modification).

Proof plan (the DAG proof, including the finite-algebra argument that avoids assuming
finite presentation of the given finite morphism):
1. Choose the affine Noetherian approximation $N$ of $S$ from
[lemma-nagata-noetherian-inverse-system-affine]. Apply [lem-sbc-normal-finite-stage-diagram] to
this $N$ and the normal integral $S$, obtaining integral normal stages $S_i$ finite over the
affine stages of $N$, dominant projections $S\to S_i$, and the finite natural transformation to
$N$. Each $S_i$ is affine by [lem-weil-pbc-finite-morphism-permanence](b), and Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]: a finite algebra is of finite type, as its module
generators also generate it as an algebra. The cone is limiting by
[lem-sbc-dominant-finite-refinement-limit]. The transition maps are affine since both source and
target are affine. Reindex by a nonempty directed set using
[lem-weil-pbc-cofiltered-limit-directed-reindex]. Dominance between integral schemes carries
generic point to generic point. Write $S=\operatorname{Spec}R$, $S_i=\operatorname{Spec}R_i$;
these dominant projections give injections $R_i\hookrightarrow R$ and $R=\varinjlim R_i$. The last
equality follows from the universal property of the affine limit, by testing maps from affine
schemes.
2. Apply [thm-pd-spreading-out](1) to $p$ and this system to obtain $Z_a\to S_a$ of finite
presentation with pullback $Z$. The stages are affine Noetherian, hence qcqs, and $Z_a$ is qcqs by
[lem-weil-pbc-qcqs-morphism-permanence](2). Apply [lem-weil-pbc-descend-flat-finite-presentation]
to obtain flatness at a later stage. Apply [lem-trf-geometrically-reduced-fibres-limit-descent] to
obtain reduced geometric fibres at a later stage. Choose a common upper bound; finite presentation
and flatness survive its base change by [lem-weil-pbc-qcqs-morphism-permanence](3) and
[lem-weil-pbc-flat-morphism-base-change]. Call this model $p_0:Z_0\to S_0$. It has every required
property of the family and base. It remains to construct the modification model. We shall show
directly that $f$ is an isomorphism, without invoking the downstream eta-normality node, and then
use the identity of $Z_0$.
3. Fix an affine open $U=\operatorname{Spec}A$ of $Z$. If it is empty its inverse image is empty,
so there is nothing to check; assume it nonempty. Its inverse image is affine, say
$\operatorname{Spec}B$, and $B$ is finite over $A$ by [def-weil-finite-integral-morphism]. The
algebra $A$ is finitely presented over $R$ by [lem-weil-pbc-lfp-affine-opens-finite-presentation].
Flatness gives $A\hookrightarrow A_K$, $K=\operatorname{Frac}R$, by
[lem-sc-flat-invertible-sections-torsion-free] with the trivial line bundle. Let $V$ be the common
schematically dense isomorphism open of $f$. If a section of $B$ vanishes on the generic fibre,
its restriction to $V\cap U$ vanishes, since the same torsion-freeness lemma applies to every
affine open of that flat open. Schematic density of $f^{-1}V$ then makes that section zero. Thus
$B\hookrightarrow B_K=A_K$, compatibly with $A\to B$, and we regard $A\subseteq B\subseteq A_K$.
The generic fibre is reduced by hypothesis and field-extension injectivity (a vector-space basis);
hence $A$ is reduced. No finite-presentation assertion about $B$ is used.
4. Choose finitely many $A$-algebra generators $b_1,\ldots,b_n$ of $B$ (module generators
suffice). By [lem-weil-pbc-finite-algebra-is-integral] choose monic polynomials $P_j(T)\in A[T]$
with $P_j(b_j)=0$. Since $B\subset A_K$, write all $b_j=a_j/r$ with a single $0\ne r\in R$ and
$a_j\in A$, by multiplying their finitely many denominators. Choose a finite presentation
$A=R[x_1,\ldots,x_m]/(g_1,\ldots,g_t)$. All coefficients of the $g_k$, of representatives of
$a_j$, and of the coefficients of $P_j$ occur at one stage $R_i$. Put
$A_i=R_i[x_1,\ldots,x_m]/(g_{1,i},\ldots,g_{t,i})$. Its base change is $A$. After increasing $i$,
$\operatorname{Spec}A_i\to S_i$ is flat by [lem-weil-pbc-descend-flat-finite-presentation] and has
reduced geometric fibres by [lem-trf-geometrically-reduced-fibres-limit-descent]. Flatness and
geometric reducedness of $U\to S$ follow by restriction from $p$, so both descent hypotheses hold.
Keep the same notation for the later coefficients and stage.
5. Arrange also $P_{j,i}(a_{j,i}/r_i)=0$ in $(A_i)_{r_i}$. Here is the finite-data check: if
$d_j=\deg P_j$, the polynomial $r^{d_j}P_j(a_j/r)$ is zero in $A$. In the displayed polynomial
presentation it is a finite combination $\sum_k h_{jk}g_k$. Adjoin the finitely many coefficients
of all $h_{jk}$ to the chosen stage. The equality of these polynomials then holds at a later stage
(each coefficient equality in the filtered colimit holds eventually). After localization it gives
the desired relation. Set $C_i=A_i[T_1,\ldots,T_n]/(P_{j,i}(T_j),r_iT_j-a_{j,i})$. The monic
relations bound each exponent of $T_j$ by $d_j-1$, so finitely many monomials generate $C_i$ as an
$A_i$-module. The linear relations give $(C_i)_{r_i}\cong(A_i)_{r_i}$ by substitution $T_j\mapsto
a_{j,i}/r_i$; the checked polynomial identities make the substitution well-defined. Sending $T_j$
to $b_j$ gives a surjection $C_i\otimes_{R_i}R\twoheadrightarrow B$.
6. Let $J_i=\{c\in C_i:r_i^Nc=0\text{ for some }N\}$ and $D_i=C_i/J_i$. This is an ideal: for two
elements use the larger exponent, and multiplication preserves annihilation. Localization
identifies $D_i$ with the image of $C_i$ in $(A_i)_{r_i}$. Flatness of $A_i$ over the domain $R_i$
gives $A_i\hookrightarrow(A_i)_{r_i}$ by [lem-sc-flat-invertible-sections-torsion-free].
Consequently $A_i\subseteq D_i\subseteq(A_i)_{r_i}$ and $(D_i)_{r_i}=(A_i)_{r_i}$. The algebra
$D_i$ is finite over $A_i$, being a quotient of $C_i$. Every element of $J_i$ maps to zero in $B$:
its image is killed by a power of the nonzero $r\in R$, while $B\subset A_K$. Thus the preceding
surjection factors as $D_i\otimes_{R_i}R\twoheadrightarrow B$. The construction requires a
surjection, not an unjustified isomorphism after a possibly nonflat base change.
7. Put $Y_i=\operatorname{Spec}A_i$ and $E_i=\operatorname{Spec}D_i$. These are Noetherian by
[lem-weil-pbc-finite-type-over-noetherian]. Let $W\subset Y_i$ be the isomorphism locus of the
finite algebra inclusion $A_i\subset D_i$. It is open: its complement is the support of the finite
module $D_i/A_i$, and if this module vanishes at a prime, one element outside that prime kills all
of a finite list of generators, so it vanishes on a principal neighbourhood. It contains $D(r_i)$
and the generic fibre over $S_i$, since $(D_i)_{r_i}=(A_i)_{r_i}$. Moreover
$\widetilde{D_i}\subset j_*\mathcal O_W$ for $j:W\hookrightarrow Y_i$: a section vanishing on $W$
vanishes after inverting $r_i$, and $D_i\hookrightarrow(A_i)_{r_i}$ remains injective upon
localization on $Y_i$.
8. We show that $W$ contains the generic points of every fibre of $Y_i\to S_i$. At such a point
[lem-trf-generic-fibre-points-smooth] supplies a smooth neighbourhood $T$. All local rings of $T$
are integrally closed domains by [lem-weil-pbc-smooth-ring-map-iff-smooth-affine] and
[lem-weil-pbc-smooth-over-normal-ring-normal], since $S_i$ is normal. The open $D(r_i)$ is dense
on $T$: flatness makes multiplication by $r_i$ injective on every affine chart, so localization is
injective; an open on which $r_i$ were everywhere nilpotent would contradict that injection. For
an affine open $H\subset T$, each section of the finite algebra $\widetilde{D_i}(H)$ is integral
over $\mathcal O_T(H)$ by [lem-weil-pbc-finite-algebra-is-integral]. Its restriction to $H\cap
D(r_i)$ extends to $\mathcal O_T(H)$ by [lem-sbc-normal-dense-open-integral-section]. The
injection into the $r_i$-localization makes the extension equal to the original section. Therefore
$\widetilde{D_i}|_T=\mathcal O_T$, so $T\subset W$. All smoothness and extension inputs are
applied to Noetherian schemes at this stage.
9. If $y\notin W$ and $s$ is its image in $S_i$, then $s\ne\eta_i$, because $W$ contains the
generic fibre. The local domain $R_{i,s}$ therefore has a nonzero maximal-ideal element, which is
a nonzerodivisor, so its depth is at least one. The fibre local ring $F=\mathcal O_{(Y_i)_s,y}$ is
reduced: its extension to an algebraic closure is reduced by the retained geometric-fibre
hypothesis, and scalar extension of a field is injective. The point $y$ is not a generic point of
a fibre component by the preceding step. Thus the local ring $F$ has dimension at least one.
[lem-weil-pbc-serre-criterion-reduced] gives depth $F\ge1$. Apply
[lem-weil-pbc-flat-local-depth-formula] to the flat local map $\mathcal O_{S_i,s}\to\mathcal
O_{Y_i,y}$; both rings are Noetherian, and its closed-fibre ring is $F$. It gives depth $\mathcal
O_{Y_i,y}\ge2$.
10. Apply [lem-sbc-depth-two-hartogs-restriction] to $L=Y_i$, its open $W$, and $N=\mathcal
O_{Y_i}$. It is quasi-coherent and finite on every affine chart and at every stalk; $Y_i$ is
Noetherian, and the previous step verifies the depth hypothesis at every point of the complement.
Hence $\mathcal O_{Y_i}=j_*\mathcal O_W$. Since $\mathcal O_{Y_i}\subseteq\widetilde{D_i}\subseteq
j_*\mathcal O_W$, we get $D_i=A_i$. The surjection in step 6 now reads $A\twoheadrightarrow B$,
and it is the original injective structure map $A\hookrightarrow B\subset A_K$. It is therefore an
isomorphism. This holds for every affine open $U\subset Z$, so the inverses of the restrictions of
$f$ glue (uniquely on overlaps) to an inverse of $f$. This argument establishes the needed
conclusion directly and never cites the downstream eta-normality node, which depends on this item.
11. Take $Z^{\prime}_0=Z_0$ and $f_0=\mathrm{id}_{Z_0}$ for the family chosen in step 2. The
identity is finite and proper directly from [def-weil-finite-integral-morphism] and
[def-weil-proper-morphism], and is an $\eta_0$-modification with $V=Z_0$: restriction to the whole
scheme is injective, including for the empty scheme. The model isomorphism $Z\cong
Z_0\times_{S_0}S$, composed with the now proved isomorphism $f:Z^{\prime}\to Z$, supplies the
second model isomorphism, and makes the diagram with $f_0$ commute. The dominant projection $S\to
S_0$ takes the generic point to the generic point, as recorded in step 1. These are precisely the
compatible base-change isomorphisms and all the required clauses. -/
theorem exists_normal_noetherian_model_of_finite_eta_modification
    {S Z Z' : Scheme.{u}} [IsAffine S] [IsIntegral S]
    (hS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s))
    (p : Z ⟶ S) [Flat p] [LocallyOfFinitePresentation p]
    [QuasiCompact p] [QuasiSeparated p] [GeometricallyReduced p]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (f : Z' ⟶ Z) [IsFinite f] [IsProper f]
    (hfη : IsIso (((Over.pullback (S.fromSpecResidueField η)).map
      (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p)).left))
    (hf : ∃ V : Z.Opens,
      (∀ W : Z.Opens, Function.Injective (V.ι.app W)) ∧
      (∀ W : Z'.Opens, Function.Injective ((f ⁻¹ᵁ V).ι.app W)) ∧
      IsIso (pullback.snd f V.ι)) :
    ∃ (S₀ Z₀ Z'₀ : Scheme.{u}) (q : S ⟶ S₀) (p₀ : Z₀ ⟶ S₀)
      (f₀ : Z'₀ ⟶ Z₀) (η₀ : S₀),
      IsAffine S₀ ∧ IsIntegral S₀ ∧ IsNoetherian S₀ ∧
      (∀ s : S₀, IsDomain (S₀.presheaf.stalk s) ∧
        IsIntegrallyClosed (S₀.presheaf.stalk s)) ∧
      IsDominant q ∧ IsGenericPoint η₀ Set.univ ∧ q η = η₀ ∧
      Flat p₀ ∧ LocallyOfFinitePresentation p₀ ∧ QuasiCompact p₀ ∧ QuasiSeparated p₀ ∧
      GeometricallyReduced p₀ ∧ IsFinite f₀ ∧ IsProper f₀ ∧
      IsIso (((Over.pullback (S₀.fromSpecResidueField η₀)).map
        (Over.homMk f₀ rfl : Over.mk (f₀ ≫ p₀) ⟶ Over.mk p₀)).left) ∧
      (∃ V₀ : Z₀.Opens,
        (∀ W : Z₀.Opens, Function.Injective (V₀.ι.app W)) ∧
        (∀ W : Z'₀.Opens, Function.Injective ((f₀ ⁻¹ᵁ V₀).ι.app W)) ∧
        IsIso (pullback.snd f₀ V₀.ι)) ∧
      ∃ (e : Z ≅ pullback p₀ q) (e' : Z' ≅ pullback (f₀ ≫ p₀) q),
        e.hom ≫ pullback.snd p₀ q = p ∧
        e'.hom ≫ ((Over.pullback q).map
          (Over.homMk f₀ rfl : Over.mk (f₀ ≫ p₀) ⟶ Over.mk p₀)).left = f ≫ e.hom := by
  sorry

end AlgebraicGeometry
