/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization
public import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
public import Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

import Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials
import Sheaf.AlgebraicGeometry.DegreeWeightedIrreducibleComponents
import Sheaf.TraceFormula.ReducedCurveNormalizationGenus
import Sheaf.AlgebraicGeometry.ProperCurveBundlePullbackDegree
import Sheaf.AlgebraicGeometry.NodalSpecialCliffordSubcurve
import Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import Sheaf.TraceFormula.NodalSubcurveBoundary
import Sheaf.AlgebraicGeometry.NodalNormalizationQuotient
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import Sheaf.AlgebraicGeometry.NodalCurveNormalizationEuler
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Gieseker potential stability and the balanced subcurve inequality

Source: Morrison, arXiv:0810.2340, Section 3.2, Definition 7 and Theorem 8,
printed pp. 13--15; Section 3.3, equation (6).
(blueprint: lem-sfb-gieseker-potential-stability).

The conclusion enumerates the reduced integral components exactly once. All degrees
are computed on their canonical normalizations. Subcurves are arbitrary nonempty proper
subsets of this enumeration, so disconnected subcurves are included.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The clauses of potential stability, on the same specified embedded curve.
The coordinate-section bijection expresses both nondegeneracy and completeness.
Source: Morrison, Section 3.2, Definition 7; Section 3.3, equation (6).
(blueprint: lem-sfb-gieseker-potential-stability). -/
structure GiesekerPotentialStabilityConclusion
    (k : Type u) [Field k] (g d n : ℕ)
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [LocallyOfFinitePresentation f]
    (i : C ⟶ ℙ(HilbertPlucker.Coordinates n; Spec (.of k))) where
  reduced : IsReduced C
  pure : C.IsPureDimension 1
  nodal : ∀ x : C, x ∉ f.smoothLocus →
    Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
        (C.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))
  hyperplane : C.Modules
  hyperplane_iso : (Scheme.Modules.tensorPullback i).obj
      (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) 1) ≅ hyperplane
  complete_nondegenerate : Function.Bijective
    (fun a : HilbertPlucker.Coordinates n → k ↦
      ∑ j : HilbertPlucker.Coordinates n,
        f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv (a j)) •
          hyperplane_iso.hom.app ⊤
            (((Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app
              (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) 1)).app ⊤
                (ProjectiveSpace.twistOneSection
                  (HilbertPlucker.Coordinates n) (Spec (.of k)) j)))
  h0 : Module.finrank k
      ((RingedSpace.moduleCohomology C.toRingedSpace 0 ⋙
        ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        hyperplane) = n + 2
  h1 : Subsingleton ((RingedSpace.moduleCohomology C.toRingedSpace 1).obj hyperplane)
  omega : C.Modules
  dualizing : NodalDualizingDatum f omega
  count : ℕ
  component : Fin count → Scheme.{u}
  integral : ∀ a, IsIntegral (component a)
  inclusion : ∀ a, component a ⟶ C
  closed : ∀ a, IsClosedImmersion (inclusion a)
  distinct : Function.Injective (fun a ↦ Set.range (inclusion a))
  exhaustive : ∀ E : Set C,
    E ∈ irreducibleComponents C ↔ ∃ a, Set.range (inclusion a) = E
  rational_component_branches : ∀ a : Fin count,
    @markedNodalComponentGenus k _ (component a) (integral a) (inclusion a ≫ f) = 0 →
      2 ≤ ((@Scheme.fromNormalization (component a) (integral a) ≫ inclusion a) ⁻¹'
        {x | x ∉ f.smoothLocus}).ncard
  balanced : ∀ S : Finset (Fin count), S.Nonempty → S ≠ Finset.univ →
    |((∑ a ∈ S, @markedNodalComponentDegree k _ C (component a) (integral a)
        (inclusion a) (inclusion a ≫ f) hyperplane : ℤ) : ℚ) -
      (d : ℚ) / (2 * (g : ℚ) - 2) *
        ((∑ a ∈ S, @markedNodalComponentDegree k _ C (component a) (integral a)
          (inclusion a) (inclusion a ≫ f) omega : ℤ) : ℚ)| ≤
      ((((⋃ a ∈ S, Set.range (inclusion a)) ∩
        (⋃ a ∈ Sᶜ, Set.range (inclusion a))).ncard : ℕ) : ℚ) / 2
  rational_two_point_degree : ∀ a : Fin count,
    Smooth (inclusion a ≫ f) →
    @markedNodalComponentGenus k _ (component a) (integral a) (inclusion a ≫ f) = 0 →
    (Set.range (inclusion a) ∩
      (⋃ b ∈ ({a}ᶜ : Finset (Fin count)), Set.range (inclusion b))).ncard = 2 →
    @markedNodalComponentDegree k _ C (component a) (integral a)
      (inclusion a) (inclusion a ≫ f) hyperplane = 1

/-- The closed curve is exactly the subscheme classified by the supplied Hilbert point,
using pullback of the recorded universal ideal. No arbitrary association is allowed.
Source: Morrison, Section 3.2, universal Hilbert family preceding Definition 7.
(blueprint: lem-sfb-gieseker-potential-stability). -/
def HilbertPointRepresents
    {k : Type u} [Field k] {n : ℕ} {P : NumericalHilbertPolynomial}
    (C : Scheme.{u})
    (i : C ⟶ ℙ(HilbertPlucker.Coordinates n; Spec (.of k)))
    (D : HilbertPlucker.Hilbert k n P)
    (x : PGLLinearization.fieldTest k k ⟶ D.H) : Prop :=
  ∃ e : C ≅
      (D.ideal.comap (ProjectiveSpace.map (HilbertPlucker.Coordinates n) x.left)).subscheme,
    e.hom ≫ (D.ideal.comap
      (ProjectiveSpace.map (HilbertPlucker.Coordinates n) x.left)).subschemeι = i

/-- Semistability in a uniformly sufficiently large Hilbert degree implies all the
potential-stability clauses and the balanced inequality on every reduced component union.
The parameter `n` writes the number of coordinates as `n + 2`; the numerical hypotheses
imply it is at least two. The bound precedes the field quantifier.
Source: Morrison, Section 3.2, Definition 7 and Theorem 8; Section 3.3, equation (6).
(blueprint: lem-sfb-gieseker-potential-stability).

Proof plan (the fifteen DAG steps, with their recorded dependencies):
1. Put $h=g-1>0$, $r=d-h$ and $t=d/r$. Then $r>0$, $d\ge10$, and $1<t<9/8<8/7$. Use [lem-sfb-
bounded-hilbert-weight-polynomials] with $B=4$, obtaining $A,m_0$. Increase $m_0$ to the uniform
Hilbert-embedding bound of [lem-sfb-hilbert-plucker-pgl-linearization]. Choose an integer $M\ge
m_0$ with $M>2rA$. This depends only on $g,d$, since $P,r,B$ do. For any $m\ge M$ with
semistable Hilbert point and any one of these weighted flags, the two inequalities in the weight
lemma give
$$a_F\le t\sum_iw_i+\frac{A-h\sum_iw_i/r}{m}\le t\sum_iw_i+A/m.$$
The difference
$a_F-t\sum_iw_i$ lies in $(2r)^{-1}\mathbf Z$. Since $A/m<1/(2r)$, it follows that $a_F\le
t\sum_iw_i$. This conclusion holds simultaneously for all these flags on every curve in
question. Denote it by (*).

2. The weight lemma gives $\dim C=1$. A field is Noetherian, and a projectively embedded scheme
is finite type; [lem-weil-pbc-finite-type-over-noetherian] therefore makes $C$ Noetherian. It
has finitely many irreducible components by [lem-weil-pbc-noetherian-finite-components]. A zero-
dimensional irreducible component would be a closed isolated point: it cannot meet another
irreducible component without being contained in it. Connectedness and $\dim C=1$ rule this out.
Thus $D=C_{\mathrm{red}}$ is a connected reduced curve of pure dimension one. The identification
of coordinate Hilbert polynomial with Euler polynomial in [lem-sfb-flat-projective-hilbert-
polynomial-locality], applied over $\operatorname{Spec}k$, gives $\chi(C,\mathcal
O_C(n))=dn+1-g$ for every integer $n$.

3. Suppose a nonzero space $W$ of linear forms vanishes on $D$. Give it weight zero and its
quotient weight one, so $s=\dim(k^r/W)<r$. The ideal of $D$ in $C$ is the nilradical. It is
nilpotent: on a finite affine cover, finitely many nilpotent generators admit a common exponent,
and the maximum of these finitely many exponents gives $N^q=0$. A nonzero restricted degree-$n$
monomial therefore has fewer than $q$ factors from $W$, so its weight is at least $n-q+1$. Thus
$$w_F(n)\ge(n-q+1)P(n),\qquad a_F\ge d.$$
But (*) gives $a_F\le ds/r<d$, a contradiction. Hence
$D$ is nondegenerate. No bound on $q$ is needed: uniformity in $m$ already came from the
bounded-weight lemma.

4. If the generic multiplicity along a reduced component of degree $e\ge1$ exceeded one, the
component-projection lemma would give a zero/one flag with $s\le e+1$ and $a_F\ge2e+1/2$. Its
hypotheses hold by steps 1--3. The inequality
$$2e+\tfrac12-\tfrac87(e+1)=\tfrac67e-\tfrac9{14}>0\quad(e\ge1)$$
contradicts (*) and $t<8/7$.
Thus $C$ is generically reduced. If now a reduced component of degree $e\le3$ were not rational
normal, the other projection estimate would give $s\le e$ and $a_F\ge e+1/2$. Since
$e+1/2-(8/7)e=1/2-e/7\ge1/14>0$, this again contradicts (*). Consequently every such component
is rational normal. These estimates concern component degrees on normalization, as specified in
the cited lemma. Finally $\deg_C L=P(1)-P(0)=d$ in the Euler-degree convention. The component
formula [lem-trf-degree-weighted-irreducible-components] now has all multiplicities one. Each
component normalization is a smooth proper integral curve and is finite birational by [lem-trf-
reduced-curve-normalization-genus]. The degree-one pullback formula [lem-sfb-proper-curve-
bundle-pullback-degree] identifies its hyperplane degree with the component's Euler-degree.
Consequently the sum of the normalized component degrees of $D$ is $d$, also before the finite-
length nilradical is eliminated.

5. Apply the jet-weight lemma to $C$. Its generically reduced and nondegenerate hypotheses and
its low-degree prerequisite were proved above. A ramified normalized branch would give $a_F\ge8$
with $\sum w_i\le7$, contradicting (*) and $7t<8$. A point of multiplicity at least three would
give $a_F\ge3/2$ and $\sum w_i=1$, contradicting $t<8/7$. Finally a nonnodal double point, after
all normalization maps are unramified, would give $a_F\ge7/2$ with $\sum w_i\le3$, contradicting
$3t<24/7<7/2$. Thus every singularity of $D$ is an ordinary node, with the completed local ring
in the statement. This includes double points with a tangent line component; their coefficient
is $7/2$, so they cannot be discarded using only the larger coefficient for the other tangent
case.

6. The hyperplane line on $D$ is very ample, since the reduced closed subscheme still embeds in
projective space. If $H^1(D,L)$ were nonzero, [lem-sfb-nodal-special-clifford-subcurve] would
supply a connected subcurve $Y$ with $e=\deg_Y L\ge2$ and $h^0(Y,L)\le e/2+1$. If $Y=D$,
nondegeneracy gives $r\le h^0(D,L)\le d/2+1$, contrary to $r=d+1-g$ and $d>2g$. Suppose $Y$ is
proper instead. It meets its complement, since $D$ is connected. Choose one such boundary branch
on a normalized complementary component. Its hyperplane degree is a positive integer by [lem-
trf-fibre-degree-ample-criterion], because it is the pullback of an ample line. For the selected
single branch, the degree condition in [lem-sfb-subcurve-span-weight-bound] holds. That lemma
and (*) yield
$$e+\tfrac12\le t\,h^0(Y,L)\le t(e/2+1).$$
But
$e+1/2-(8/7)(e/2+1)=3e/7-9/14\ge3/14>0$ for $e\ge2$. This contradiction proves $H^1(D,L)=0$.

7. Let $N=\ker(\mathcal O_C\to\mathcal O_D)$. It is coherent, since $C$ is Noetherian, and its
stalks vanish at every generic point by generic reducedness. Its closed support is therefore
zero-dimensional, a finite set of closed points. By [lem-sfb-coherent-zero-dimensional-support],
both $N\otimes\mathcal O_C(1)$ and $N$ have no higher cohomology, and zero global sections would
force either to be zero. Tensor the reduction sequence by the invertible hyperplane line; this
preserves exactness, as checked in any local trivialization. Cohomology across the closed
immersion $D\to C$ is identified by [lem-weil-pbc-affine-morphism-cohomology-edge]. The long
exact sequence and step 6 give $H^1(C,\mathcal O_C(1))=0$. Vanishing in degrees at least two
follows from [lem-sc-noetherian-cohomology-above-dimension], since $\dim C=1$. Thus the Euler
polynomial at $1$ gives $h^0(C,\mathcal O_C(1))=P(1)=r$.

8. The same long exact sequence now gives
$$h^0(D,L)=r-h^0(C,N\otimes\mathcal O_C(1)).$$
Nondegeneracy of $D$ means exactly that restriction of the $r$-dimensional space of ambient
linear forms to $D$ is injective. Therefore $h^0(D,L)\ge r$, forcing $h^0(C,N\otimes\mathcal
O_C(1))=0$. Global generation in [lem-sfb-coherent-zero-dimensional-support] gives
$N\otimes\mathcal O_C(1)=0$, hence $N=0$ after tensoring with the inverse line. Thus $C=D$ is
reduced, pure one-dimensional and nodal. Ambient linear forms inject into the $r$-dimensional
$H^0(C,L)$ and so give an isomorphism. This proves completeness, nondegeneracy, $h^0=r$ and
$h^1=0$.

9. For each nonempty proper reduced union $Y$ and its reduced complement $Z$, [lem-trf-nodal-
subcurve-boundary] says that their intersection is precisely a finite reduced set of boundary
nodes and that each has one smooth branch there on either side. Apply [lem-sfb-gieseker-
component-interpolation] to the reduced complete nonspecial embedding obtained in step 8 and the
inequalities (*) from step 1. For each normalized component $E$ of $Z$, its degree is at least
the number $b_E$ of its boundary branches, or it is a rational normal component of degree
$b_E-1$. In the latter case positivity of the hyperplane degree gives $b_E\ge2$. Thus all the
hypotheses of [lem-sfb-subcurve-span-weight-bound] hold with every boundary branch chosen. It
gives a zero/one flag with
$$\deg_YL+\tfrac{k_Y}{2}\le a_F\le t s\le t h^0(Y,L|_Y).$$
There is
no connectedness requirement on $Y$ in that weight estimate.

10. For any such $Y$, let $K$ be the kernel of the surjection $L\to i_*(L|_Y)$ for its closed
immersion $i:Y\to C$. This kernel is coherent, and [lem-sc-noetherian-cohomology-above-
dimension] gives $H^2(C,K)=0$. The exact cohomology sequence and $H^1(C,L)=0$ then give
$H^1(C,i_*L|_Y)=0$. Apply [lem-weil-pbc-affine-morphism-cohomology-edge] to $i$ to obtain
$H^1(Y,L|_Y)=0$. Also $H^q(Y,L|_Y)=0$ for $q\ge2$ by the same dimension-vanishing statement.
Hence $h^0(Y,L|_Y)=\chi(Y,L|_Y)$. This holds separately on each connected component if $Y$ is
disconnected.

11. Apply [lem-trf-nodal-normalization-quotient] separately to each connected component of $Y$.
Tensor its exact sequence by $L|_Y$. Local trivializations identify the resulting middle term
with the finite direct image of the pulled-back line and the last term with one one-dimensional
fibre per internal node. The quotient has the same Euler characteristic before and after
twisting. Euler additivity [lem-pc-euler-additive] and the affine cohomology comparison for the
finite normalization [lem-weil-pbc-affine-morphism-cohomology-edge] therefore give
$$\chi(Y,L|_Y)-\chi(Y,\mathcal O_Y)=\sum_{E\subset\widetilde
Y}\bigl(\chi(E,L|_E)-\chi(E,\mathcal O_E)\bigr)=\deg_Y L.$$
The last equality is exactly [def-
pc-degree-line-bundle] on each smooth normalized component. Combining with step 10 gives
$h^0(Y,L|_Y)=\deg_YL+\chi(Y,\mathcal O_Y)$.

12. Let $v_Y$ be the number of components of $Y$, $e_Y^{\mathrm{int}}$ its internal-node count
(a self-node counts once), and $g_E$ the genera of its normalized components. Summing [lem-trf-
nodal-curve-normalization-euler] over the connected components gives
$$\chi(Y,\mathcal O_Y)=v_Y-
e_Y^{\mathrm{int}}-\sum_Eg_E.$$
The unmarked degree formula of [lem-sfb-nodal-log-canonical-
reconstruction] gives, on the same components of the whole nodal curve $C$,
$$w_Y:=\deg_Y\omega_C=\sum_E(2g_E-2+\text{node branches on }E)
=-2\chi(Y,\mathcal O_Y)+k_Y.$$
Each internal node contributes two branches, each boundary node one. For $Y=C$, the same count
and $\chi(C,\mathcal O_C)=P(0)=1-g$ give $w_C=2g-2$. The dualizing-line lemma applies over
$\operatorname{Spec}k$ with no markings: projectivity, connectedness, reducedness, purity and
nodality were proved, and a finite-type scheme over a field is finitely presented and flat over
that field.

13. Write $l_Y=\deg_YL$ and $\chi_Y=\chi(Y,\mathcal O_Y)$. Substitute step 11 in step 9 and
multiply by $r>0$:
$$r(l_Y+k_Y/2)\le d(l_Y+\chi_Y).$$
Since $d-r=g-1=h$ and $\chi_Y=(k_Y-w_Y)/2$
from step 12, this rearranges to
$$h l_Y\ge (d/2)w_Y-(h/2)k_Y,$$
so $l_Y-dw_Y/(2h)\ge-k_Y/2$.
This is an exact inequality: the integral-gap argument in step 1 removed the finite-$m$ error
before we used any subcurve.

14. The component-degree definition is additive on complementary unions, so $l_Z=d-l_Y$ and
$w_Z=2g-2-w_Y$; the equality $l_C=d$ also follows by applying step 11's normalization
computation to $C$ and using $P(1)-P(0)=d$. The same boundary nodes give $k_Z=k_Y$. Apply step
13 to $Z$ and substitute these three identities. This yields $l_Y-dw_Y/(2g-2)\le k_Y/2$.
Together the two bounds are exactly the asserted absolute-value inequality, including when $Y$
or $Z$ is disconnected.

15. Consider an irreducible component whose normalization has genus zero, and let $b$ count all
node branches on that normalization. Its positive integral hyperplane degree is $l\ge1$ by [lem-
trf-fibre-degree-ample-criterion], and its dualizing degree is $-2+b$ by [lem-sfb-nodal-log-
canonical-reconstruction]. If $C$ is irreducible, the Euler/branch computation of step 12 gives
$b=2g\ge4$. If the component is proper and $b\le1$, it has no self-node and hence is smooth; its
boundary count is $b$ (and connectedness in fact gives $b\ge1$). The balanced inequality on that
component would then give
$$\left|l-\frac d{2g-2}(-2+b)\right|\le b/2,$$
which is impossible
since $l\ge1$ and $-2+b\le-1$. Thus every genus-zero normalized component has at least two node
branches. Finally for a smooth rational component meeting its complement in two points, there
are no internal self-nodes, $b=k=2$, and the dualizing degree is zero. The inequality gives
$|l|\le1$, and positivity gives $l=1$.
-/
theorem gieseker_potential_stability
    (g d n : ℕ) (hg : 2 ≤ g) (hd : 9 * (g - 1) < d)
    (hn : n + 2 = d + 1 - g) :
    ∃ M : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (C : Scheme.{u}) (f : C ⟶ Spec (.of k))
      (i : C ⟶ ℙ(HilbertPlucker.Coordinates n; Spec (.of k))),
      IsClosedImmersion i → ConnectedSpace C →
      i ≫ (ℙ(HilbertPlucker.Coordinates n; Spec (.of k)) ↘ Spec (.of k)) = f →
      ∀ (P : NumericalHilbertPolynomial),
      P.1 = Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (1 - (g : ℚ)) →
      ProjectiveHilbertPolynomial.IsCoordinatePolynomial k (n + 1) i P.1 →
      ∀ (D : HilbertPlucker.Hilbert k n P) (m : ℕ), M ≤ m →
      ∀ (E : HilbertPlucker.Presentation D m)
        (x : PGLLinearization.fieldTest k k ⟶ D.H),
        HilbertPointRepresents C i D x →
        x.left (IsLocalRing.closedPoint k) ∈ E.semistable →
        ∃ (_lfp : LocallyOfFinitePresentation f),
          Nonempty (@GiesekerPotentialStabilityConclusion k _ g d n C f _lfp i) := by
  sorry

end AlgebraicGeometry
