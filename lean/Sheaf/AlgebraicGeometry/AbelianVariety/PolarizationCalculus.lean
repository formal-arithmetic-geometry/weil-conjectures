module

public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.InfiniteClosedPointsInterOfTopologicalKrullDimPos
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube

/-! # Dual abelian varieties and line-bundle homomorphisms

Source: Milne, Abelian Varieties, Chapter I §§5, 8, 9, especially Proposition 8.1,
Remark 8.2, pp.36–40, and §9 opening paragraph.
(blueprint: lem-sfb-abelian-polarization-calculus)

The normalized difference includes the constant identity-line factor. Thus no basis
of that line is chosen. Translation, inversion and pullback are stated as identities
of classifying families; uniqueness identifies their classifying morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj GrpObj

namespace AlgebraicGeometry

open Scheme.Modules

/-- Existence of the dual, with its dimension, normalized Poincare universal property,
line-bundle homomorphisms, translation invariance, pullback and inversion formulas,
and the effective Cartier divisor isogeny criterion.

Source: Milne AV I §§5, 8, 9; Proposition 8.1 and Remark 8.2; pp.36–40;
§9 opening paragraph (blueprint: lem-sfb-abelian-polarization-calculus).

Proof plan:
1. By [lem-sc-abelian-variety-projective] and [lem-sc-abelian-variety-characterization], $A$ is
projective and geometrically integral. Apply [lem-sfb-projective-picard-identity-representability]
with $X=A$ and $e=0$, and provisionally denote its proper connected identity component by $P$. It
represents exactly the rigidified fibrewise algebraically trivial families in the statement, with
tensor group law and universal sheaf $\mathcal P$. Both identity-axis normalizations are part of
that representing construction. Smoothness and dimension of $P$ will be proved below; they are not
assumed here.

2. Let $c:A\times A\to\operatorname{Spec}k$. Use the explicitly normalized family $N_L=m^*L\otimes
p_1^*L^{-1}\otimes p_2^*L^{-1}\otimes c^*(0^*L)$. Cancellation gives its canonical trivializations
on both identity axes. Its fibre at $y$ is $t_y^*L\otimes L^{-1}$ up to a constant one-dimensional
factor. These classes are algebraically trivial: the same family, parameterized by the connected
smooth variety $A$, connects each fibre to the trivial fibre at $0$. Thus [lem-sfb-projective-
picard-identity-representability] gives a unique $\phi_L:A\to P$ and
$N_L\cong(1\times\phi_L)^*\mathcal P$. Dropping the constant factor after choosing a basis of
$0^*L$ gives the displayed $L_0$ in the item.

3. Apply [thm-sc-theorem-of-cube] on $A_x\times A_y\times A_z$. Rearranging its seven factors, and
retaining the constant identity-line factors, gives $N_L(x,y+z)\cong N_L(x,y)\otimes N_L(x,z)$ as
families on the first factor, rigidified at $x=0$. For example the unnormalized quotient of these
two sides is $L_{x+y+z}L_xL_yL_z/(L_{x+y}L_{x+z}L_{y+z})$, which is trivial by the cited cube
identity; the identity-line normalization cancels its remaining constant factor. Representability
and the tensor group law identify this equality of families with
$\phi_L(y+z)=\phi_L(y)+\phi_L(z)$. The zero fibre gives $\phi_L(0)=0$, so this is a homomorphism
of group schemes.

4. For $b\in A(k)$, substitute $(x,y,b)$ in the same cube identity. It says, after cancelling
$L_x,L_y,L_b$ and normalizing the two axes, that $N_{t_b^*L}\cong N_L$ as rigidified families on
$A\times A$. Apply the uniqueness in [lem-sfb-projective-picard-identity-representability] to
obtain $\phi_{t_b^*L}=\phi_L$. This is an equality of morphisms, since the cube was used on the
whole parameter scheme, rather than just on its rational points.

5. Apply the same representing construction to $B$. Pulling a rigidified family back by $a\times1$
preserves its rigidification because $a(0)=0$, and preserves algebraic equivalence by pulling back
each family in its defining chain. It also preserves tensor products. Hence it defines a
homomorphism $a^\vee:P_A\to P_B$. For a variable $y\in B$, $a\circ t_y=t_{a(y)}\circ a$, so
$(a\times1)^*N_L$ evaluated at $a(y)$ is the normalized family $t_y^*a^*L\otimes(a^*L)^{-1}$. This
equality of pullback families over $B$ gives $\phi_{a^*L}=a^\vee\phi_La$ by representability.

6. For the universal algebraically trivial line bundle $M$ on $A\times P$, its translated
difference is again algebraically trivial on each fibre, by the connected family used in step 2.
Thus it defines $d:A\times P\to P$, $(x,[M])\mapsto[t_x^*M\otimes M^{-1}]$. On $A\times\{0\}$ it
is zero. Apply [lem-sc-rigidity] with first factor $A$, connected second factor $P$, and separated
finite-type target $P$. The first factor is proper, geometrically connected and geometrically
reduced by [lem-sc-abelian-variety-characterization]. Rigidity makes $d$ independent of $x$, and
$d(0,[M])=0$ makes it identically zero. By the representing property the normalized family $N_M$
is trivial, universally over $P$. Pulling the resulting identity $m^*M\cong p_1^*M\otimes p_2^*M$
back by $x\mapsto(x,-x)$ shows $[-1]^*M\cong M^{-1}$, with identity normalization. Consequently
$[-1]^\vee=[-1]$ on $P$. Step 5 and the homomorphism property now give
$\phi_{[-1]^*L}=(-1)\phi_L(-1)=\phi_L$.

7. Suppose $H$ is ample and put $K=\ker\phi_H$. This is a closed subgroup: it is the inverse image
of the closed identity of the separated group $P$. By [lem-sfb-abelian-closed-subgroup-reduced-
component], $B=(K_{\mathrm{red}})^0$ is an abelian subvariety and $\dim B=\dim K$. Since
$\phi_H|_B=0$, the representing identity for $N_H$ restricts trivially on $B\times B$. Pulling
back along $(1,-1):B\to B\times B$ shows $H|_B\otimes[-1]^*(H|_B)$ is trivial up to a constant
line. The restriction $H|_B$ is ample. Let $H^{\otimes m}$ be very ample [def-sc-ample];
restricting its closed immersion $A\to\mathbf P^N$ to $B$ gives a closed immersion $i:B\to\mathbf
P^N$ with $i^*\mathcal O(1)\cong M:=H^{\otimes m}|_B$, defined by the restricted sections
$s_0,\dots,s_N\in H^0(B,M)$, which generate $M$. The complete linear system $j:B\to\mathbf
P(H^0(B,M)^\vee)$ satisfies $i=\pi\circ j$, where $\pi$ is the linear projection dual to
$k^{N+1}\to H^0(B,M)$, defined on the open complement of the common zero locus of the $s_k$, which
contains $j(B)$. Hence $j$ is a monomorphism; it is proper by [lem-weil-pbc-proper-to-separated],
hence a closed immersion by [lem-pc-proper-monomorphism-closed], so $M$ is very ample. Its inverse
pullback is ample too, and [lem-sc-ample-tensor] makes their tensor product ample. On a positive-
dimensional proper geometrically integral $B$, a trivial bundle cannot be ample: [lem-
pc-h0-proper-variety] gives $H^0(B,\mathcal O_B)=k$, so every morphism defined by sections of a
trivial power is constant and cannot be a closed immersion. Hence $\dim B=0$, and the closed-
subgroup auxiliary makes $K$ finite, including its possible infinitesimal structure.

8. Choose an ample $H$ using [lem-sc-abelian-variety-projective]. The map $\phi_H:A\to P$ is
proper by [lem-weil-pbc-proper-to-separated] and has finite kernel by step 7. For a closed target
point its residue field is $k$ by [lem-weil-pbc-closed-point-residue-field-base]. Every nonempty
fibre has a closed point by [lem-sc-lft-over-field-jacobson-space], again rational over $k$.
Choose one, $u$; then $v\mapsto v-u$ and $w\mapsto u+w$ identify that entire scheme-theoretic
fibre with the finite kernel. Empty fibres cause no problem. The positive-dimensional-fibre locus
is closed by [lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous]; if nonempty, Jacobson
density would give a closed target point in it, which we just ruled out. Thus all fibres have
dimension at most zero, and [lem-zl-finite-type-fibre-image-dimension-bounds] gives $g\leq\dim P$.
The Picard tangent identity [lem-sfb-projective-picard-identity-representability] and [lem-sfb-
abelian-structure-h1-dimension] give $\dim_kT_0P=g$. By [lem-ag-group-identity-local-dimension]
and [lem-weil-pbc-regular-local-cotangent-dimension], $\dim P\leq g$. Equality follows, and the
same local-ring criterion makes $\mathcal O_{P,0}$ regular.

9. The regular closed-point smoothness criterion [lem-weil-pbc-regular-closed-point-smooth-source]
on an affine neighborhood of $0$ makes $P$ smooth at $0$. Every closed point is $k$-rational by
[lem-weil-pbc-closed-point-residue-field-base], so translation gives the same local-ring
regularity and smoothness at every closed point. The smooth locus is open (it is the union of the
neighborhoods on which the affine-local smooth condition holds). Its closed complement, if
nonempty, contains a closed point by [lem-sc-lft-over-field-jacobson-space], a contradiction. Thus
$P$ is smooth everywhere. It is already proper and connected, so it is the abelian variety
$A^\vee$ required in the statement, and step 8 proves $\dim A^\vee=g$. Apply [lem-sc-abelian-
variety-characterization] to see that it is irreducible as well.

10. Any $\phi_L$ with finite scheme-theoretic kernel is surjective now that $A$ and $A^\vee$ have
equal dimension. Indeed the closed-target fibres are translates of the kernel, and the proper
fibre-dimension and Jacobson argument of step 8 makes every fibre zero-dimensional. By [lem-weil-
pbc-proper-to-separated] the homomorphism is proper, and its image $Z$ is closed by [lem-weil-pbc-
proper-closed-image]; Since $A$ is reduced, its map factors through $Z_{\mathrm{red}}$: on affine
opens, functions vanishing on the image pull back into every prime ideal and hence to zero. The
fibres of this factorization agree with the fibres already considered. Apply [lem-zl-finite-type-
fibre-image-dimension-bounds] to this finite-type map with $d=\dim Z$ and $n=0$ to get $g\leq\dim
Z$; the image inequality for $A\to A^\vee$ gives $\dim Z\leq g$. A proper closed subset of the
irreducible $g$-dimensional $A^\vee$ has dimension less than $g$: any chain in that closed subset
can be extended by the irreducible whole space. Hence $Z=A^\vee$. In particular, step 7 makes
$\phi_H$ an isogeny for every ample $H$.

11. For the converse let $L=\mathcal O_A(F)$ with $F$ effective and suppose $\ker\phi_L$ finite.
Let $D=F_{\mathrm{red}}$ as a reduced closed subscheme and $S=\operatorname{Stab}_A(D)$, which
exists by [lem-sfb-closed-translation-stabilizer]. The group $C=(S_{\mathrm{red}})^0$ is an
abelian subvariety by [lem-sfb-abelian-closed-subgroup-reduced-component]. The Cartier-divisor
clause of the stabilizer auxiliary gives $\mu^*F=p_1^*F$ on $A\times C$. Consequently $\mu^*L\cong
p_1^*L$; restricting this isomorphism along $0\times C$ identifies $L|_C$ with the constant line
$0^*L$, so the normalized family $N_L|_{A\times C}$ is trivial. Representability gives
$\phi_L|_C=0$. The closed immersion $C\to A$ therefore factors through the finite scheme-theoretic
kernel; hence $\dim C=0$. The closed-subgroup auxiliary now makes $S$ finite.

12. Steps 2–3, proved using [thm-sc-theorem-of-cube], identify $[t_a^*L\otimes L^{-1}]$ with
$\phi_L(a)$ and make $\phi_L$ additive. Thus the class of $t_a^*L\otimes t_b^*L\otimes
t_{-a-b}^*L\otimes L^{-\otimes3}$ is $\phi_L(a)+\phi_L(b)+\phi_L(-a-b)=0$, so by the representing
property of [lem-sfb-projective-picard-identity-representability] (over $T=\operatorname{Spec}k$)
that sheaf is trivial up to a constant line. Over $k$ any constant line is trivial, so
$t_a^*L\otimes t_b^*L\otimes t_{-a-b}^*L\cong L^{\otimes3}$. Thus the sum of the three translated
effective divisors is a member of $|L^{\otimes3}|$. Given $x\in A(k)$, first choose $a$ so
$t_a^*F$ does not contain $x$. Then choose $b$ avoiding the two proper translated supports that
would make $t_b^*F$ or $t_{-a-b}^*F$ contain $x$. Each choice is possible because $A$ is
irreducible by [lem-sc-abelian-variety-characterization]. Every nonempty avoiding open in the
smooth variety $A$ has a $k$-point by [lem-pc-rational-points-dense]. This proves that
$L^{\otimes3}$ is generated by global sections: for any point choose a closed specialization using
[lem-sc-lft-over-field-jacobson-space]; a section nonvanishing at that specialization also does
not vanish at the original point, since its nonvanishing locus is open. The same argument applies
when $F=0$; then the translated divisors are empty. By [lem-fin-proper-coherent-finite-
dimensional], $V=H^0(A,L^{\otimes3})$ is finite dimensional. The quotient $V\otimes\mathcal
O_A\twoheadrightarrow L^{\otimes3}$ gives $f:A\to\mathbf P(V)$ and $f^*\mathcal O(1)\cong
L^{\otimes3}$ by [lem-trf-projective-bundle-quotient-geometry].

13. If $x,y\in A(k)$ have $y-x\notin S(k)$, some translate of $D$ contains $x$ but not $y$. To see
this, the parameters of translates through $x$ and through $y$ are respectively $D-x$ and $D-y$
(since $x\in t_a^*D$ means $x+a\in D$). If the first were contained in the second, translation
would inject the finite set of its irreducible divisorial components into the same set:
containment between these components of equal dimension is equality. The injection is a
permutation, so the two reduced supports would be equal. Equality would mean $y-x\in S(k)$. The
resulting nonempty difference is an open subset of a reduced component and contains a $k$-point by
Jacobson density and the closed-point residue-field lemma. Fix such a translate $t_a^*F$. Choose
$b$ with neither $t_b^*F$ nor $t_{-a-b}^*F$ passing through $y$, by avoiding two proper closed
sets. The section with zero divisor their sum vanishes at $x$ and not at $y$, so $f(x)\ne f(y)$.
Fix a closed target point $z$. Its residue field is $k$ by [lem-weil-pbc-closed-point-residue-
field-base], so the closed points of $A_z$ are $k$-points of $A$. If $A_z$ is nonempty, choose one
such point $x$ by [lem-sc-lft-over-field-jacobson-space]. The separation just proved forces every
closed point of $A_z$ into the finite coset $x+S(k)$. Thus $A_z$ has finitely many closed points,
and [lem-sc-positive-dimensional-locally-algebraic-closed-points] rules out a positive-dimensional
irreducible component. Empty fibres already have dimension $-\infty$. The morphism $f$ is proper
by [lem-weil-pbc-proper-to-separated], since its source is proper and its target separated. By
[lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous], the set of target points whose fibres
have positive dimension is closed. If nonempty it contains a closed point by [lem-sc-lft-over-
field-jacobson-space], contrary to the preceding calculation. Thus every fibre has dimension at
most zero.

14. The morphism $f$ is proper by [lem-weil-pbc-proper-to-separated]. Its fibres are Noetherian
and zero-dimensional by step 13, so [lem-sc-zero-dim-noetherian-finite-discrete] makes them finite
discrete spaces. Since $f$ is of finite type and quasi-compact, [pqf-lem-qf-finitefibres] makes it
quasi-finite; [cor-pqf-proper-quasifinite-finite] now makes it finite. A finite morphism is affine
by [def-weil-finite-integral-morphism]. Since $\mathcal O_{\mathbf P(V)}(1)$ is ample, [lem-weil-
pbc-pullback-ample-invertible] makes $L^{\otimes3}=f^*\mathcal O(1)$ ample in the absolute sense.
The projective-space twist is very ample, hence ample; its standard affine nonvanishing charts
verify the absolute sense directly. Apply [lem-weil-pbc-ample-very-ample-immersion-affine-base] to
obtain an immersion from a positive power of $L^{\otimes3}$. This immersion is proper by [lem-
weil-pbc-proper-to-separated] and is a monomorphism, so [lem-pc-proper-monomorphism-closed] makes
it closed; the projection argument of step 7 then makes the complete linear system of that power a
closed immersion as well. Thus $L$ is ample in the definition [def-sc-ample]. Combining this
converse with steps 7 and 10 gives the effective Cartier divisor criterion, with finite scheme-
theoretic kernel and surjectivity exactly as stated.
-/
theorem IsAbelianVariety.exists_dual_polarization_calculus
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] :
    ∃ D : AbelianDualPoincareDatum A,
      IsAbelianVariety.dim D.dual = IsAbelianVariety.dim A ∧
      (∀ L : A.left.Modules, L.IsInvertible →
        ∃ φ : A ⟶ D.dual, (∀ ψ : A ⟶ D.dual, ClassifiesAbelianDifference D L ψ ↔ ψ = φ) ∧
          IsMonHom φ) ∧
      (∀ (L : A.left.Modules), L.IsInvertible →
        ∀ (φ : A ⟶ D.dual), ClassifiesAbelianDifference D L φ →
        ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ A,
          Nonempty
            ((Scheme.Modules.pullback (lift (𝟙 A) (toUnit A ≫ x ≫ φ)).left).obj D.poincare ≅
              (Scheme.Modules.pullback (lift (𝟙 A) (toUnit A ≫ x) ≫ μ[A]).left).obj L ⊗
                Scheme.Modules.dual L)) ∧
      (∀ (L : A.left.Modules), L.IsInvertible →
        ∀ (φ : A ⟶ D.dual), ClassifiesAbelianDifference D L φ →
        ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ A,
          ClassifiesAbelianDifference D
            ((Scheme.Modules.pullback (lift (𝟙 A) (toUnit A ≫ b) ≫ μ[A]).left).obj L) φ) ∧
      (∀ (B : Over (Spec (.of k))) [GrpObj B] [IsAbelianVariety B]
        (E : AbelianDualPoincareDatum B) (a : B ⟶ A), IsMonHom a →
        ∃ aDual : D.dual ⟶ E.dual,
          (∀ g : D.dual ⟶ E.dual,
            Nonempty
              ((Scheme.Modules.pullback (a ▷ D.dual).left).obj D.poincare ≅
                (Scheme.Modules.pullback (B ◁ g).left).obj E.poincare) ↔ g = aDual) ∧
          IsMonHom aDual ∧
          ∀ (L : A.left.Modules), L.IsInvertible →
            ∀ (φA : A ⟶ D.dual) (φB : B ⟶ E.dual),
              ClassifiesAbelianDifference D L φA →
              ClassifiesAbelianDifference E ((Scheme.Modules.pullback a.left).obj L) φB →
              φB = a ≫ φA ≫ aDual) ∧
      Nonempty
        ((Scheme.Modules.pullback (ι[A] ▷ D.dual).left).obj D.poincare ≅
          (Scheme.Modules.pullback (A ◁ ι[D.dual]).left).obj D.poincare) ∧
      (∀ (L : A.left.Modules), L.IsInvertible →
        ∀ (φ : A ⟶ D.dual), ClassifiesAbelianDifference D L φ →
          ClassifiesAbelianDifference D ((Scheme.Modules.pullback ι[A].left).obj L) φ) ∧
      (∀ (J : A.left.IdealSheafData), J.IsInvertible →
        ∀ (φ : A ⟶ D.dual), ClassifiesAbelianDifference D (Scheme.Modules.dual J.toModules) φ →
          (IsAmple A.hom (Scheme.Modules.dual J.toModules) ↔ IsIsogeny φ)) := by
  sorry

end AlgebraicGeometry
