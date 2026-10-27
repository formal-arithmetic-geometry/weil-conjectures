module

public import Sheaf.AlgebraicGeometry.GroupSchemeLinearization
public import Sheaf.AlgebraicGeometry.ProjectiveLinearQuotient
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.LocallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.NoetherianSpace
import Sheaf.RepresentationTheory.PGLGeometricReductivity
import Sheaf.AlgebraicGeometry.ProjectivePolarizationSectionAlgebra
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.DeligneLaumon.IrreducibleFibreDimensionLowerBound

/-! # Semistable orbit closures and orbit dimensions

Source: Morrison, arXiv:0810.2340, §3.3, Corollary 11(3), p.17;
Milne, Algebraic Groups, Propositions 1.65--1.66; MFK, GIT, Chapter 1.
(blueprint: lem-sfb-git-orbit-closure-dimension)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits CartesianMonoidalCategory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.GITOrbitGeometry

variable {k : Type u} [Field k] {G : Grp (Over (Spec (.of k)))}
variable {Z : Over (Spec (.of k))}

/-- The orbit map, using G × Spec k, canonically G, as its source.
This uses the existing action, on all scheme points rather than only rational points.
Source: Milne, p.27 (blueprint: lem-sfb-git-orbit-closure-dimension). -/
def orbitMap (a : ModObj G.X Z) (z : PGLLinearization.fieldTest k k ⟶ Z) :
    G.X ⊗ PGLLinearization.fieldTest k k ⟶ Z :=
  GroupSchemeLinearization.act a _ (fst _ _) (snd _ _ ≫ z)

/-- The full image of the orbit map, with its subspace topology when used as a type.
Source: Milne, p.27 (blueprint: lem-sfb-git-orbit-closure-dimension). -/
def orbit (a : ModObj G.X Z) (z : PGLLinearization.fieldTest k k ⟶ Z) : Set Z.left :=
  Set.range (orbitMap a z).left

/-- The semistable locus as the union of nonvanishing loci of positive-degree
invariant sections, using exactly the dependency's scheme-valued invariance predicate.
Source: Morrison §2.1; MFK, Chapter 1
(blueprint: lem-sfb-git-orbit-closure-dimension). -/
def semistableLocus {a : ModObj G.X Z} {A : Z.left.Modules}
    (D : GroupSchemeLinearization.Linearization a A) : Set Z.left :=
  {x | ∃ (n : ℕ) (_ : 0 < n) (s : Scheme.Modules.SectionRingComponent A n),
    D.IsInvariant n s ∧ x ∈ Scheme.Modules.nonvanishingLocus (A.tensorPow n) s}

/-- The same orbit viewed inside the semistable locus, with the induced topology.
Source: Morrison §3.3; MFK, Chapter 1
(blueprint: lem-sfb-git-orbit-closure-dimension). -/
def semistableOrbit {a : ModObj G.X Z} {A : Z.left.Modules}
    (D : GroupSchemeLinearization.Linearization a A)
    (z : PGLLinearization.fieldTest k k ⟶ Z) : Set (semistableLocus D) :=
  Subtype.val ⁻¹' orbit a z

end AlgebraicGeometry.GITOrbitGeometry

namespace AlgebraicGeometry

/-- Every semistable PGL orbit is locally closed, satisfies the stabilizer dimension
formula, and has exactly one closed orbit in its semistable closure. Boundary orbits
in the ambient scheme have smaller dimension. The PGL hypothesis uses the
already recorded scalar-quotient definition; Z and its stabilizers need not be reduced.
The additive dimension equality is equivalent to the stated subtraction formula,
since all three nonempty finite-type schemes have finite nonnegative dimensions.

Source: Morrison, arXiv:0810.2340, §3.3, Corollary 11(3), p.17;
Milne, Propositions 1.65--1.66; MFK, GIT, Chapter 1.
(blueprint: lem-sfb-git-orbit-closure-dimension)

Proof, following the DAG steps:
1. First obtain a projective polarization in the embedding convention needed below. The
projective-to-proper theorem makes $Z$ proper over $k$. The ample-to-very-ample immersion
theorem, over $\operatorname{Spec}k$, gives $i:Z\to\mathbf P^n_k$ with $A^{\otimes d}\simeq
i^*\mathcal O(1)$ for some $d>0$. Projective space is separated (it is proper by the same
projective-to-proper theorem). The proper-to-separated-target theorem makes $i$ proper, so its
image is closed. The immersion-with-closed-image theorem therefore makes $i$ a closed immersion.
Thus the hypotheses of the projective-polarization section-algebra theorem apply to $(Z,A)$,
including when $Z$ is nonreduced. Dependencies: lem-kun-projective-implies-proper,
lem-weil-pbc-ample-very-ample-immersion-affine-base, lemma-nagata-proper-to-separated-target,
lem-weil-pbc-immersion-closed-image-closed-immersion.

2. Use the matrix model $G=D_+(\det)\subset\mathbf P(\operatorname{Mat}_r)$. Locally, a
projective invertible matrix has a generator which is an invertible matrix; changing that
generator multiplies it by a unit. Conversely invertible matrices modulo this scalar change glue
to the same projective matrix. These inverse descriptions identify this open scheme with
$\operatorname{PGL}_r$. The projective-polarization chart theorem applied to $\mathbf
P^{r^2-1}$, $\mathcal O(1)$ and the degree-$r$ determinant makes $G$ affine of finite type. Its
standard projective charts are polynomial rings localized at the nonzero determinant polynomial,
hence reduced domains; their pairwise intersections are nonempty principal opens. Consequently
$G$ is integral. The finite-type-over-Noetherian theorem makes $Z$ and $G$ Noetherian (a field
is Noetherian). The minimal-closed-subset theorem gives the descending-chain condition on their
closed subsets: the members of an infinite strict descending chain would have no minimal member.
The compact-subsets theorem then makes every subset quasi-compact. In particular their open
subschemes have finite affine covers and remain finite type over $k$. Dependencies:
lem-sfb-projective-polarization-section-algebra, lem-weil-pbc-finite-type-over-noetherian,
lem-sfb-noetherian-space-compact-subsets, lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.

3. We will use rational-point detection as follows. In a nonempty locally closed subscheme of a
finite-type $k$-scheme, choose a nonempty affine open $V$. It is quasi-compact and $T_0$, so the
closed-point theorem gives a closed point of $V$. The closed-point residue-field theorem makes
it $k$-rational. Thus every such nonempty locally closed subset has a $k$-point. In particular
$k$-points are dense: if the complement of their closure were nonempty, apply this argument to
that open complement. A nonempty fibre over a rational point also has a rational point, since it
is finite type over $k$. Dependencies: lem-sc-quasi-compact-kolmogorov-closed-point,
lem-weil-pbc-closed-point-residue-field-base.

4. Fix $z\in Z^{ss}(k)$ and write $a_z:G\to Z$, $g\mapsto gz$, and $O=a_z(|G|)$. Over affine
charts the coordinate map is finite type because generators over $k$ also generate over the
target algebra; quasi-compact inverse images are supplied by Step 2. Thus $a_z$ and its fibres
over rational points are finite type. Its image is constructible: over each affine open
$W\subset Z$, the inverse image has a finite affine cover by Step 2, and each chart maps to the
affine finite-type scheme $W$. Apply the affine Chevalley theorem to each of these finitely many
maps and take their union; this gives constructibility on every member of a finite affine cover
of $Z$. Let $C=\overline O$ in $Z$, with the reduced induced closed subscheme structure. It is
finite type, since its affine coordinate rings are quotients of those of $Z$. It is irreducible:
a cover of $C$ by two closed subsets pulls back to a cover of the irreducible $G$, so one
contains $O$, hence all of $C$. For each $g\in G(k)$, the identity $g a_z(h)=a_z(gh)$ shows
$gO=O$ and therefore $gC=C$. Dependencies: lem-wf-affine-constructible-open,
lem-weil-pbc-reduced-induced-closed-subscheme.

5. Choose a nonempty affine open $W\subset C$. The constructible set $O\cap W$ is dense in $W$,
so the constructible-open theorem supplies a nonempty open $V\subset C$ contained in $O$. Choose
$v\in V(k)$ by Step 3; its fibre under $a_z$ is nonempty, so Step 3 also gives $h\in G(k)$ with
$hz=v$. Put $T=\bigcup_{g\in G(k)}gV$, an open subset of $C$ contained in $O$. It contains all
rational points of $O$: any such point lifts to $G(k)$ by the same fibre argument, and hence is
a translate of $v$. The closed subset $a_z^{-1}(C\setminus T)$ of $G$ has no rational point;
Step 3 makes it empty. Thus $O=T$ is open in its closure, proving local closedness. This
argument applies to every rational point of $Z$, without using semistability. Dependencies:
lem-wf-affine-constructible-open.

6. The scheme-theoretic stabilizer $H=G_z$ is the fibre $a_z^{-1}(z)$: for every $k$-algebra $R$
its points are exactly those $h\in G(R)$ with $hz_R=z_R$. Since $Z$ is separated, this equalizer
with the constant map is a closed subscheme of $G$: it is the pullback of the closed diagonal of
$Z$ along $g\mapsto(gz,z)$, and the closed-immersion base-change theorem makes it closed. It is
a subgroup by $hz=z$, $h'z=z\Rightarrow hh'z=z$ and $hz=z\Rightarrow h^{-1}z=z$. In particular
$H$ is finite type. For $g\in G(k)$, left multiplication by $g$ gives an isomorphism $H\simeq
a_z^{-1}(gz)$, with inverse left multiplication by $g^{-1}$: over every $R$, $(gh)z=gz$ if and
only if $hz=z$. This identifies the fibre schemes, including all nilpotents. Dependencies:
def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change.

7. Apply the irreducible fibre-dimension theorem to $a_z:G\to Z$. Both schemes are finite type,
and $G$ is nonempty irreducible. It gives $n\ge0$ with $\dim G=\dim C+n$ and a nonempty dense
open of $G$ where the local topological fibre dimension is $n$. Choose a rational $g$ in this
open by Step 3. By Step 6 its fibre at $gz$ is $gH$, with $g$ corresponding to the identity of
$H$. The rational-point stalk/topological-dimension comparison identifies this local fibre
dimension with $\dim\mathcal O_{H,e}$. The group-identity dimension theorem gives $\dim\mathcal
O_{H,e}=\dim H$, without smoothness or reducedness of $H$. Finally $O$ is a nonempty open in the
irreducible locally finite-type $C$, so the open-dimension theorem gives $\dim O=\dim C$.
Finite-type dimensions are finite. Consequently $\dim(Gz)=\dim G-\dim G_z$ as an equality of
finite integers. Dependencies: lem-zl-irreducible-fibre-dimension-lower-bound,
lem-ag-rational-point-stalk-topological-local-dimension, lem-ag-group-identity-local-dimension,
lem-sc-dimension-locally-algebraic, lem-kun-dimension-finite-type.

8. Put $S=Z^{ss}(A)$ and $C_S=C\cap S$. By definition $S$ is the union of the nonvanishing opens
of positive-degree invariant sections of powers of $A$. The linearization makes each such open
invariant, so $O\subset S$, and likewise $Gy\subset S$ for every $y\in S(k)$. Thus $C_S$ is the
closure of $O$ in $S$, is irreducible, and $O$ is open in $C$ (Step 5) and in $C_S$. Set
$B=C\setminus O$, the boundary of $O$ in its closure in $Z$; its part $B\cap S=C_S\setminus O$
is the boundary inside $S$. $B$ is closed in $C$, proper, and stable under $G(k)$. For $y\in
B(k)$, $a_y^{-1}(C)$ is closed in $G$ and contains $G(k)$, as $gC=C$; density from Step 3 makes
it all of $G$. Since $O$ is open in $C$, $a_y^{-1}(B)=G\setminus a_y^{-1}(O)$ is closed in $G$,
and it contains $G(k)$ as $gB=B$; so it is all of $G$ and $Gy\subset B$. For any chain of
irreducible closed subsets of $B$ (closed in $C$, as $B$ is), adjoining the irreducible $C$ adds
a strict step. Therefore $\dim B<\dim C$ when $B$ is nonempty, and $\dim C=\dim O$ by Step 7.
Since $O\subset C_S\subset C$, subspace monotonicity also gives $\dim C_S=\dim O$. Consequently
every orbit in $\overline{Gz}\setminus Gz$, with the closure taken in $Z$ or in $S$, has
dimension at most $\dim B<\dim O$. Subspace monotonicity here follows directly by taking
closures of a chain in the larger space: their intersections with the original subspace recover
the original chain, so all inclusions remain strict. Dependencies:
def-kun-topological-krull-dimension.

9. The set of dimensions of orbits of rational points of $C_S$ is a nonempty set of nonnegative
integers (it contains $\dim O$). Choose $y\in C_S(k)$ whose orbit has least dimension. If $Gy$
were not closed in $S$, its boundary in its closure in $S$ would be a nonempty locally closed
subset of a finite-type scheme and hence would contain $w\in S(k)$ by Step 3. Its closure lies
in the closed subset $C_S\subset S$, so $w\in C_S$. Applying Step 8 with $y$ in place of $z$
gives $\dim Gw<\dim Gy$, contradicting minimality. Thus $C_S$ contains an orbit closed in $S$.
Dependencies: .

10. For uniqueness suppose $O_1=Gy_1$ and $O_2=Gy_2$ are distinct orbits in $C_S$ closed in $S$.
Semistability gives invariant sections $s_i\in H^0(Z,A^{\otimes d_i})$, $d_i>0$, nonzero at
$y_i$. Replace them by $s_1^{d_2}$ and $s_2^{d_1}$ to give both degree $d_1d_2$. At each of the
two rational points the equation $s_1^{d_2}+c s_2^{d_1}=0$ excludes at most one $c\in k$, since
the relevant one of these sections is nonzero. An algebraically closed field is infinite: if it
were finite, $1+\prod_{a\in k}(T-a)$ would have no root. Choose $c$ avoiding both exceptions and
put $s=s_1^{d_2}+c s_2^{d_1}$. Then $U=Z_s$ is an invariant affine finite-type open by Step 1
and the polarization chart theorem, and it contains $y_1,y_2$. It also contains $z$: otherwise
the invariant closed zero set of $s$ would contain $O$ and $C$, contradicting $y_1\in C\cap U$.
Invariance then gives $O\subset U$. Dependencies:
lem-sfb-projective-polarization-section-algebra.

11. Write $U=\operatorname{Spec}E$. Each $O_i$ is closed in $U$, because it is closed in $S$ and
$U\subset S$. Give it the reduced induced closed structure $Y_i=\operatorname{Spec}(E/I_i)$,
with $I_i$ radical. Distinct orbits have disjoint rational points. If $Y_1\cap Y_2$ were
nonempty, Step 3 would give a rational point in it. Its two nonempty orbit-map fibres would have
rational points, making $y_1$ and $y_2$ translates of one another, a contradiction. Thus
$Y_1\cap Y_2=\varnothing$, whence $I_1+I_2=E$: a proper sum would lie in a maximal ideal and
give a point in the intersection. The Chinese remainder theorem now makes $E\to E/I_1\times
E/I_2$ surjective. Dependencies: lem-weil-pbc-reduced-induced-closed-subscheme,
lem-pc-crt-ideal-quotient-product.

12. The quotient in Step 11 is equivariant for the full group scheme. Indeed $G$ and $Y_i$ are
reduced affine finite-type schemes over the algebraically closed $k$, so their product is
reduced by the reduced-product theorem. For $b\in I_i$, pull back $b$ along $G\times Y_i\to U$.
Its value at every pair $(g,y)\in G(k)\times Y_i(k)$ is $b(gy)=0$, because $O_i$ is an orbit.
The product vanishing principle therefore makes this pulled-back function zero. In coordinates
the composite $E\to E\otimes_k k[G]\to (E/I_i)\otimes_k k[G]$ kills $I_i$, which is exactly the
condition for the coaction to descend. The coactions consequently descend to each $E/I_i$ and to
their product; the quotient map is equivariant. This argument does not require $E$ reduced.
Dependencies: lem-wf-affine-product-reduced.

13. In $F=E/I_1\times E/I_2$, the element $b=(0,1)$ is invariant: the action preserves each of
the two factors and their scalar constants. Apply the PGL geometric-reductivity power-lifting
statement to the surjective equivariant map $E\twoheadrightarrow F$. Both are finitely generated
$k$-algebras (a finite product of the two quotients is generated by their generators and
$(1,0)$). It gives $N>0$ and $f\in E^G$ mapping to $b^N=b$. Thus $f$ is zero on $Y_1$ and one on
$Y_2$. Only the lifting of a power is used; exactness of taking invariants is not assumed.
Dependencies: lem-sfb-pgl-geometric-reductivity.

14. Set $a=f(z)\in k$. Invariance says that the pullback of $f$ along the orbit map $a_z:G\to U$
is the constant $a$: restrict the coaction identity $\rho(f)=f\otimes1$ at $z$. Hence $O$ lies
in the closed zero set $V(f-a)$ in $U$. Its closure in $U$ is $C\cap U$, so both $y_1,y_2$ lie
in that zero set. Evaluation at $y_1$ gives $a=0$, and evaluation at $y_2$ gives $a=1$, a
contradiction. Thus the closed orbit from Step 9 is unique. Dependencies: .

15. Every construction above used only the underlying topology of $Z$ for orbit closures and
dimensions, but used the actual scheme fibres in Step 6. The stabilizer in Step 7 was never
replaced by its reduced subgroup: its identity local-ring dimension equals its full scheme
dimension by the cited group theorem even when it is nonreduced. In Step 12 reduced structures
were put only on the two closed orbit subsets to test invariance of their ideals; the ambient
algebra $E$ and the geometric-reductivity map were allowed to be nonreduced. Consequently all
conclusions proved above hold for nonreduced $Z$ and nonreduced stabilizers, as stated.
Dependencies: . -/
theorem semistable_orbit_closure_dimension
    {k : Type u} [Field k] [IsAlgClosed k] (r : ℕ) (hr : 2 ≤ r)
    (G : Grp (Over (Spec (.of k))))
    (hG : IsProjectiveLinearQuotient k r G.X)
    (Z : Over (Spec (.of k))) [IsHProjective Z.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (a : ModObj G.X Z) (A : Z.left.Modules) [A.IsInvertible]
    (hA : Scheme.Modules.IsAmple Z.left A)
    (D : GroupSchemeLinearization.Linearization a A)
    (z : PGLLinearization.fieldTest k k ⟶ Z) (hz : D.IsSemistable k z) :
    IsLocallyClosed (GITOrbitGeometry.orbit a z) ∧
    topologicalKrullDim (GITOrbitGeometry.orbit a z) +
        topologicalKrullDim (GroupSchemeLinearization.stabilizer a k z) =
      topologicalKrullDim G.X.left ∧
    (∃! O : Set (GITOrbitGeometry.semistableLocus D),
      (∃ y : PGLLinearization.fieldTest k k ⟶ Z,
        D.IsSemistable k y ∧ O = GITOrbitGeometry.semistableOrbit D y) ∧
      IsClosed O ∧ O ⊆ closure (GITOrbitGeometry.semistableOrbit D z)) ∧
    (∀ y : PGLLinearization.fieldTest k k ⟶ Z,
      GITOrbitGeometry.orbit a y ⊆
        closure (GITOrbitGeometry.orbit a z) \ GITOrbitGeometry.orbit a z →
      topologicalKrullDim (GITOrbitGeometry.orbit a y) <
        topologicalKrullDim (GITOrbitGeometry.orbit a z)) := by
  sorry

end AlgebraicGeometry
