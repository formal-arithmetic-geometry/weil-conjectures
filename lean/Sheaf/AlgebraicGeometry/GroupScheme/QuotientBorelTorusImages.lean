module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomRationalPoints
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy

/-! # Borel subgroups and maximal tori under quotient homomorphisms

Source: Milne, Algebraic Groups (2017), Proposition 17.20, printed pp.357--358;
Theorem 5.39, printed p.108.
(blueprint: lem-sfb-quotient-borel-torus-images)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Images and lifts of Borel subgroups and maximal tori under a faithfully flat
homomorphism. A closed subgroup factorization with faithfully flat first arrow
identifies the scheme-theoretic image: on coordinate rings the first arrow is
injective, so the closed subgroup's ideal is exactly the kernel of the composite.
Thus the existential image representatives below specify the actual closed images,
including their nilpotent scheme structures. No kernel hypothesis is imposed.

Source: Milne, Algebraic Groups (2017), Proposition 17.20, pp.357--358, and
Theorem 5.39, p.108. (blueprint: lem-sfb-quotient-borel-torus-images)

Proof plan, following the seven steps of the DAG:

1. For every restriction of $f$ considered below, with codomain $D$ or an already constructed
closed image, [lem-sfb-affine-homomorphism-flat-image] supplies a factorization
$J\twoheadrightarrow I\hookrightarrow D$ with the first map faithfully flat. This factor is the
scheme-theoretic image: the coordinate algebra of $I$ injects into that of $J$ by [lem-weil-pbc-
faithfully-flat-universally-injective] applied to the module $F[I]$; hence the kernel of $F[D]\to
F[J]$ is exactly the defining ideal of $I$. In particular all the asserted restrictions onto
images are faithfully flat. For a Borel $B$ put $C=f(B)$. Apply [lem-sfb-solvable-normal-image-
geometry] to the faithfully flat map $B\to C$ with its normal subgroup $N=B$ and image $I=C$. Its
hypotheses require normality only inside $B$, which holds for $B$ itself. Thus $C$ is smooth,
connected and solvable.

2. Use [lem-sfb-algebraic-group-homogeneous-quotient] to form the separated finite-type quotients
$X=A/B$ and $Y=D/C$. The morphism $A\to D\to Y$ is invariant under right multiplication by $B$:
locally it sends $ab$ and $a$ to the same coset because $f(b)\in C$. The quotient kernel-pair
formula and [lem-weil-pbc-fpqc-representable-descent] therefore descend this map to $\bar f:X\to
Y$. It is surjective: for any geometric point of $Y$, first lift fpqc locally to $D$ and then
along the faithfully flat map $A\to D$; composition gives a local lift to $X$. Nonemptiness of the
necessary base changes follows from [lem-weil-pbc-faithfully-flat-base-change] and [lem-weil-pbc-
faithfully-flat-surjective-spectrum]. The scheme $X$ is proper by [lem-sfb-borel-quotient-proper-
geometry]. Consequently [lem-weil-pbc-image-universally-closed] makes $Y$ proper, since $Y$ is
separated and of finite type.

3. Here is the criterion of Proposition 17.19 in the case needed. Choose a smooth connected
solvable subgroup $E$ of $D$ of largest dimension; the trivial subgroup starts the nonempty
collection. By [lem-sfb-solvable-normal-subgroup-products], dimensions are bounded nonnegative
integers and a proper inclusion of smooth connected groups strictly increases dimension. Thus $E$
is Borel. Left multiplication of $D$ on itself descends to an action on $Y=D/C$ by the quotient
kernel-pair formula and [lem-weil-pbc-fpqc-representable-descent]; both action identities can be
checked after lifting a quotient section. The proper nonempty finite-type scheme $Y$ has an
$E$-fixed point by [lem-sfb-solvable-proper-fixed-point]. This point is represented by $d\in
D(F)$: lift the point fpqc locally using the quotient statement and then take a closed point in
its nonempty finite-type fibre; [lem-weil-pbc-closed-point-residue-field-base] identifies its
residue field with $F$. The quotient equality criterion says, on every $F$-algebra $R$, that
$d_R^{-1}E(R)d_R\subseteq C(R)$. Thus $d^{-1}Ed\subseteq C$ as subgroup schemes. Since $C$ is
smooth connected solvable, maximality of the Borel $d^{-1}Ed$ gives $C=d^{-1}Ed$. This proves that
every Borel image is Borel without changing the kernel hypotheses.

4. Choose one Borel $B_0$ of $A$ by the existence argument of step 3. Its image $C_0$ is Borel by
steps 1--3. Apply [lem-sfb-algebraic-group-homogeneous-quotient] and [lem-sfb-borel-quotient-
proper-geometry] to form the proper $D/C_0$. As in step 3, left multiplication descends to this
quotient. By [lem-sfb-solvable-proper-fixed-point], the target Borel $C_1$ fixes a point $dC_0$.
The same fibre and residue-field argument gives $d\in D(F)$. Fixedness over every algebra gives
$d^{-1}C_1d\subseteq C_0$; Borel maximality makes this equality, so $C_1=dC_0d^{-1}$. Since $D$ is
smooth, [lem-sfb-affine-group-homomorphism-image] applied to the given faithfully flat $f$
supplies $a\in A(F)$ with $f(a)=d$. Conjugation is a group-scheme automorphism, so $aB_0a^{-1}$ is
again maximal smooth connected solvable. The identity $f(a_R b a_R^{-1})=d_R f(b)d_R^{-1}$ after
every scalar extension identifies its scheme-theoretic image with $C_1$. Faithful flatness of the
restriction follows from step 1.

5. Let $T$ be maximal in $A$. Choose a smooth connected solvable subgroup containing $T$ of
largest dimension, starting with $T$ itself (a torus is commutative). The dimension bounds and
strict increase in [lem-sfb-solvable-normal-subgroup-products] make it a Borel $B$. Then $T$ is
maximal in $B$. Put $C=f(B)$, a Borel by steps 1--3. Since $F$ is algebraically closed it is
perfect. Apply [lem-sfb-perfect-solvable-unipotent-torus] to $B$ to obtain a smooth connected
normal unipotent $U$ with torus quotient $P=B/U$. By [lem-sfb-solvable-torus-complements], $T\to
P$ is an isomorphism. Form the image $V=f(U)\subseteq C$ by step 1. Apply [lem-sfb-unipotent-
normal-quotient-image] to $B\to C$ and $U$: $V$ is smooth connected normal unipotent. The quotient
$R=C/V$ is affine finite type and smooth connected by [lem-sfb-affine-normal-quotient-geometry].
Since $U$ maps to $V$, the quotient universal properties induce $g:P\to R$. The maps $B\to C$ and
$C\to R$ are surjective on $F$-points by [lem-sfb-affine-group-homomorphism-image]. Thus $g$ is
surjective on $F$-points (lift a point of $R$ to $B$ and then take its class in $P$). As $R$ is
smooth, that node also makes $g$ faithfully flat. Apply [lem-sfb-torus-homomorphism-image] with
source $P$, target $R$, image $I=R$ and closed immersion $\mathrm{id}_R$: $R$ is a torus. This
uses no reducedness of any kernel.

6. Let $S=f(T)\subseteq C$, with faithfully flat restriction as in step 1. It is a torus by [lem-
sfb-torus-homomorphism-image]. Tori are smooth and connected, so by the dimension bounds and
strict increase in [lem-sfb-solvable-normal-subgroup-products] a torus subgroup of $C$ containing
$S$ of largest dimension is a maximal torus $S_1$ of $C$ containing $S$. Apply [lem-sfb-solvable-
torus-complements] to $(C,V,R)$ from step 5: the restriction $S_1\to R$ is an isomorphism. The
composite $T\xrightarrow{\sim}P\xrightarrow{g}R$ is surjective on $F$-points by step 5; it is the
restriction to $T$ of $B\to C\to R$, so it factors through $S\subseteq S_1\xrightarrow{\sim}R$,
and $S(F)\to S_1(F)$ is surjective. Since $S_1$ is smooth, [lem-sfb-affine-group-homomorphism-
image] makes the inclusion $S\hookrightarrow S_1$ faithfully flat. Its coordinate-algebra map is
surjective by the affine characterization of [def-weil-closed-immersion] and injective by [lem-
weil-pbc-faithfully-flat-universally-injective]; hence $S=S_1$. Now $C$ is a Borel subgroup of
$D$, so by [lem-sfb-borel-maximal-torus-conjugacy] for $D$ it contains a torus $S'$ maximal in
$D$; $S'$ is a fortiori maximal in $C$. The conjugacy clause of the same node for the smooth
connected group $C$ gives $c\in C(F)$ with $S=cS'c^{-1}$. Conjugation by $c$ is an automorphism of
$D$ preserving inclusions of tori, so $f(T)=S$ is maximal in $D$.

7. Choose a maximal torus $T_0$ of $A$: by [lem-sfb-solvable-normal-subgroup-products] a torus
subgroup of $A$ of largest dimension exists (the trivial torus is one) and, tori being smooth
connected, it is maximal. Step 6 makes $S_0=f(T_0)$ maximal in $D$. For any maximal torus $S_2$ of
$D$, the conjugacy clause of [lem-sfb-borel-maximal-torus-conjugacy] for $D$ gives $d\in D(F)$
with $S_2=dS_0d^{-1}$. Lift $d$ to $a\in A(F)$ by [lem-sfb-affine-group-homomorphism-image], since
$f$ is faithfully flat and $D$ is smooth. Then $aT_0a^{-1}$ is maximal, as conjugation and its
inverse preserve inclusions of tori. For every $F$-algebra $R$ the identity $f(a_R t
a_R^{-1})=d_Rf(t)d_R^{-1}$ identifies its image subgroup scheme with $S_2$. The restriction is
faithfully flat by step 1. Together with step 4 this proves both image-surjectivity clauses,
including rank zero.
-/
theorem quotient_borel_torus_images {F : Type u} [Field F] [IsAlgClosed F]
    (A D : Grp (Over (Spec (.of F))))
    [IsAffine A.X.left] [IsAffine D.X.left]
    [LocallyOfFiniteType A.X.hom] [QuasiCompact A.X.hom]
    [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    [Smooth A.X.hom] [ConnectedSpace A.X.left]
    [Smooth D.X.hom] [ConnectedSpace D.X.left]
    (f : A ⟶ D) (hf : f.hom.hom.left.appTop.hom.FaithfullyFlat) :
    (∀ (B : Grp (Over (Spec (.of F)))) (iB : B ⟶ A),
      IsBorelGroupScheme iB.hom.hom →
      ∃ (C : Grp (Over (Spec (.of F)))) (iC : C ⟶ D) (r : B ⟶ C),
        IsBorelGroupScheme iC.hom.hom ∧ iB ≫ f = r ≫ iC ∧
        r.hom.hom.left.appTop.hom.FaithfullyFlat) ∧
    (∀ (C : Grp (Over (Spec (.of F)))) (iC : C ⟶ D),
      IsBorelGroupScheme iC.hom.hom →
      ∃ (B : Grp (Over (Spec (.of F)))) (iB : B ⟶ A) (r : B ⟶ C),
        IsBorelGroupScheme iB.hom.hom ∧ iB ≫ f = r ≫ iC ∧
        r.hom.hom.left.appTop.hom.FaithfullyFlat) ∧
    (∀ (T : Grp (Over (Spec (.of F)))) (iT : T ⟶ A),
      ReductiveTorusCentralizer.IsMaximalTorus iT →
      ∃ (S : Grp (Over (Spec (.of F)))) (iS : S ⟶ D) (r : T ⟶ S),
        ReductiveTorusCentralizer.IsMaximalTorus iS ∧ iT ≫ f = r ≫ iS ∧
        r.hom.hom.left.appTop.hom.FaithfullyFlat) ∧
    (∀ (S : Grp (Over (Spec (.of F)))) (iS : S ⟶ D),
      ReductiveTorusCentralizer.IsMaximalTorus iS →
      ∃ (T : Grp (Over (Spec (.of F)))) (iT : T ⟶ A) (r : T ⟶ S),
        ReductiveTorusCentralizer.IsMaximalTorus iT ∧ iT ≫ f = r ≫ iS ∧
        r.hom.hom.left.appTop.hom.FaithfullyFlat) := by
  sorry

end AlgebraicGeometry
