module

public import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Sheaf.AlgebraicGeometry.ProperStability
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModelExistence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.AbelianVariety.PicardZeroCohomology
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Sheaf.AlgebraicGeometry.CoherentFiniteSupportSkyscrapers
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.CoherentSupportPowerIdealKills
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.AlgebraicGeometry.Regular

/-! # The coherent Poincare transform of the structure sheaf

Source: Mumford, Abelian Varieties, III §13, pp.126–129, Corollary 1 p.129.
(blueprint: lem-sfb-poincare-coherent-transform)

The identity skyscraper is the ordinary module pushforward of the structure sheaf
of Spec k along the identity section. Its scalar action is therefore evaluation
at that section. The conclusion asserts existence, with no scalar normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u wP wB

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- The normalized Poincare module has derived direct image the reduced identity
skyscraper in degree dim A, in arbitrary characteristic, including dimension zero.

Source: Mumford, Abelian Varieties, III §13, pp.126–129, Corollary 1 p.129.
(blueprint: lem-sfb-poincare-coherent-transform).

Proof plan:
1. Put $B=A^\vee$ and $C=Rp_{2*}\mathcal P_A$. By [lem-sfb-abelian-polarization-calculus], $B$ is
an abelian variety of dimension $g$. The projection $p_2$ is proper by [lem-kun-proper-stability],
which also gives properness of the composite $A\times B\to B\to\operatorname{Spec}k$. The schemes
$B$ and $A\times B$ are proper over $k$, hence Noetherian, and $\mathcal P_A$ is coherent, by
[lem-trf-proper-field-invertible-coherent]. Moreover $p_2$ is flat: on affine product charts its
ring map is $D\to E\otimes_kD$, whose target is a free $D$-module after choosing a $k$-basis of
$E$. The line module $\mathcal P_A$ is locally the structure sheaf, so it too is flat over $B$ and
has relative Tor dimension zero. Thus
[lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect] makes $C$ perfect. By
[lem-pc-relatively-flat-canonical-module-base-change], its derived pullback by every $T\to B$ is
the derived direct image of the ordinary restricted Poincare module; this includes residue fields,
localizations and nonflat infinitesimal quotients.

2. For a closed point $b\ne e$ of $B$, the normalized fibre $\mathcal P_b$ is algebraically
trivial and nontrivial, by the representing property in [lem-sfb-abelian-polarization-calculus].
By [lem-weil-pbc-closed-point-residue-field-base], these closed points are $k$-points, since $B$
is of finite type over algebraically closed $k$. By [lem-sfb-abelian-picard-zero-cohomology] and
the base change in step 1, the derived fibre of $C$ at $b$ is zero. Apply
[lem-sc-perfect-finite-free-residue-model-existence] at $b$: all its ranks are zero, so $C$
vanishes on a neighbourhood of $b$. Each cohomology sheaf of the perfect complex $C$ is coherent.
Its support is closed by [lem-weil-pbc-finite-type-module-support-closed], and the density of
closed points [lem-sc-lft-over-field-jacobson-space] applied on $B\setminus\{e\}$ shows that this
support is contained in $\{e\}$. Thus $C$ is zero away from the identity.

3. At $e$, step 1 identifies the derived fibre with $R\Gamma(A,\mathcal O_A)$. By
[lem-sc-abelian-variety-characterization] and [lem-pc-h0-proper-variety] its degree-zero
cohomology is $k$. Cohomology is finite dimensional by
[lem-fin-proper-coherent-finite-dimensional] and zero above $g$ by
[lem-sc-noetherian-cohomology-above-dimension]; there is no negative cohomology. By
[lem-sc-perfect-finite-free-residue-model-existence] choose a finite free model on an affine
neighbourhood of $e$ with ranks equal to these fibre dimensions. Pass to $R=\mathcal O_{B,e}$ and
denote the resulting complex by $K$. It represents the local restriction of $C$, has terms only in
$[0,g]$ and $K^0=R$. Its differentials reduce to zero modulo $\mathfrak m$: each term modulo
$\mathfrak m$ already has the dimension of its cohomology, so both adjacent differential ranks
must be zero. By [lem-weil-pbc-smooth-scheme-over-field-regular] and
[lem-ag-group-identity-local-dimension], $R$ is regular local of dimension $g$, with residue field
$k$.

4. Let $D=\operatorname{Hom}_R^\bullet(K,R[0])$, with the usual cochain signs, so $D$ has terms in
$[-g,0]$. For every prime of $R$ other than $\mathfrak m$, $K$ localizes to an acyclic bounded
finite free complex, by step 2. Such a complex is split exact: starting at its last nonzero term,
split the surjection onto that free term and repeat on its projective kernel. Its dual is
therefore acyclic too. Consequently all cohomology of $D$ is supported at $\mathfrak m$. The
complex $D[-g]$ has terms in $[0,g]$, so [lem-sfb-regular-local-punctual-acyclicity] gives
$H^j(D)=0$ for $j<0$; its positive cohomology is zero by its shape. Thus $D$ is a finite free
resolution of $M=H^0(D)=\operatorname{coker}(D^{-1}\to D^0)$. Since $D^0=R$ and the matrix entries
lie in $\mathfrak m$, write $M=R/I$ for an ideal $I\subseteq\mathfrak m$.

5. The nonzero cyclic module $R/I$ has support only at $\mathfrak m$. Apply
[lem-weil-pbc-coherent-support-power-ideal-kills] on $\operatorname{Spec}R$ with the coherent
sheaf associated to $R/I$ and the ideal $\mathfrak m$. We obtain $\mathfrak m^N\subseteq I$ for
some $N\geq1$. Set $T=\operatorname{Spec}(R/I)$ and let $j:T\to B$ be the local morphism. The
maximal ideal of $R/I$ is nilpotent, and its residue field is $k$. No assertion that $T$ is
reduced is being made.

6. For any $R$-algebra $Q$, finite freeness gives the natural identity
$$H^0(K\otimes_RQ)=\ker(K^0\otimes_RQ\to K^1\otimes_RQ)=\operatorname{Hom}_R(R/I,Q).$$ Indeed the
right side is exactly the kernel obtained by applying $\operatorname{Hom}_R(-,Q)$ to $D^{-1}\to
D^0\to R/I\to0$; $K$ has no negative term. The affine derived-category equivalence
[lem-pc-affine-qcoh-derived-equivalence] and the base-change comparison
[lem-pc-relatively-flat-canonical-module-base-change] identify the left side, for $Q=R/I$, with
$H^0(A\times_kT,\mathcal P_T)$. The identity of $R/I$ therefore gives a section $s$. Its reduction
at the closed point of $T$ is nonzero: under the same kernel identity it is the nonzero quotient
$R/I\to k$, represented by $1\in K^0\otimes_Rk=k$. Hence $s$ reduces to a nonzero constant section
of $\mathcal O_A$.

7. The section $s$ trivializes $\mathcal P_T$. To check this, trivialize the line module locally
on $A\times T$ and write $s$ as a scalar $u$. Its reduction modulo the nilpotent ideal $\mathfrak
m(R/I)$ is a unit, since the reduced section on $A$ is a nonzero constant. A lift of its inverse
makes $u$ invertible by the finite geometric-series inverse for $1+v$ with $v$ nilpotent. Thus
$\mathcal O_{A\times T}\xrightarrow{s}\mathcal P_T$ is an isomorphism. Restricting $s$ to the
identity section of $A$ gives a unit in $R/I$; divide by it to respect the fixed rigidification.
Now [lem-sfb-abelian-polarization-calculus] identifies $j:T\to B$ with the constant identity map,
since their rigidified families are isomorphic. On local rings, the quotient $R\to R/I$ must
consequently factor through $R/\mathfrak m=k$. Hence $\mathfrak m\subseteq I$, and together with
$I\subseteq\mathfrak m$ this proves $I=\mathfrak m$. In particular the dual complex $D$ resolves
the reduced residue field, rather than a thickening.

8. Choose $g$ generators $x_1,\ldots,x_g$ of $\mathfrak m$. They form a regular sequence by
[lem-weil-pbc-regular-local-generators-regular-sequence], hence a Koszul-regular sequence by
[lem-weil-pbc-regular-sequence-koszul-regular]. Its Koszul complex resolves $k$. Reindex $D$ as
the nonnegative chain resolution with degree $n$ equal to $D^{-n}$. By
[lem-sfb-projective-resolution-homotopy-equivalence] it is homotopy equivalent to the augmented
Koszul resolution. Dualizing these chain maps and homotopies gives a homotopy equivalence between
their dual cochain complexes; finite free double duality (with the standard cochain evaluation
signs) identifies the dual of $D$ with $K$. By [lem-sc-koszul-regular-sequence-dual-complex],
therefore, $$K\simeq\bigwedge_k^g\operatorname{Hom}_k(\mathfrak m/\mathfrak m^2,k)[-g].$$ The
chosen parameters give a basis of $\mathfrak m/\mathfrak m^2$, so the displayed determinant is a
one-dimensional $k$-space; choosing a nonzero basis identifies it with $k$. Thus $K\simeq k[-g]$
in $D(R)$. When $g=0$, the parameter list is empty, $R=k$ and the determinant is $k$ in degree
zero, so the same argument applies.

9. By step 2 every cohomology sheaf of $C$ is supported at $e$. The local computation in step 8
gives $\mathcal H^i(C)_e=0$ for $i\ne g$ and $\mathcal H^g(C)_e\cong k$ as $R$-modules, with
scalar action through $R\to k$. Hence $\mathcal H^i(C)=0$ for $i\ne g$. Apply
[lem-trf-coherent-finite-support-skyscrapers] to $\mathcal H^g(C)$: its singleton support and
stalk identify it with the module skyscraper $e_*k$, with precisely the evaluation action in the
statement. Finally [lem-sf-derived-concentrated-single] yields $$Rp_{2*}\mathcal
P_A=C\simeq\mathcal H^g(C)[-g]\simeq e_*k[-g].$$ The only arbitrary choice is a basis of the
one-dimensional determinant; the item asserts existence of an isomorphism, not a canonical scalar
normalization. All inputs hold in arbitrary characteristic.
-/
theorem IsAbelianVariety.poincare_coherent_transform
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (D : AbelianDualPoincareDatum A)
    [HasDerivedCategory.{wP}
      (SheafOfModules.{u} (moduleRings (A ⊗ D.dual).left.toRingedSpace))]
    [HasDerivedCategory.{wB}
      (SheafOfModules.{u} (moduleRings D.dual.left.toRingedSpace))] :
    Nonempty
      ((RingedSpace.derivedModuleDirectImage
          (snd A D.dual).left.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (A ⊗ D.dual).left.toRingedSpace)) 0).obj
            D.poincare) ≅
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings D.dual.left.toRingedSpace)) 0).obj
            ((RingedSpace.moduleDirectImage (η[D.dual]).left.toLRSHom.toShHom).obj
              (𝟙_ (Spec (.of k)).Modules)))⟦-(IsAbelianVariety.dim A : ℤ)⟧) := by
  sorry

end AlgebraicGeometry
