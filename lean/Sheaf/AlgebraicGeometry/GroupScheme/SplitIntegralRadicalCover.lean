module

public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeReductiveCoverTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.Algebra.Field.ULift
import Sheaf.LinearAlgebra.RootDatumLatticeEmbedding
import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.CategoryTheory.Sites.Precoverage

/-! # Integral radical quotient and simply connected central cover

Source: Conrad, Reductive group schemes, Example 5.1.7, Theorem 5.3.1,
Corollary 5.3.3, Theorem 6.1.16, and Exercise 6.5.2(i).
(blueprint: lem-sfb-split-integral-radical-cover).

The base is the universe lift of Spec Z. The final quantifier takes every morphism
Spec R to this base, hence every ring base change, including the zero ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

open RelativeReductiveCover

/-- A split reductive integral group has a maximal central torus, a semisimple quotient,
and a split simply connected central cover of that quotient.

Source: Conrad, Reductive group schemes, Example 5.1.7, pp.138--139;
Theorem 5.3.1 and Corollary 5.3.3, pp.160--164; Theorem 6.1.16, p.196;
Exercise 6.5.2(i), p.235.
(blueprint: lem-sfb-split-integral-radical-cover)

Proof plan (the eight DAG steps):
1. Write $U=D_{\mathbf Z}(M)$ for the given split maximal torus of $H$. Apply
   [lem-sfb-integral-split-root-datum] to obtain the constant roots $\Phi$ and coroots, valid on
   every geometric fibre. Put $L=\mathbf Z\Phi$. The relative centre formula
   [lem-sfb-relative-reductive-centre-weight-kernel] gives the scheme-theoretic closed centre
   $$Z(H)=D_{\mathbf Z}(M/L)\subseteq U.$$ The latter lemma applies over $\mathbf Z$, a nonzero
   Noetherian ring, and its constant-support hypothesis is exactly supplied by the first citation.
   In particular this is an identity of group schemes, not merely of points over fields.
2. Set $A=M/L$, let $A_{\mathrm{tor}}$ be its subgroup of finite-order elements, and put
   $C=A/A_{\mathrm{tor}}$. The finitely generated abelian-group structure theorem makes
   $A_{\mathrm{tor}}$ finite and $C\simeq\mathbf Z^r$ for some $r\geq0$. The surjection
   $M\twoheadrightarrow A\twoheadrightarrow C$ induces a closed immersion $T=D_{\mathbf
   Z}(C)\hookrightarrow Z(H)$ by relative diagonalizable duality. Thus $T\simeq\mathbf G_m^r$ is
   central and closed in $H$ (in coordinates the two successive quotient maps are surjective). For
   any algebraically closed field $k$, a subtorus of $Z(H)_k=D_k(A)$ has character group free of
   finite rank. Its character map from $A$ kills $A_{\mathrm{tor}}$, so its inclusion factors
   through $D_k(C)=T_k$. Hence $T_k$ is the largest central subtorus. This elementary
   factorization uses the duality statement over $k$ and does not replace the centre by its
   reduction.
3. Apply [lem-sfb-relative-central-multiplicative-quotient] over $\mathbf Z$ to the closed central
   multiplicative-type subgroup $T\subseteq H$. It represents $Q=H/T$ by a reductive integral
   group, with kernel $T$, and makes $p:H\to Q$ faithfully flat and finitely presented and a
   represented fppf quotient. Formation of this quotient and the maximal torus $U/T$ commute with
   arbitrary base change. Put $N=\ker(M\to C)$. The relative diagonalizable quotient formula
   identifies $U/T=D_{\mathbf Z}(N)$; $N$ is free of finite rank by
   [lem-weil-subgroup-finite-free-abelian-group-free]. Therefore $Q$ has a split maximal torus.
   For every algebraically closed $k$, step 2 identifies $T_k$ with the largest central torus of
   $H_k$. By [lem-sfb-reductive-radical-quotient] this is its radical and $H_k/T_k$ is semisimple.
   The arbitrary-base-change clause of the relative quotient identifies this quotient with $Q_k$.
   Thus $Q$ is split semisimple.
4. Extract the root datum $(X,\Psi,X^\vee,\Psi^\vee)$ of the split semisimple group $Q$ by
   [lem-sfb-integral-split-root-datum]. Its roots span $V=X\otimes\mathbf Q$. Apply
   [lem-sfb-root-datum-lattice-embedding] with this datum. Since the root span is all of $V$, its
   complementary central space is zero. Its weight lattice $$P=\{v\in V:\langle
   v,\beta^\vee\rangle\in\mathbf Z\text{ for every }\beta\in\Psi\}$$ is free of finite rank, and
   $X\subseteq P$ with finite index: the lemma's map $j$ is precisely this inclusion because its
   root-space projection is the identity. Every root is in $X$, so the inclusion fixes all roots
   and the coroot restrictions agree.
5. Use the roots $\Psi\subset P$ and coroot functionals on $P$ induced by the rational coroots.
   They form a reduced root datum: the pairing is integral by the definition of $P$;
   $s_\beta(v)=v-\langle v,\beta^\vee\rangle\beta$ preserves $P$ since both $v$ and $\beta$ lie
   there and the coefficient is integral; the root-coroot permutations, finiteness of the
   reflection group and reducedness are those of the datum on $X$, acting on the same rational
   vector space. By [lem-sfb-integral-root-datum-isogenies], realize this datum by a split
   reductive integral group $S$ with maximal torus $D_{\mathbf Z}(P)$. The roots still span
   $P\otimes\mathbf Q=V$, and the full weight lattice computed from these coroots is $P$ itself.
   The two fibre criteria of [lem-sfb-integral-split-root-datum] therefore make $S$ semisimple and
   simply connected on every geometric fibre, exactly in the sense required in the item.
6. The finite-index inclusion $u:X\hookrightarrow P$ satisfies the isogeny theorem with $G_0=Q$,
   $G_1=S$ and the identity bijection of roots: $u(\beta)=\beta$ and restriction of the coroot on
   $P$ is the coroot on $X$. Thus [lem-sfb-integral-root-datum-isogenies] supplies a finite
   faithfully flat finitely presented homomorphism $\pi:S\to Q$ with closed central kernel
   $$F=D_{\mathbf Z}(P/X).$$ Since $P/X$ is finite, $\mathbf Z[P/X]$ is a free $\mathbf Z$-module
   on the finite basis $\{e_a:a\in P/X\}$. Thus $F$ is finite locally free, including at primes
   dividing its rank. In particular no prime-to-characteristic or reduced-kernel assumption has
   entered the construction.
7. Let $\mathbf Z\to B$ be any ring map. The first quotient and its kernel remain the represented
   fppf quotient by the arbitrary-base-change clause of
   [lem-sfb-relative-central-multiplicative-quotient]. The second map and its kernel remain
   faithfully flat, finitely presented and $D_B(P/X)$ by [lem-sfb-integral-root-datum-isogenies].
   To verify its quotient interpretation explicitly, pull back the singleton fppf cover $S_B\to
   Q_B$ along any point $q:V\to Q_B$. By [lem-trf-fppf-covering-base-change] it gives a cover of
   $V$ on which $q$ lifts to $S_B$. Two lifts $s_1,s_2$ have the same image exactly when
   $s_1^{-1}s_2\in F_B$, by the kernel equality. Consequently the fppf sheafification of $S_B/F_B$
   is $Q_B$. This proves the second exact sequence and its base-change assertion, with
   scheme-theoretic kernels throughout.
8. The chosen split tori remain products of $\mathbf G_m$ over $B$; $F_B$ has coordinate algebra
   $B[P/X]$, free on the same finite basis. Every geometric fibre over $B$ is obtained from an
   algebraically closed field equipped with a map from $\mathbf Z$, so the root-datum and fibre
   criteria already checked give the same semisimple and simply connected properties after this
   base change. These criteria are compatible with base change by
   [lem-sfb-integral-split-root-datum]. If $B$ is the zero ring the base scheme is empty and the
   assertions hold vacuously. For empty root data, $H$ is a torus, $T=H$ and $Q=S=1$; for a
   semisimple $H$, $C=0$ and $T=1$. Thus the allowed trivial cases introduce no exceptions.
-/
theorem splitIntegral_radical_cover
    (H T₀ B : Grp (Over (Spec (.of (ULift.{u} ℤ)))))
    (iT : T₀ ⟶ H) (iB : B ⟶ H) (j : T₀ ⟶ B)
    (hH : IsReductive H) (hT : IsSplitMaximalTorus iT)
    (hB : IsBorel iB) (hTB : j ≫ iB = iT) :
    ∃ (T Q S F : Grp (Over (Spec (.of (ULift.{u} ℤ)))))
      (i : T ⟶ H) (p : H ⟶ Q) (a : F ⟶ S) (π : S ⟶ Q) (r : ℕ),
      Nonempty (T ≅ relativeSplitTorus (Spec (.of (ULift.{u} ℤ))) r) ∧
      IsClosedImmersion i.hom.hom.left ∧ IsCentral i.hom.hom ∧
      IsSemisimple Q ∧ HasSplitMaximalTorus Q ∧
      IsSemisimple S ∧ HasSplitMaximalTorus S ∧ HasSimplyConnectedFibres S ∧
      IsClosedImmersion a.hom.hom.left ∧ IsCentral a.hom.hom ∧
      IsFinite F.X.hom ∧ Flat F.X.hom ∧ LocallyOfFinitePresentation F.X.hom ∧
      IsFppfGroupQuotient i p ∧ Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      LocallyOfFinitePresentation p.hom.hom.left ∧
      IsFppfGroupQuotient a π ∧ Flat π.hom.hom.left ∧ Surjective π.hom.hom.left ∧
      LocallyOfFinitePresentation π.hom.hom.left ∧
      ∀ (R : Type u) [CommRing R] (f : Spec (.of R) ⟶ Spec (.of (ULift.{u} ℤ))),
        Nonempty ((Over.pullback f).mapGrp.obj T ≅ relativeSplitTorus (Spec (.of R)) r) ∧
        IsClosedImmersion ((Over.pullback f).mapGrp.map i).hom.hom.left ∧
        IsCentral ((Over.pullback f).mapGrp.map i).hom.hom ∧
        IsReductive ((Over.pullback f).mapGrp.obj H) ∧
        IsSplitMaximalTorus ((Over.pullback f).mapGrp.map iT) ∧
        IsSemisimple ((Over.pullback f).mapGrp.obj Q) ∧
        HasSplitMaximalTorus ((Over.pullback f).mapGrp.obj Q) ∧
        IsSemisimple ((Over.pullback f).mapGrp.obj S) ∧
        HasSplitMaximalTorus ((Over.pullback f).mapGrp.obj S) ∧
        HasSimplyConnectedFibres ((Over.pullback f).mapGrp.obj S) ∧
        IsClosedImmersion ((Over.pullback f).mapGrp.map a).hom.hom.left ∧
        IsCentral ((Over.pullback f).mapGrp.map a).hom.hom ∧
        IsFinite ((Over.pullback f).mapGrp.obj F).X.hom ∧
        Flat ((Over.pullback f).mapGrp.obj F).X.hom ∧
        LocallyOfFinitePresentation ((Over.pullback f).mapGrp.obj F).X.hom ∧
        IsFppfGroupQuotient ((Over.pullback f).mapGrp.map i)
          ((Over.pullback f).mapGrp.map p) ∧
        Flat ((Over.pullback f).mapGrp.map p).hom.hom.left ∧
        Surjective ((Over.pullback f).mapGrp.map p).hom.hom.left ∧
        LocallyOfFinitePresentation ((Over.pullback f).mapGrp.map p).hom.hom.left ∧
        IsFppfGroupQuotient ((Over.pullback f).mapGrp.map a)
          ((Over.pullback f).mapGrp.map π) ∧
        Flat ((Over.pullback f).mapGrp.map π).hom.hom.left ∧
        Surjective ((Over.pullback f).mapGrp.map π).hom.hom.left ∧
        LocallyOfFinitePresentation ((Over.pullback f).mapGrp.map π).hom.hom.left := by
  sorry

end AlgebraicGeometry
