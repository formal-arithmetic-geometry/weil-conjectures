module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Additive Jordan decomposition and its linear compatibility laws

Source: Milne, Algebraic Groups (2017), preliminaries to Proposition 17.74, p.376;
additive versions of Theorem 9.11 and Propositions 9.13--9.15, pp.168--169.
(blueprint: lem-sfb-additive-jordan-linear-compatibility)

The predicate below describes a pair of parts without choosing any endomorphism.
Diagonalizability means that the eigenspaces span after extension to an algebraic closure.
The theorem supplies the unique pair, its polynomial expressions, and its compatibility
with intertwiners, tensor sums and perfect scalar extensions.
-/

@[expose] public section

universe u v w z

set_option autoImplicit false

namespace Module.End

/-- A commuting additive Jordan decomposition, with geometric semisimplicity expressed
by spanning eigenspaces over the algebraic closure. No polynomial membership is assumed.
Source: Milne, Algebraic Groups, preliminaries to Proposition 17.74, p.376.
(blueprint: lem-sfb-additive-jordan-linear-compatibility) -/
def IsAdditiveJordanDecomposition
    {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (A S N : Module.End k V) : Prop :=
  A = S + N ∧ Commute S N ∧
    (⨆ a : AlgebraicClosure k,
      Module.End.eigenspace (S.baseChange (AlgebraicClosure k)) a) = ⊤ ∧
    IsNilpotent N

/-- The additive Jordan decomposition exists uniquely, lies in the polynomial algebra,
and respects arbitrary intertwiners, tensor sums and extensions between perfect fields.
The tensor and scalar-extension clauses assert that the displayed candidate pair is
itself a Jordan decomposition; by the uniqueness clause these are precisely the parts.
Source: Milne, Algebraic Groups, p.376 and pp.168--169.
(blueprint: lem-sfb-additive-jordan-linear-compatibility)

Proof (the seven steps of the DAG node):

1. We first record explicitly how equality is detected after scalar extension. Choose a finite
basis $(e_i)_{i=1}^d$ of a $k$-space $U$, with coefficient maps $e_i^*:U\to k$. For any
extension $L/k$, the maps $\lambda\otimes u\mapsto(\lambda e_i^*(u))_i$ and
$(a_i)_i\mapsto\sum_i a_i\otimes e_i$ are inverse $L$-linear maps between $L\otimes_k U$ and
$L^d$, as checked on pure tensors by bilinearity. Thus $(1\otimes e_i)$ is a basis, dimension is
preserved, and extension of linear maps is injective: their matrices keep their entries under
the injective inclusion $k\hookrightarrow L$. Addition, composition, identity and powers commute
with extension, by evaluating on $\lambda\otimes u$. For a tensor of two finite-dimensional
spaces, finitely many tensors of basis vectors span by expansion, so it too is finite
dimensional. If any space in an assertion is zero, its endomorphism is the unique map, its
identity equals zero, and nilpotence has exponent one; all subsequent formulas still apply.

2. Apply [lem-sfb-polynomial-jordan-chevalley-decomposition] to $A$, obtaining $N=q(A)$ and
$S=p(A)$ with $A=N+S$, $N$ nilpotent and $S$ complement-semisimple. Polynomial expressions in
the same endomorphism commute: $A^iA^j=A^{i+j}=A^jA^i$ and expand the two finite polynomial
sums. By [lem-sfb-geometric-semisimplicity-field-extension], $S$ is geometrically semisimple.
Set $A_s=S$ and $A_n=N$; this proves existence and membership in $k[A]$. Conversely, suppose
$A=S'+N'$ with $S'N'=N'S'$, $S'$ geometrically semisimple and $N'$ nilpotent. The same
comparison makes $S'$ complement-semisimple. The uniqueness assertion of
[lem-sfb-polynomial-jordan-chevalley-decomposition] therefore identifies it with $(S,N)$. This
proves uniqueness for all commuting decompositions, without requiring their parts to be
polynomial a priori.

3. Let $K/k$ be an extension with $K$ perfect. The extended pair $S_K=1\otimes A_s$,
$N_K=1\otimes A_n$ sums to $1\otimes A$ and commutes by the pure-tensor formulas in step 1. If
$A_n^r=0$, then $N_K^r=1\otimes A_n^r=0$. By [lem-sfb-geometric-semisimplicity-field-extension],
$S_K$ is geometrically semisimple, hence complement-semisimple over the perfect field $K$. The
extended space is finite dimensional by step 1. Apply uniqueness in
[lem-sfb-polynomial-jordan-chevalley-decomposition] over $K$ to this pair and to the polynomial
decomposition of $1\otimes A$. This gives precisely the two scalar-extension equalities. In
particular they hold for an algebraic closure of $k$, which is perfect.

4. Here is the action of the semisimple part on primary spaces over an algebraically closed
field. Write $A=S+N$ for the pair already constructed, and fix $r\geq1$ with $N^r=0$. Choose an
eigenbasis $(v_i)$ for $S$, with $Sv_i=a_i v_i$. Since $SN=NS$, $N$ preserves each
$S$-eigenspace, so $(A-a_i)^r v_i=N^r v_i=0$. Thus each $v_i$ lies in $E_{a_i}(A)$ of
[lem-sfb-generalized-eigenspace-direct-sum]. Grouping a basis expansion by the finitely many
$a_i$ expresses every vector as a sum of vectors in these primary spaces. Uniqueness of primary
expansions in that cited statement shows that every vector of $E_a(A)$ is a combination of the
$v_i$ having $a_i=a$. Therefore $S$ acts as $a$ on $E_a(A)$, including primary spaces equal to
zero.

5. For $fA=Bf$, extend everything to one algebraic closure $\bar k$ of $k$. Step 3 identifies
the extended parts with the parts over $\bar k$. Induction on $n$ gives $(B-a)^n f=f(A-a)^n$, so
$f$ sends $E_a(A)$ into $E_a(B)$ for every $a\in\bar k$. Step 4 says that the two semisimple
parts act by the same scalar $a$ on these spaces; hence $fA_s=B_sf$ on each $E_a(A)$, and on the
whole space by the spanning assertion of [lem-sfb-generalized-eigenspace-direct-sum].
Subtracting from $fA=Bf$ gives $fA_n=B_nf$. The injectivity from step 1 descends both equalities
to $k$. No inverse of $f$, and no invertibility of $A$ or $B$, has been used.

6. On $V\otimes_k W$ set $S=A_s\otimes1+1\otimes B_s$ and $N=A_n\otimes1+1\otimes B_n$.
Evaluation on $v\otimes w$ gives $S+N=C$ and $SN=NS$: endomorphisms on different factors
commute, and on the same factor the given Jordan parts commute. Write $X=A_n\otimes1$,
$Y=1\otimes B_n$, with $A_n^r=B_n^t=0$ for $r,t\geq1$. Then $XY=YX$, $X^r=Y^t=0$. Distributively
expand $(X+Y)^{r+t}$ into words. Reordering each word gives $X^iY^{r+t-i}$, which vanishes
because either $i\geq r$ or $r+t-i\geq t$. Thus $N$ is nilpotent, with no division by factorials
in any characteristic.

7. To check the remaining property of the candidate $S$, extend to $\bar k$. The coefficient
formulas of step 1 identify $\bar k\otimes_k(V\otimes_k W)$ with $(\bar k\otimes_k
V)\otimes_{\bar k}(\bar k\otimes_k W)$: send $\lambda\otimes(v\otimes w)$ to $(\lambda\otimes
v)\otimes(1\otimes w)$ and send $(\lambda\otimes v)\otimes(\mu\otimes w)$ back to
$\lambda\mu\otimes(v\otimes w)$. Bilinearity checks both inverses. The geometric comparison
[lem-sfb-geometric-semisimplicity-field-extension] gives eigenbases $(v_i)$ and $(w_j)$ for the
extended $A_s,B_s$, with eigenvalues $a_i,b_j$. By [lem-sc-tensor-product-free-basis], applied
over $\bar k$ to these finite bases, the $v_i\otimes w_j$ form a basis. On this basis
$S(v_i\otimes w_j)=(a_i+b_j)(v_i\otimes w_j)$, so $S$ is geometrically semisimple. The candidate
pair from step 6 therefore is a commuting semisimple-nilpotent decomposition of $C$. Convert
geometric to complement semisimplicity by [lem-sfb-geometric-semisimplicity-field-extension] and
apply uniqueness in [lem-sfb-polynomial-jordan-chevalley-decomposition]. It yields $C_s=S$ and
$C_n=N$, as required. Repeated eigenvalue sums do not affect diagonalizability.
-/
theorem exists_additiveJordanDecomposition_compatibility
    {k : Type u} [Field k] [PerfectField k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : Module.End k V) :
    ∃ S N : Module.End k V,
      IsAdditiveJordanDecomposition A S N ∧
      S ∈ Algebra.adjoin k {A} ∧ N ∈ Algebra.adjoin k {A} ∧
      (∀ S' N' : Module.End k V, IsAdditiveJordanDecomposition A S' N' →
        S' = S ∧ N' = N) ∧
      (∀ (W : Type w) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
          (B T M : Module.End k W), IsAdditiveJordanDecomposition B T M →
        (∀ f : V →ₗ[k] W, f.comp A = B.comp f →
          f.comp S = T.comp f ∧ f.comp N = M.comp f) ∧
        IsAdditiveJordanDecomposition
          (TensorProduct.map A (LinearMap.id : Module.End k W) +
            TensorProduct.map (LinearMap.id : Module.End k V) B)
          (TensorProduct.map S (LinearMap.id : Module.End k W) +
            TensorProduct.map (LinearMap.id : Module.End k V) T)
          (TensorProduct.map N (LinearMap.id : Module.End k W) +
            TensorProduct.map (LinearMap.id : Module.End k V) M)) ∧
      (∀ (K : Type z) [Field K] [Algebra k K] [PerfectField K],
        IsAdditiveJordanDecomposition (A.baseChange K) (S.baseChange K) (N.baseChange K)) := by
  sorry

end Module.End
