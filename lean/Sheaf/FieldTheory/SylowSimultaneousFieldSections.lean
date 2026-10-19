/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable
import WeilConjectures.RingTheory.SimpleFiltration

/-!
# Simultaneous field-factor sections after a prime-to-ell extension

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose II, proof of Theorem 3.2.1,
printed pp. 29--30, with Proposition 2.2.6, printed pp. 27--28
(blueprint: lem-per-sylow-simultaneous-field-sections).
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace FieldTheory

/-- A single finite prime-to-ell extension supplies a `K_i`-algebra homomorphism from
`F_i` into every maximal-ideal quotient of `K_i ⊗[K] K'`. Its algebra structure is the
canonical one: `a` maps to the class of `a ⊗ₜ 1`. The tensor product uses Mathlib's
commutative algebra multiplication `(a ⊗ₜ b) * (c ⊗ₜ d) = (a * c) ⊗ₜ (b * d)`.
Only `K_i/K` is required to be separable; `F_i/K_i` may be inseparable, and the finite
index type may be empty.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose II, proof of Theorem 3.2.1,
printed pp. 29--30, with Proposition 2.2.6, printed pp. 27--28
(blueprint: lem-per-sylow-simultaneous-field-sections).

Proof (the ten steps of the DAG node):
1. If $I=\varnothing$, take $K\prime=K$; its degree is $1$ and the remaining quantifiers are
empty. Henceforth suppose $I$ is nonempty. Each $F_i/K$ is finite by degree multiplicativity for
$K\subseteq K_i\subseteq F_i$. In particular it is algebraic: powers of any element are linearly
dependent in its finite-dimensional $K$-vector space. Choose an algebraic closure $\Omega_0/K$
and, by the algebraic-embedding lemma, choose $K$-embeddings $F_i\to\Omega_0$. Restrict these
embeddings to $K_i$ so that the two maps in each tower remain compatible.
Uses: lem-weil-pbc-field-degree-multiplicativity, def-weil-algebraic-closure,
lem-weil-pbc-algebraic-extension-embeds-algebraically-closed.

2. Choose a $K$-basis $\mathcal B_i$ of each image of $F_i$ in $\Omega_0$. Let $E$ be the
$K$-span in $\Omega_0$ of the finite family of products $\prod_{i\in I}b_i$ with $b_i\in\mathcal
B_i$. Expanding $1$ in each basis shows that $1$ and every image $F_i$ lie in $E$. Expanding
each product $b_ic_i$ in $\mathcal B_i$ shows that $E$ is closed under multiplication. Thus $E$
is a finite-dimensional commutative $K$-algebra and a domain, since it is a subring of a field.
The finite-dimensional-domain lemma makes it a field. Apply the normal-closure lemma to $E/K$ to
obtain a finite normal extension $L/K$ containing these compatible copies of all $F_i$ and
$K_i$. Choose an algebraic closure $\Omega$ of $L$, and identify all these fields with their
images in it.
Uses: lem-weil-pbc-finite-dimensional-domain-is-field,
lem-weil-pbc-finite-extension-in-finite-normal-extension, def-weil-algebraic-closure.

3. Let $G=\operatorname{Aut}_K(L)$. It is finite, since it is a subset of the finite set of
$K$-embeddings $L\to L$. Choose an $\ell$-Sylow subgroup $P\subseteq G$: write $|P|=\ell^a$ and
$d=[G:P]$, with $\ell\nmid d$. Define $K\prime=L^P=\{x\in L:\sigma(x)=x\text{ for all }\sigma\in
P\}$. This is a subfield containing $K$ (the fixed-element equations are preserved by addition,
multiplication and inverse), finite-dimensional over $K$ as a $K$-subspace of $L$. The action of
$P$ on $L$ is faithful because $P$ is a subgroup of its automorphism group. The finite faithful
action theorem therefore gives $[L:K\prime]=|P|=\ell^a$.
Uses: lem-weil-pbc-finite-extension-finitely-many-embeddings,
lem-weil-pbc-sylow-subgroup-prime-index, lem-wf-finite-field-action-fixed-degree.

4. In characteristic $p>0$, apply the normal-degree-factor theorem to the finite normal
extension $L/K$ and the algebraic closure $\Omega$ chosen above. It gives $[L:K]=|G|p^c$ for
some $c\geq0$. Cosets partition the finite group $G$ into $d$ sets each of size $|P|$, so
$|G|=d|P|$. Degree multiplicativity in $K\subseteq K\prime\subseteq L$ and $[L:K\prime]=|P|$
give $|P|[K\prime:K]=d|P|p^c$, hence $[K\prime:K]=dp^c$. Both $d$ and $p$ are prime to $\ell$,
by the Sylow choice and the hypothesis $\ell\ne p$, respectively. Thus this degree is prime to
$\ell$.
Uses: lem-exc-normal-field-degree-factors, lem-weil-pbc-field-degree-multiplicativity.

5. In characteristic $0$, put $S=L^G$. Since $L/K$ is algebraic normal, the fixed-field
purely-inseparable theorem gives $S/K$ purely inseparable; by the characteristic-zero clause of
that definition this says $S=K$. Apply the faithful finite action theorem to $G$ acting on $L$.
It gives $[L:K]=[L:S]=|G|$. As in the preceding step, $|G|=d|P|$ and degree multiplicativity
cancel $|P|=[L:K\prime]$ to give $[K\prime:K]=d$, again prime to $\ell$. This completes the
degree assertion in every characteristic.
Uses: lem-weil-pbc-normal-extension-fixed-field-purely-inseparable,
def-weil-pbc-finite-purely-inseparable-extension, lem-wf-finite-field-action-fixed-degree,
lem-weil-pbc-field-degree-multiplicativity.

6. Fix $i$ and any maximal-ideal quotient $q:K_i\otimes_KK\prime\twoheadrightarrow M$ in the
statement. The images of $e_j\otimes1$, for a $K$-basis $(e_j)$ of $K_i$, span $M$ over
$K\prime$: every tensor is a finite sum of pure tensors. Hence $M/K\prime$ is finite and
algebraic. Extend $K\prime\hookrightarrow\Omega$ to an embedding $u:M\hookrightarrow\Omega$ by
the algebraic-embedding lemma. For $x\in K_i$, its minimal polynomial over $K$ splits in $L$
because the copy $K_i\subset L$ of step 2 lies in the normal extension $L/K$. The element
$u(q(x\otimes1))$ is another root of that same polynomial, so belongs to $L$: in the field
$\Omega$, a product of linear factors vanishes only if one factor vanishes. Also $u(q(1\otimes
b))=b\in K\prime$ for $b\in K\prime$. Surjectivity of $q$ and the finite-sum tensor description
now imply $u(M)\subseteq L$. Identify $M$ with this subfield of $L$; this retains its actual
$K_i$-map, which may differ from the initial copy of $K_i$ in $L$.
Uses: lem-weil-pbc-algebraic-extension-embeds-algebraically-closed,
def-weil-pbc-module-tensor-product, lem-weil-pbc-algebra-tensor-pushout-universal-property.

7. The finite $K\prime$-spanning set of $L$ is also an $M$-spanning set, so $L/M$ is finite.
Degree multiplicativity gives $\ell^a=[L:K\prime]=[L:M][M:K\prime]$. Thus $[L:M]$ divides
$\ell^a$. With the actual map $K_i\to M$ fixed in step 6, form the commutative $M$-algebra
$B=M\otimes_{K_i}F_i$, with the tensor multiplication and unit. Scalar-extension dimension gives
$\dim_M B=[F_i:K_i]=n_i$, where $\ell\nmid n_i$. In particular $B\ne0$. Every strict chain of
$B$-submodules of its regular module is a strict chain of $M$-subspaces, so has length at most
$n_i$ (dimension rises by at least one per inclusion). The definition of module length therefore
gives finite length of $B$ as a $B$-module. Apply the simple-filtration theorem to obtain
$0=B_0\subsetneq\cdots\subsetneq B_r=B$ with simple $B$-module quotients $Q_j=B_j/B_{j-1}$.
Uses: lem-weil-pbc-field-degree-multiplicativity,
lem-weil-pbc-algebra-tensor-pushout-universal-property, lem-pc-finrank-field-base-change,
def-weil-pbc-module-length, lem-weil-pbc-finite-length-module-simple-filtration.

8. For each simple quotient $Q_j$, choose $0\ne v_j\in Q_j$. The image of $B\to Q_j$, $b\mapsto
bv_j$, is a nonzero $B$-submodule, hence all of $Q_j$. Write $\mathfrak m_j$ for its kernel. The
induced bijection $B/\mathfrak m_j\to Q_j$ is $M$-linear. The ideal $\mathfrak m_j$ is maximal:
any ideal properly containing it has nonzero image in $Q_j$, hence image $Q_j$; choose $b$ in
that ideal with $bv_j=v_j$, so $1-b\in\mathfrak m_j$ and the ideal contains $1$. Thus
$N_j=B/\mathfrak m_j$ is a field and $[N_j:M]=\dim_M Q_j$. Extending a basis of $B_{j-1}$ to one
of $B_j$ gives $\dim_M B_j=\dim_M B_{j-1}+\dim_M Q_j$; telescoping gives
$n_i=\sum_{j=1}^r[N_j:M]$. If every summand were divisible by $\ell$, so would be $n_i$. Choose
a $j$ for which $\ell\nmid[N_j:M]$, and put $N=N_j$. This argument retains multiplicities and
works even when $B$ has nilpotents.
Uses: def-weil-pbc-simple-module.

9. The field $N/M$ is finite since it is a quotient of the finite-dimensional $M$-space $B$.
Extend the inclusion $M\hookrightarrow\Omega$ of step 6 to an embedding
$v:N\hookrightarrow\Omega$ by the algebraic-embedding lemma. The composite $F_i\to B\to
N\xrightarrow{v}\Omega$ is a $K$-field embedding. For each $x\in F_i$, its image is a root of
the minimal polynomial of $x$ over $K$. That polynomial splits in $L$, since the original copy
$F_i\subset L$ belongs to the normal extension of step 2; the same linear-factor argument as in
step 6 places this image in $L$. The image of $M$ is already contained in $L$. Every element of
$N$ is the image of a finite sum of pure tensors from $B$, so $v(N)\subseteq L$. Thus,
preserving the actual map from $M$, view $M\subseteq N\subseteq L$.
Uses: lem-weil-pbc-algebraic-extension-embeds-algebraically-closed,
def-weil-pbc-module-tensor-product, lem-weil-pbc-algebra-tensor-pushout-universal-property.

10. Degree multiplicativity in $M\subseteq N\subseteq L$ shows that $[N:M]$ divides $[L:M]$,
hence divides $\ell^a$ by step 7. By step 8 it is also prime to $\ell$, so $[N:M]=1$. Therefore
the structural inclusion $M\to N$ is an isomorphism: $1$ is a basis of the one-dimensional
$M$-space $N$, so each element lies in $M$. Compose $F_i\to B\to N$ with its inverse $N\to M$.
The tensor relation identifies the two maps from $K_i$ into $B$, and the inverse fixes $M$, so
this is a homomorphism of $K_i$-algebras for the exact $K_i\to M$ map of the chosen quotient.
Since $i$ and the maximal-ideal quotient $M$ were arbitrary, the same $K\prime$ gives every
required section.
Uses: lem-weil-pbc-field-degree-multiplicativity,
lem-weil-pbc-algebra-tensor-pushout-universal-property.
-/
theorem exists_primeTo_extension_simultaneous_field_sections
    (K : Type u) [Field K] (ell : ℕ) (hell : ell.Prime) (hchar : ell ≠ ringChar K)
    (I : Type t) [Finite I] (Ki : I → Type v) [∀ i : I, Field (Ki i)]
    [∀ i : I, Algebra K (Ki i)] [∀ i : I, FiniteDimensional K (Ki i)]
    [∀ i : I, Algebra.IsSeparable K (Ki i)]
    (Fi : I → Type w) [∀ i : I, Field (Fi i)] [∀ i : I, Algebra (Ki i) (Fi i)]
    [∀ i : I, FiniteDimensional (Ki i) (Fi i)]
    (hdegree : ∀ i : I, Nat.Coprime (Module.finrank (Ki i) (Fi i)) ell) :
    ∃ (K' : Type (max u v w)) (_ : Field K') (_ : Algebra K K'),
      FiniteDimensional K K' ∧ Nat.Coprime (Module.finrank K K') ell ∧
        ∀ (i : I) (m : Ideal (Ki i ⊗[K] K')), m.IsMaximal →
          Nonempty (Fi i →ₐ[Ki i] ((Ki i ⊗[K] K') ⧸ m)) := by
  sorry

end FieldTheory
