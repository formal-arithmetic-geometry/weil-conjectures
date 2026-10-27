module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Sheaf.RingTheory.FiniteSubcoalgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Sheaf.FieldTheory.FiniteExtensionTensorAlgebraicClosureReduced

/-! # Separable splitting of geometrically diagonal coalgebras

Source: Milne, Algebraic Groups (2017), Theorem 12.18(c)–(d), printed pp.237–238,
and Corollary 12.19, printed p.238.
(blueprint: lem-sfb-geometrically-diagonal-coalgebra-separable-basis)

The scalar-extended coalgebras use Mathlib's tensor-product coalgebra instance.
The conclusion indexes its basis by all group-like elements, with their actual values.
-/

set_option autoImplicit false

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Coalgebra

/-- If a coalgebra has a group-like basis over an algebraic closure, all its group-like
elements over an embedded separable closure form a basis. No finite-dimensionality is assumed.
Source: Milne, Algebraic Groups (2017), Theorem 12.18(c)–(d), printed pp.237–238,
and Corollary 12.19, printed p.238.
(blueprint: lem-sfb-geometrically-diagonal-coalgebra-separable-basis)

Proof:
1. Put K = ks and L = kbar. The field K is separably closed, and L is an algebraic
closure of K. The pure-tensor maps identify L tensor_K (K tensor_k C) with L tensor_k C
as coalgebras (def-pd-separable-closure, def-weil-algebraic-closure, and
def-weil-pbc-module-tensor-product). For any v in K tensor_k C, choose a finite-dimensional
subcoalgebra D containing v by lem-sfb-coalgebra-finite-subcoalgebra.
2. Tensoring the inclusions of D and D tensor_K D by L is injective, by
lem-weil-pbc-module-over-field-flat and lem-weil-pbc-flat-tensor-exact. Thus W = L tensor_K D
is a finite-dimensional subcoalgebra of L tensor_k C. A finite basis of D has images with
finite support in the given geometric basis; let S0 be the union of these supports.
3. Contracting the second tensor factor of Delta(w) with the ith basis coordinate gives
a_i g_i in W when w = sum_i a_i g_i belongs to W. Hence a_i nonzero implies g_i belongs
to W. Therefore W has basis the g_i belonging to W, a subset of S0.
4. By lem-sfb-finite-coalgebra-dual-base-change, for A = D dual, L tensor_K A is W dual.
Evaluation on the basis of W identifies this convolution algebra with L^S, so it is
commutative and reduced. Extend 1 in L to a K-basis and take its coordinate functional ell.
The map ell tensor id retracts the inclusion A to L tensor_K A, so A is commutative and reduced.
5. A is Artinian by lem-weil-pbc-finite-dim-algebra-artinian. By
lem-sfb-reduced-artinian-residue-product it is the product of its finitely many residue
fields E_m, each finite-dimensional over K. The zero algebra has an empty such product.
6. By lem-weil-pbc-tensor-finite-product and tensor symmetry, A tensor_K L is the product
of E_m tensor_K L. Each factor is reduced: insertion with zero in the other coordinates
preserves multiplication and would send a nonzero nilpotent to one in the product.
By lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable each E_m/K is
separable, and lem-pc-sepclosed-finite-sep-trivial identifies it with K. Thus A is K^M.
7. The coordinate algebra homomorphisms A to K correspond, by
lem-sfb-finite-coalgebra-dual-base-change, to group-like elements d_m of D. The coordinate
functionals form a basis of A dual, and evaluation D to A dual is an isomorphism.
Thus the d_m form a basis of D. Their images in K tensor_k C remain group-like, so the
arbitrary v is in the span of all group-like elements. For D zero the basis is empty.
8. For a group-like h, write its geometric image as sum_i a_i g_i. The equation
Delta(h) = h tensor h gives a_i squared = a_i and a_i a_j = 0 for distinct indices.
The counit gives sum_i a_i = 1. Over L exactly one coefficient is 1, all others are 0.
The scalar-extension map is injective using the same ell tensor id retraction. Therefore
distinct group-like elements have distinct geometric basis images. Every finite relation
between them becomes a relation in that basis, and all coefficients vanish. Together
with step 7 this proves the asserted basis statement, including the zero coalgebra. -/
theorem geometricallyDiagonal_separableClosure_basis
    {k : Type u} [Field k] {ks : Type v} [Field ks] {kbar : Type w} [Field kbar]
    [Algebra k ks] [IsSepClosure k ks] [Algebra k kbar] [IsAlgClosure k kbar]
    [Algebra ks kbar] [IsScalarTower k ks kbar]
    {C : Type t} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (hgeom : ∃ (ι : Type (max w t)) (b : Module.Basis ι kbar (kbar ⊗[k] C)),
      ∀ i : ι, IsGroupLikeElem kbar (b i)) :
    ∃ b : Module.Basis {c : ks ⊗[k] C // IsGroupLikeElem ks c} ks (ks ⊗[k] C),
      ∀ c : {c : ks ⊗[k] C // IsGroupLikeElem ks c}, b c = c.val := by
  sorry

end Coalgebra
