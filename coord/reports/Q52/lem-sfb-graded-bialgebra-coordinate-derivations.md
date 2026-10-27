## Worker report

The module `Sheaf.RingTheory.GradedBialgebraCoordinateDerivations` states
`GradedAlgebra.exists_coordinate_derivations`, with exactly one postponed theorem and no
new definitions. Its proof is `sorry`. The declaration docstring contains all seven steps
of the accepted DAG proof. Only the item's `lean` field changes.

The inherited ending was a stage-1 refusal, not a stage-2 blocker. The current node is
`split`, reviewed by Q92, has no Lean record, and appears as stage 2 in `coord/queue.tsv`.
The stage-handoff paragraph of `coord/brief-stage2.md` explicitly authorizes this work.
No released repair note exists. The accepted statement and split are preserved.

Source read: `literature/milne-abelian-varieties_AV.pdf`, PDF page 61, printed page 55,
I Lemma 12.2 and its proof. The node correctly identifies this as an agent-written
prerequisite for the Borel structure input, not a statement printed in Milne. In particular,
Milne's perfectness assumption for the subsequent structure theorem is not an assumption
of this intermediate derivation lemma.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Field k, with no restriction on characteristic or perfectness | `(k : Type u) [Field k]`; no `CharP`, `CharZero`, or `PerfectField` binder |
| Associative unital k-algebra A | `(A : Type v) [Ring A] [Algebra k A]`; `Ring` includes associative multiplication and a unit, without assuming ordinary commutativity |
| Finite dimension and 1 nonzero | `[FiniteDimensional k A] [Nontrivial A]` |
| Nonnegative internal direct-sum grading | `(𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]`; Mathlib's structure includes the direct-sum decomposition and multiplicative grading |
| A^0 = k times 1 | `hconnected : 𝒜 0 = Submodule.span k {(1 : A)}` |
| Signed commutativity on all homogeneous a,b | `hcomm`, with subtype elements in components m,n and scalar sign `(-1 : k) ^ (m * n)` |
| Given k-linear coproduct | `Δ : A →ₗ[k] A ⊗[k] A` |
| Coproduct preserves degree | `hdegree`: its value on component n belongs to the span of pure tensors in bidegrees p,q with p+q=n |
| Unital algebra map into the signed tensor product | `hunit` and `hmul`; linearity is already bundled in Δ, and preserving 1 and multiplication is exactly the remaining algebra-map data. `GradedTensorProduct.of` is the canonical linear identification; multiplication on its codomain is Mathlib's signed multiplication |
| Coassociativity | `hcoassoc`, using `TensorProduct.assoc` and the two tensor maps |
| Epsilon is the degree-zero projection, identified with k | `ε : A →ₗ[k] k` and `hprojection : algebraMap k A (ε a) = GradedAlgebra.proj 𝒜 0 a`. Connectedness and nontriviality identify this uniquely; ε is not an arbitrary augmentation |
| Both counit identities | The two conjuncts of `hcounit`, using the canonical `TensorProduct.lid` and `TensorProduct.rid` |
| I is the positive part | `I : Submodule k A` with `hI`, the supremum of all components indexed by positive natural numbers. The direct-sum grading makes this the indicated positive direct sum |
| I² is the span of products of two elements of I | `hJ`: J is the comap along `I.subtype` of exactly this ambient span. This realizes I² inside I; the span lies in I by the positive grading |
| Finitely many positive-degree homogeneous elements x_j of degrees d_j | `s : ℕ`, `d : Fin s → ℕ`, `hd`, `x : Fin s → I`, and `hx`. Using elements of I records membership already implied by positivity, without choosing or omitting any lifts |
| Their classes form a basis of I/I² | `b : Module.Basis (Fin s) k (I ⧸ J)` and `hb : b j = J.mkQ (x j)`; b is exactly this family, not a different basis |
| For each i there is a k-linear map | `∀ i : Fin s, ∃ D : A →ₗ[k] A` |
| Degree -d_i, with negative components zero | First conjunct: `D a ∈ (if d i ≤ n then 𝒜 (n - d i) else ⊥)` for every homogeneous a in degree n. The bottom component forces zero when n<d_i, rather than incorrectly allowing a scalar via truncated natural subtraction |
| Value at 1 is zero | Second conjunct `D 1 = 0` |
| Coordinate values on every given generator | Third conjunct `∀ j, D (x j : A) = if i = j then 1 else 0` |
| Signed Leibniz for all homogeneous a,b | Last conjunct, for independent homogeneous degrees m,n: `D (a*c) = D a*c + (-1 : k)^(d i*m) • (a*D c)` |
| No cocommutativity, perfectness, or characteristic assumption | None is present, and no ordinary `Bialgebra k A` or `CommRing A` instance is imposed |

Dependency declarations read and used:

- `def-weil-field` is the Mathlib leaf `Field`, in `Mathlib.Algebra.Field.Defs`.
  Its full class definition and docstring were read; no replacement field notion is introduced.
- `def-weil-pbc-module-tensor-product` is the Mathlib leaf `TensorProduct`, in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with its canonical pure tensor and module
  structure. The recorded universal-property declarations `TensorProduct.lift`,
  `TensorProduct.lift.tmul`, and `TensorProduct.ext'` in `.Basic`, and `LinearMap.rTensor`
  and `LinearMap.rTensor_tmul` in `.Map`, were read. Tensor maps in the signature use
  the same canonical `TensorProduct.map`. Both dependencies have `mathlib_match`
  records, so neither requires a project Lean record or dependency module.
- Additional existing Mathlib interfaces used directly: `GradedAlgebra` and
  `GradedAlgebra.proj` (`Mathlib.RingTheory.GradedAlgebra.Basic`),
  `GradedTensorProduct` and `GradedTensorProduct.of`
  (`Mathlib.LinearAlgebra.TensorProduct.Graded.Internal`),
  `TensorProduct.assoc`, `.lid`, `.rid` (`.Associator`), `Module.Basis` (`.Basis.Defs`),
  and `Submodule.mkQ` (`.Quotient.Defs`). Their definitions/docstrings were opened.
  In particular `GradedTensorProduct.tmul_coe_mul_coe_tmul` characterizes exactly the
  sign required by the node. These are existing notions, not missing new definitions.

Searches performed before drafting:

- `msearch.py ... leanfinder "Coordinate graded derivations on a finite connected graded
  signed commutative bialgebra"`: eight hits, including exterior grading, `GradedAlgebra`,
  and `TensorProduct.gradedMul_def`, but no coordinate-derivation theorem.
- `msearch.py ... loogle "GradedAlgebra, TensorProduct"`: twelve hits, including
  `GradedTensorProduct.of` and `.auxEquiv`. This found the exact signed tensor notion used.
- `msearch.py ... grep "GradedBialgebra|SignedTensor|graded.*[Bb]ialgebra|
  graded.*[Dd]erivation|Koszul"`: three unrelated Koszul comments; no matching theorem.
- `msearch.py ... leansearch "graded bialgebra coordinate partial derivations homogeneous
  generators indecomposables"`: eight hits on graded generation, polynomial derivatives,
  `GradedAlgebra`, and homogeneous decompositions; no matching theorem.
- Direct `rg` searches in `lean/WeilConjectures`, `lean/Sheaf` and Mathlib for
  `GradedBialgebra`, `SignedTensor`, graded derivations, signed tensor and coordinate
  derivations found `Sheaf.RingTheory.BoundedBialgebraExterior`, whose linear-coproduct
  hypotheses use the exact signed tensor product now reused here. It states an exterior
  criterion, not coordinate derivations.
- The upstream ordinary contraction theorem
  `Bialgebra.exists_derivation_counitAlgHom_comp` and cotangent theorem in
  `WeilConjectures.RingTheory.HopfAlgebra.Cartier`, and the normalization proof in
  `WeilConjectures.RingTheory.Bialgebra.Frobenius`, were read. They require ordinary
  commutative bialgebras and ordinary derivations, so cannot replace this signed graded
  theorem. No import of these proof examples is needed or recorded as a DAG dependency.
- A direct search for this node id under `lean/WeilConjectures` found no attachment.
  A collision search for `exists_coordinate_derivations`, `coordinate_derivations`,
  `GradedBialgebra`, and `GradedDerivation` in Mathlib, both source trees and
  `dag/lean_names_upstream.json` found no existing declaration with this name or statement.

Edge cases checked mathematically before drafting and against the final signature:

- s=0: `Fin 0` is empty and the conclusion is vacuous. In particular A=k is included.
- n<d_i, including n=0: the output component is bottom, enforcing zero rather than A^0.
- n=d_i: the output lies in A^0, allowing the required value 1 on x_i.
- Characteristic 2: all signs become +1; no assumption forces odd squares to vanish.
- Characteristic p and imperfect fields: no hypothesis excludes either. Truncated
  primitive polynomial algebras of p-power height remain admissible.
- Exterior generators u,v of degree 1: the sign gives D_v(uv)=-u as required.
- Mixed generator degrees and nontrivial correction terms: over F_3, with primitive t,y
  of degrees 2,4 and t^3=y^3=0, lifts x_1=t, x_2=y+t² require the correction
  partial_1=D_1-2tD_2; the statement requests normalization on these actual lifts.
- Repeated degrees are allowed; neither sorting nor distinctness is assumed.
- Independent universes u,v for k and A are explicitly bound; all other variables are
  explicit, with `autoImplicit false`.

There is no statement correction, disputed claim, missing notion, or dependency repair.
The initial compiler probe rejected the token ∂ as a binder; it was renamed D, with no
mathematical change. `scompile.py Q52 lem-sfb-graded-bialgebra-coordinate-derivations
<module>` then compiled both sandbox and actual module names cleanly (about 1.1 and
1.2 seconds respectively), with no non-sorry warnings.

## Second reading by Q52

This is a sequential second reading by the same worker: the dispatcher explicitly forbids
starting other agents, and the delivery receives the maintainer's independent review.
No claim of a separate worker review is made.

I reopened the accepted node and final file and checked each correspondence above.
The key points were that the tensor multiplication is signed despite the underlying
ordinary module tensor, that the coproduct is unital and multiplicative as well as
coassociative, and that both counit identities and the precise degree-zero projection
are retained. The positive part I and square J are fixed by equations, not arbitrary
subspaces. The basis b is fixed to the classes of the supplied x_j by hb, so there is no
replacement of the generators. The output is genuinely zero below d_i, and the sign
in Leibniz is d_i times the degree of the first factor. All four conclusions and all
field characteristics remain present. No mismatch or further mathematical change was
found. The node's accepted statement, source, statement dependencies, proof and proof
dependencies are unchanged, and the recorded signature is extracted verbatim from the file.
