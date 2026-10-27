## Worker report

The module `Sheaf.RingTheory.SplitPolynomialBoundaryAttachment` states
`Algebra.SplitPolynomialAttachment.exists_boundary_attachment`, with its sole theorem
proof `sorry`. No statement, dependency list, or proof plan in the node was changed.
All four helper definitions are direct data or predicates spelling out notation within
this node's own statement; no new independent mathematical notion is introduced.
All declarations are public, listed in `lean.declarations`, and have source/blueprint
docstrings. `autoImplicit` is explicitly false. Only the sandbox was edited.

Sources read: `literature/stacks-project/cotangent.tex`, Tag 08PX,
`proposition-polynomial`, especially its inductive step; and
`literature/stacks-project/simplicial.tex`, Tag 017P, `definition-split`.
The DAG already repairs arbitrary lifts of degeneracies in the printed 08PX proof;
this delivery states that repaired node exactly. No new source error or dispute arose.

Hypotheses and clauses, matched to the Lean:

- A homomorphism of commutative rings A → B is `[CommRing A] [CommRing B]
  [Algebra A B]`, with the specified homomorphism `algebraMap A B`. Algebra structure
  is exactly the data of this homomorphism, not an additional mathematical condition.
- The nonnegative integer is `n : ℕ`. `P : SimplicialObject.Truncated
  (CommAlgCat A) n` is the specified truncated functor, and `ε` is its natural
  transformation to the constant algebra B. Thus all old identities are actual
  functor/augmentation identities, rather than separately assumed equations.
- The finite sets E_0,...,E_n are `E : Fin (n+1) → Type w` with
  `[∀ j, Finite (E j)]`. For each degree `k`, `Variable E k` is the sigma type
  `(j,e,σ)` where σ:[k]→[j] is surjective. There is no separate `j ≤ k` field:
  surjectivity of the map between the finite ordinals implies it, so this is
  exactly the displayed variable set. `p k` is the specified A-algebra equivalence
  from the polynomial algebra to P_k, including its coefficient identification.
- `hdeg` quantifies over every surjection τ between retained ordinals and every
  variable. `precompose τ hτ` is `(j,e,τ ≫ σ)`, where category composition `τ ≫ σ`
  is the displayed right-to-left function composition σ τ. The constructor's
  surjectivity witness is the actual composite of the two witnesses.
- T is `T : Type z` with `[Finite T]`; `b : T → B`; and
  `a : T → Fin (n+2) → P_n` is the prescribed family of faces.
- `haug` states ε_n(a_(t,i))=b_t for every t and i.
- `hfaces` uses `CompatibleFaces`: at n=0 it has no conditions; at n=r+1,
  `∀ i j : Fin (r+2), i ≤ j`, the equation is
  `d_i(a_(t,j+1)) = d_j(a_(t,i))`. This parametrizes exactly all original
  pairs i<j+1. The original first boundary index is `i.castSucc` and the
  original second boundary index is `j.succ`; all targets are degree r.
- The conclusion quantifies an actual `(n+1)`-truncated functor P' and actual
  natural transformation ε'. The witness `hP : trunc(P') = P` is literal
  equality, retaining objects and all operators, not only an unspecified iso.
- `q : MvPolynomial (Variable E (n+1) ⊕ T) A ≃ₐ[A] P'_(n+1)` supplies the
  new displayed polynomial presentation. A polynomial algebra on the disjoint
  union is precisely A[x_(e,σ),y_t], equivalently A[x_(e,σ)][y_t]. The new
  generator `y_t` is `q (X (Sum.inr t))`; old degenerate variables are
  `q (X (Sum.inl x))`.
- The first conjunct says that restriction of ε' is `eqToHom hP ≫ ε`, so the
  augmentation is retained together with the specified lower functor.
- The second conjunct says each new face of y_t is exactly a_(t,i), transported
  only across the equality hP. The third gives ε'(y_t)=b_t.
- The last conjunct quantifies over every new surjection [n+1]→[k] and every
  old variable, and says that its degeneracy is substitution of the composite
  label. Together with hdeg and hP this includes every degeneracy through n+1.
  For the identity surjection of [n+1], the action is the identity by functoriality,
  so y_t is the variable labelled by (n+1,t,id) in the extended indexing.
  A surjection [k]→[n+1] for k≤n does not exist, hence no missing lower image
  of a top nondegenerate variable needs specification.
- All simplicial identities hold because P' is a functor on the truncated
  simplex category. All augmentation identities hold because ε' is natural.
  There are no extra flatness, Noetherian, finite-type or nonzero-ring hypotheses.

Dependency declarations used:

- `def-weil-pbc-simplicial-coskeleton`: its Mathlib match is
  `CategoryTheory.SimplicialObject.Truncated` and truncation/restriction, read in
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`. This theorem only uses the
  truncation part; no coskeleton existence assumption is imposed. The canonical
  ordinal inclusion is `SimplexCategory.Truncated.incl`; `Hom.tr` packages actual
  ordinal maps in the full subcategory.
- `def-weil-pbc-mv-polynomial-ring`: recorded `MvPolynomial`, in
  `Mathlib.Algebra.MvPolynomial.Basic`, and its `algHom_ext` were read there;
  `MvPolynomial.aeval` and `aeval_X` were read in `Mathlib.Algebra.MvPolynomial.Eval`.
  The signature uses MvPolynomial and X. The proof docstring uses evaluation and
  uniqueness; no polynomial-ring copy was introduced.
- The category is Mathlib's `CommAlgCat`, with actual A-algebra maps and A-algebra
  equivalences. Its object and Hom declarations were read in
  `Mathlib.Algebra.Category.CommAlgCat.Basic`.
- `lem-sfb-truncated-simplex-presentation` is a proof dependency only and has
  no recorded Lean module or Mathlib match in the supplied DAG. Its statement
  and source were read; there is therefore no available proof module to import.
  Its recognition and natural-transformation clauses are explicitly named in the
  six-step proof docstring. The two other proof dependencies are already public
  imports because they are also statement dependencies.

Edge cases checked before writing and rechecked against the compiled signature:

- At n=0 the helper imposes no face--face equation; haug still equates the two
  augmented faces to b_t. The old variable set is just E_0 with the unique
  ordinal surjection, and the new degree includes its degeneracy and all y_t.
- At n=1 the compatibility helper gives exactly the three pairs of the three
  prescribed faces: (0,1), (0,2), (1,2).
- Empty T allows the extension with only degenerate variables. Empty E_j, even
  all E_j empty, are allowed; polynomial rings on the empty type are the base.
- The zero ring is allowed. No `Nontrivial`, field, or characteristic restriction
  is hidden in the category, equivalences, or finite-set hypotheses.
- Separate universes u,v,w,z permit arbitrary base rings, coefficient algebras,
  and finite label sets. Algebra equivalences allow different source/target type
  universes; no equality of these universe parameters is imposed.

Searches actually run via `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- LeanFinder: `Extend a truncated simplicial polynomial algebra by generators
  with prescribed compatible faces and fixed degeneracies`: 8 hits, including
  truncated simplex faces, degeneracies and truncation; no polynomial attachment.
- Loogle: `"Truncated", "MvPolynomial"`: 0 hits.
- grep: `(latching|degenerac|simplicial).*(MvPolynomial|polynomial)|
  (MvPolynomial|polynomial).*(latching|degenerac)`: 0 hits.
- LeanSearch: `Extend a truncated simplicial commutative algebra by polynomial
  generators along compatible boundary`: 8 hits, algebra-generator extensions
  and generic skeleton/Kan-extension declarations. These do not retain a given
  truncation while prescribing boundary values and fixed split degeneracies.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for splitPolynomial/split_polynomial,
  boundary_attachment/BoundaryAttachment/SplitPolynomial, and later
  SplitPolynomialAttachment/CompatibleFaces/exists_boundary_attachment and
  polynomial-simplicial phrases found no matching declaration. The existing
  `FinitePolynomialSimplicialResolution` module cites this item in its proof;
  it does not state the attachment theorem. The scheme-valued
  `FiniteSplitReplacementBoundaryAttachment` was read (including current source
  through `scompile.py --source`); it attaches coproducts of schemes to étale
  hypercovers, not polynomial algebra variables, so is not a duplicate.
- `grep -rn` for the node id in `lean/WeilConjectures` found no hits.

Validation: scompile.py compiled the single module in sandbox and library modes,
cleanly in 1.3 seconds each. An initial unknown unqualified `whiskerLeft` was
corrected to `Functor.whiskerLeft`; the final file has no diagnostic probes,
no warnings, and no proofs except the required theorem sorry. The required
`deliver2.py --no-push` dry run passed preflight and compilation (commit
`8c06e5d6233`); the final push repeats these checks on the current base.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
