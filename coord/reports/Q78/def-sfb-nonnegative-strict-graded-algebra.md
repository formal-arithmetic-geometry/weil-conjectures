## Worker report

The module `Sheaf.RingTheory.NonnegativeStrictGradedAlgebra` defines strict graded
commutativity on the dependency's actual internally graded, possibly
noncommutative algebra. It also defines the three parity submodules, the
zero extension to integer degrees, the even subalgebra, its inherited
commutative ring structure, and its positive even ideal. There is one postponed
theorem, `GradedAlgebra.parity_properties`, stating the node's final structural
assertions. Its docstring supplies the complete finite-sum argument from the
node. No definition has unspecified data.

Hypothesis and clause correspondence:

- The commutative base ring is `{R : Type u} [CommRing R]`; the associative unital
  algebra is `{A : Type v} [Ring A] [Algebra R A]`. The independent explicit
  universes impose no size restriction between the two rings. In particular,
  there is no assumption that `A` is commutative or nontrivial.
- The nonnegative family is `𝒜 : ℕ → Submodule R A`. The binder
  `[GradedAlgebra 𝒜]` is exactly the declaration recorded by the only statement
  dependency, `def-sfb-nonnegative-graded-algebra`. It supplies both the internal
  direct-sum decomposition (`DirectSum.Decomposition`) and multiplicative
  grading including the degree-zero unit (`SetLike.GradedMonoid`). The scalar
  image is in degree zero since it is an R-submodule containing 1. None of
  these notions is privately copied.
- Homogeneity of degree i is membership `x ∈ 𝒜 i`; the existing submodule subtype
  is available when homogeneous elements themselves need to be bundled.
  `integerComponent` is literally `𝒜 n` in integer degree `ofNat n` and the
  bottom submodule in each negative degree `negSucc n`.
- The class field `signed_comm` says, for all natural degrees i,j and elements
  x,y in the corresponding components,
  `x * y = (-1 : A) ^ (i * j) * (y * x)`.
  The sign is multiplication by the ring element, equal to the scalar sign
  since an algebra map preserves -1 and powers.
- The independent field `odd_sq_zero` says for every `Odd i` and `x ∈ 𝒜 i`,
  `x ^ 2 = 0`. This condition is not inferred by cancelling 2.
- `evenPart 𝒜 = ⨆ i : ℕ, 𝒜 (2 * i)` and
  `oddPart 𝒜 = ⨆ i : ℕ, 𝒜 (2 * i + 1)` are their sums inside A. A supremum of
  submodules is precisely the set of finite sums from those submodules. The
  given internal direct sum identifies it with the image of the indicated
  restricted external direct sum; the restricted sum is injective because
  the full sum map is. Thus these definitions have exactly the intended
  internal carriers, rather than supplying arbitrary parity submodules.
- `positiveEvenPart 𝒜 = ⨆ i : ℕ, ⨆ (_ : 0 < i), 𝒜 (2 * i)` uses strictly
  positive even indices, with no degree-zero contribution.
- The first two conjuncts of `parity_properties` give the unit and
  multiplicative closure of `evenPart`. The existing Mathlib constructor
  `Submodule.toSubalgebra` gives `evenSubalgebra`, with that precise carrier,
  inherited multiplication/addition and scalar map. The third conjunct gives
  even commutativity; `evenSubalgebraCommRing` extends the inherited ring
  instance with that commutativity, without altering any operations.
- The fourth conjunct says even elements multiply the positive even submodule
  into itself. `positiveEvenIdeal` has carrier exactly those elements of the
  even subalgebra whose image in A lies in `positiveEvenPart`. Its zero/addition
  fields come from that actual submodule and its multiplication closure comes
  from the fourth conjunct. Since the even ring is commutative, this is the
  required ideal, not just an unrelated ideal or a one-sided substitute.

Dependency source read: `Mathlib.RingTheory.GradedAlgebra.Basic.GradedAlgebra`
(the declaration name is `GradedAlgebra`, at lines 163–172), including the full
`GradedRing` signature/docstring at lines 48–67. Read also
`DirectSum.Decomposition` and its two inverse laws in
`Mathlib.Algebra.DirectSum.Decomposition`, lines 46–59, and
`SetLike.GradedMonoid` in `Mathlib.Algebra.GradedMonoid`, lines 521–523.
This dependency has `status: mathlib` and its usable `mathlib_match` supplies
its declaration directly. No dependency repair or new node is needed.

Source read: `literature/stacks-project/dpa.tex`, lines 952–990, the paragraphs
before Tag 09PG (in Tag 09PF) and the following observation identifying the
positive even part as an ideal of the commutative even ring.

Edge cases checked before writing:

- Characteristic 2: signed commutativity alone allows nonzero odd squares;
  the separate `odd_sq_zero` field excludes them, as the source requires.
- Degree zero: 0 is even, never odd, and never strictly positive. The unit and
  scalar image belong to the even part, not necessarily its positive ideal.
- An algebra concentrated in degree zero has even part A and zero odd and
  positive even parts. The strictness condition then says A is commutative,
  exactly as the sign rule requires.
- The zero ring, vanishing components and vanishing odd part are permitted;
  no nontriviality, nonempty support or invertibility of 2 is assumed.
- Odd components in degrees other than one are included by `Odd i`. The sign
  rule includes all ordered pairs of degrees and all homogeneous elements.
- Negative integer degrees are bottom, rather than incorrectly using
  `Int.toNat` to send a negative degree into the degree-zero component.
- Infinite parity sums mean finite-support elements inside A, not products.
  An empty positive-degree support gives the zero ideal.

Searches for an existing declaration (all against the read-only live sources):

- `msearch.py ... leanfinder "A nonnegatively graded algebra is strictly graded
  commutative when homogeneous elements commute with sign and odd homogeneous
  squares vanish"`: eight hits, including `ExteriorAlgebra.gradedAlgebra`,
  `CliffordAlgebra.gradedAlgebra`, `SetLike.gcommRing`, `GradedAlgebra` and
  `TensorProduct.gradedComm_gradedMul`. The first two are particular algebras,
  `gcommRing` assumes ordinary commutativity, `GradedAlgebra` has no strictness
  fields, and the tensor-product result is a braiding formula. No match.
- `msearch.py ... loogle '"GradedAlgebra"'`: twelve hits, giving the underlying
  grading and projection constructions; no strict graded-commutativity class.
- `msearch.py ... grep 'strictly graded|strict.*graded.*comm|GradedComm'`:
  ten hits in the graded tensor-product braiding files, no general strictness
  condition on a graded algebra.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for strict graded terminology,
  parity names and the proposed declaration names: the self-Tor Tate
  comparison files only discuss strictness in their proofs/docstrings and do
  not define this notion. Those files were read to confirm this distinction.
- `rg` of the whole Mathlib source and `dag/lean_names_upstream.json` for the
  proposed class, parity definition and structure names: no collision.
- Search for the item id in `lean/WeilConjectures`: no occurrence.

No node correction, missing dependency, or statement dispute was found.
All new declarations, including the postponed structural theorem, are listed
in the item's `lean.declarations`. Only the item's `lean` field is changed.

Validation: `scompile.py Q78 def-sfb-nonnegative-strict-graded-algebra` compiled
this module on the server under both sandbox and library names, cleanly
(4.2 seconds and 6.4 seconds respectively). No diagnostic commands remain.

## Second reading by Q78

A second pass by the same worker re-read the node and module after compilation;
the dispatcher forbids starting another agent. The maintainer supplies the
independent review. This pass checked the source clauses against the binders
and each class field, verified that the ring on A is not silently commutative,
and checked that odd-square-zero remains independent in characteristic 2.
It checked both natural parity index formulas, the strict positivity binder,
and the negative-degree pattern match. The three submodule sums use the
original grading, and the even subalgebra and ideal use those actual carriers.
The conjuncts of `parity_properties` exactly supply unit, product closure,
commutativity, and ideal closure. The commutative ring instance retains the
inherited operations. All structure data is explicit; the only postponed
proof is the named theorem with the matching node's source and proof text.
No mismatch was found and no statement or dependency field was changed.
