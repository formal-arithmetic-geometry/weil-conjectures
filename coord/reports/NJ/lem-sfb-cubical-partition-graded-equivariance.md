## Worker report

The module `Sheaf.AlgebraicTopology.CubicalPartitionGradedEquivariance` states
`IntegralLatticeCubical.partitionGradedEquivariance`. Its only postponed proof is
that theorem, with the node's complete six-step proof plan in its docstring.
The four helper definitions contain actual constructions, with no chosen unknown data.
No natural-language statement, dependency record, or dependency list was changed.

Clause-by-clause reading:

- `r : ℕ` includes exactly all nonnegative integral ranks. `Fin r → ℤ` is the lattice
  with its given ordered standard basis `unitVector r`. Reindexing coordinates from
  `1,...,r` to `Fin r` preserves their order and the inversion counts.
- `Chains r a`, `Directions r a`, and `cell r a v I` are the dependency's existing free
  abelian groups and basis symbols, in integer degree `a`. They are not redefined.
  The imported `boundary` is precisely the displayed alternating sum, and the imported
  `augmentation` takes every degree-zero vertex to one. The degree-zero boundary is zero
  since its only direction set is empty.
- `partitionTensorComplex r` is the existing Mathlib tensor complex of the published
  cubical complex, extended by zero to negative integer degrees. Its degree `n` is the
  direct sum of the tensor summands of total degree `n`. The original natural-degree
  complex already vanishes above rank `r`. Zero extension adds all integer degrees
  without truncating a permitted case. `partitionTensorInclusion r a b n` is the canonical
  inclusion of a tensor summand, using tensor maps, degree-equality transports, and the
  inverse of `extendXIso`; it is zero for a negative factor or incorrect total degree.
  Negative-factor summands are zero modules, so this also includes their unique maps.
- The first conjunct gives exactly the signed differential on every homogeneous pure
  tensor: the first boundary plus `(a.negOnePow : ℤ)` times the second boundary.
  `Int.negOnePow` is the integral parity sign for every integer, including negative ones.
  The use of actual linear maps from actual tensor products expresses well-definedness;
  the differential belongs to the specified bundled chain complex.
- The second conjunct states square-zero in every integer degree. It is explicitly
  included because the node states it, even though the bundle also carries this proof.
- `directionSum` is the existing sum `u_A`, and `partitionSign` is the existing integer
  sign counting pairs `(a,b)` with `b<a`. Neither notion is copied.
- `gradedPartitionComponent` transports the existing `diagonalComponent` to integer
  degree on each free basis symbol; there is no second independent partition formula.
  The third conjunct identifies its generator values with the node's displayed sum.
  The index `A ∈ I.val.powerset` enumerates the ordered partitions `(A,I\A)` exactly.
- The fourth conjunct says any entire integer-indexed linear family with those generator
  values equals `gradedPartitionComponent`. Together with the preceding generator
  formula and the actual definition, this is existence and uniqueness of the specified
  family, rather than an arbitrary choice or a stronger chain-map assertion.
- The fifth conjunct counts exactly `2^|I|` summation indices and says each term has
  `|A|+|I\A|=|I|`. Terms are counted before collection of equal values, as in the node.
- The sixth conjunct makes every component with `n<0` or `r<n` zero. These are exactly
  the degrees with empty source basis. It does not force the tensor complex itself to
  vanish above `r` (it may remain nonzero up to `2r`).
- The seventh conjunct is exactly `P_n τ_w = (τ_w tensor τ_w) P_n` for every integer
  degree and lattice vector. The source translation is the dependency's `translate`.
  `partitionTensorTranslate` is the zero-extended tensor of the existing two translation
  maps, not an arbitrary target action. No partition/differential commutation is asserted.

Dependencies read and used:

- `Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction`:
  `IntegralLatticeCubical.Directions`, `Chains`, `cell`, `unitVector`, `boundary`,
  `augmentation`, `translate`, and `contraction`. I read their complete signatures and
  docstrings, including the zero extension and contraction proof plan.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, and
  `Mathlib.LinearAlgebra.Finsupp.LinearCombination`: `Finsupp.linearCombination`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`: `TensorProduct`,
  `TensorProduct.lift`, its generator uniqueness, and `TensorProduct.map`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology`; and `Mathlib.Algebra.Homology.HomologicalComplex`:
  `ChainComplex`. The chain-complex notion is used through the bundled tensor complex.
- Additional already published helper interface in
  `Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal`: `chainComplex`,
  `translationMap`, `directionSum`, `partitionSign`, `diagonalComponent`, and `tensorCell`
  (the latter was read to check the published inclusion and formula).
  Their complete signatures and docstrings were read. The theorem `diagonal` is not
  used to assert the present theorem. These definitions are currently housed with the
  downstream theorem; importing their module does not currently create an import cycle.
  Adding a reciprocal proof import to that module would create one and must be omitted
  under stages/2-statements.md §3.7. No dependency on the downstream theorem is added to
  the DAG. A later reorganization of these already shared definitions can remove this
  module-level limitation without changing either mathematical statement.
- `Mathlib.Algebra.Homology.Embedding.Extend`: `HomologicalComplex.extend`,
  `extendXIso`, and `extendMap`, with `(ComplexShape.embeddingUpIntGE 0).op`.
  These existing constructions supply the canonical zero extension; the four helpers
  in this module only specialize/transport the objects of this node.

Edge cases checked before and after writing:

- Rank zero: the lattice has one point; only degree-zero cells remain, the unique
  partition is empty in both parts, the sign is one, and translations are trivial.
- Empty direction set: the powerset has one term, both factors have degree zero, and
  the differential has an empty face sum; no subtraction of natural degrees is used
  to hide the negative target.
- Negative degree and degree above rank: `Directions r n` is empty and hence the source
  free group is zero. The sixth clause explicitly includes both ranges.
- Top degree: no source degree is dropped. Tensor target degrees above rank remain
  available, even though the partition map there has zero source.
- A negative tensor factor: its source is zero. Its boundary also has zero source,
  making the signed formula compatible with the zero inclusion.
- Zero degree in the first factor: its boundary is zero, and the second-factor sign
  is one. This avoids interpreting a nonexistent degree-minus-one cell as nonzero.
- Arbitrary negative coordinates and translations: all lattice coordinates remain
  integers; no positivity or finiteness assumption on vertices is introduced.
- The theorem uses no universe variable: the lattice, finite subsets, and free abelian
  groups in this statement are small types already fixed by the node, not arbitrary
  universe-indexed input modules.

Searches made:

- `msearch.py ... leanfinder "The signed cubical lattice subset partition diagonal
  extends uniquely to a graded homomorphism equivariant for diagonal translation"`:
  eight results, including box partitions and Dold–Kan decomposition, no exact statement.
- `msearch.py ... loogle "TensorProduct.map, Finsupp.linearCombination"`:
  zero results for the combined query. Direct source reads found both constructions.
- `msearch.py ... leansearch "Cubical lattice partition sum is equivariant for
  simultaneous translation and uniquely extends from the free basis"`:
  eight results on translated sums, affine bases, and partitions, no exact statement.
- `msearch.py ... grep "cubical|Cubical|partition.*diagonal"`: one unrelated Mathlib
  permutation-cycle square partition result; no cubical lattice formula.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `Cubical`, `cubical`,
  `partitionGraded`, and `partition_graded`, plus the exact blueprint id in
  `lean/WeilConjectures`: no upstream match; found the published contraction,
  integral diagonal, and partition-boundary-expansion modules in `Sheaf`.
  These published definitions were reused. Their stronger chain-map theorem is not
  exactly this graded statement, and it does not explicitly state uniqueness/counting.
- Read the current blueprint `latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`
  in full. Paragraph (3) supplies the ordinary-open/direct-image route, not the agent's
  cubical calculation; the report and docstrings preserve that distinction, consistent
  with this node's recorded source and proof_origin.

Validation: `scompile.py` compiled the final file both in its sandbox and at its intended
library module path without errors or unexpected warnings (2.7 s and 3.0 s).
No statement correction or disputed statement was needed.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
