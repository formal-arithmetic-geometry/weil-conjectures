## Worker report

This delivery completes the inherited attachment as an `existing: true` record for
`AlgebraicGeometry.Scheme.Hom.exists_pointCount_le_mul_pow` in
`WeilConjectures.PointCountBound` (branch `slopmaster2`). No module or theorem is added.
Only the item's `lean` field changes. There is no repair note for this item.

I read the full DAG statement, its proof, the convention dependency and its Lean record,
the source blueprint file, the complete upstream theorem and its docstring, and the
current published module returned by `scompile.py --source WeilConjectures.PointCountBound`.
The current published theorem agrees with the local upstream theorem at lines 132–196.
The shared node's previous attachment named this theorem but omitted the module, main
declaration, signature and existing flag. This delivery supplies that complete record.

Hypothesis and clause correspondence:

| Node text | Existing Lean interface and specialization |
| --- | --- |
| finite field k₀ = F_q | Section parameters `{k : Type u} [Field k] [Finite k]`; q is `Nat.card k`. No particular presentation of a finite field is selected. |
| U₀ over k₀ | `{X : Scheme.{u}}` and `(f : X ⟶ Spec (.of k))` are its scheme and structure map. |
| affine | `[IsAffine X]`. |
| smooth curve | The theorem requires only `hX : topologicalKrullDim X ≤ 1`, supplied by the curve hypothesis. Smoothness is allowed and is unnecessary for this existing general bound. The source proof's pure-dimension-one condition implies this bound too. |
| separated and finite type | The convention record points to Mathlib `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`. Finite type supplies `[LocallyOfFiniteType f]`; separatedness is unnecessary for this existing bound. Affineness over a field supplies quasi-compactness. |
| k_n = F_(q^n) | Existing `FiniteField.galoisExtension k n`, the splitting field of `X^(q^n)-X`; `FiniteField.nat_card_galoisExtension k n hn` identifies its cardinality with `Nat.card k ^ n` when n is nonzero. |
| #U₀(k_n) | `f.pointCount n` unfolds to `Nat.card (f.fieldPoints (FiniteField.galoisExtension k n))`. `fieldPoints` is the subtype of scheme morphisms `Spec k_n ⟶ X` whose composite with f equals the structure map from the algebra embedding. Thus it counts points over the base field, not geometric or closed points. |
| one constant independent of n | `∃ d : ℕ, ∀ n : ℕ, ...`. |
| d ≥ 1 | The existing theorem initially permits d = 0. Replace its witness d by d + 1: 1 ≤ d + 1, and `d * q^n ≤ (d + 1) * q^n`. Conversely any positive witness is an unrestricted witness. This changes neither the existence claim nor the point count and handles the empty scheme. |
| all n ≥ 1 | `∀ n : ℕ, n ≠ 0 → ...`; for natural n, nonzero is equivalent to 1 ≤ n. |
| bound d q^n | `f.pointCount n ≤ d * Nat.card k ^ n`. |

The pre-existing theorem is more general in its hypotheses, so no smoothness or separatedness
assumption is required to invoke it. Its specialization is precisely the requested bound;
its unrestricted constant and the requested positive constant are equivalent as explained
above. The delivered record retains the verbatim existing signature instead of pretending
that the source explicitly binds smoothness or positivity.

The statement dependency `def-weil-pbc-scheme-conventions` is explicitly a convention-only
node: its Lean record has `convention: true`, `module: null`, and `declaration: null`.
It supplies no definition to import. Its affine, finite-type and separated notions are
Mathlib's `AlgebraicGeometry.IsAffine` (`AffineScheme`),
`AlgebraicGeometry.LocallyOfFiniteType` (`Morphisms.FiniteType`), and
`AlgebraicGeometry.IsSeparated` (`Morphisms.Separated`). I read these class signatures and
reused the existing source theorem's instances. `Scheme.Hom.fieldPoints`, `.pointCount`,
and `FiniteField.galoisExtension` are read in `Comparator/Weil/Definitions.lean` and exported
by the existing `WeilConjectures.PointCountBound` import. `WeilConjectures.PointCount`
provides `Scheme.Hom.finite_fieldPoints`, confirming that `Nat.card` is a finite point count
for the finite-type schemes and finite extensions here, rather than its infinite-set junk
value. No new copy of the finite-field or scheme conventions is introduced.

Edge cases checked: the empty affine scheme has count zero and admits constant 1; no
nonempty hypothesis is added. Disconnected smooth affine curves are admitted. At n = 1
the extension is the base field up to k-isomorphism. The junk extension at n = 0 is excluded
by exactly the source's positive-n hypothesis. Finite fields of every characteristic are
allowed, and their cardinality is at least 2. The uniform constant may be increased even
when every point count vanishes. Arbitrary universe u is explicitly bound upstream.

Searches made:

- `msearch.py leanfinder`: “constant bound rational points affine smooth curve finite
  field”. Eight Mathlib hits, including polynomial admissibility, Chevalley complexity,
  Chevalley–Warning, and Weierstrass nonsingularity; none is this general scheme theorem.
- `msearch.py leansearch`: “affine curve finite field rational point count at most
  constant times field cardinality”. Eight hits, including
  `FiniteField.card_image_polynomial_eval` and Weierstrass-curve definitions; no match.
- `msearch.py loogle`: `pointCount, Finite, Fintype`. No hits: unknown Mathlib identifier
  `pointCount`.
- `msearch.py grep`: `pointCount_le_mul_pow`, all Mathlib. No hits.
- Direct `rg` in upstream `WeilConjectures` for the node id and
  `exists_pointCount_le_mul_pow` found the existing theorem in `PointCountBound.lean`
  and its consumer in `EtaleCohomology/Purity/RealSheaves/Semicontinuity.lean`.
- Direct `rg` in project `lean/Sheaf` for `pointCount`, `PointCount`, and the theorem
  name found uses of upstream point-count modules and the separate fixed-algebraic-closure
  finite-field datum, but no second bound. The item's statement does not fix an algebraic
  closure, so the existing splitting-field model is the appropriate model here.
- The upstream name-index search found no additional matching declaration.

No statement correction, disputed statement, new definition node or dependency repair is
needed. The existing theorem's source includes its full Noether-normalization proof. It
already proves the bound, so stage 2 must not restate it with `sorry`.

Validation uses only `scompile.py`: a scratch import probe checks the full theorem type,
its axioms, point-count definitions, finiteness theorem and extension-cardinality theorem.
The scratch probe compiled cleanly against both sandbox and published-library contexts;
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The prescribed delivery wrapper additionally checks the recorded declaration through its
own import-and-`#check` probe and runs server preflight.

## Second reading by Q35

No independent second worker is claimed: this dispatch prohibits other agents and assigns
independent review to the maintainer. In the self-check I reopened the node and existing
source and checked the table above, specifically the positive-constant conversion, the
finite point-set interpretation, the positive-n condition, and the empty scheme case.
No Lean declaration or mathematical node statement was changed.
