## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSquareMonomorphismAbsoluteSeparated`
states `AlgebraicGeometry.affine_square_monomorphism_absolute_separated` with
`sorry` and constructs the canonical helper
`AlgebraicGeometry.Scheme.relativeToAbsoluteSquare` by `pullback.lift`.
The helper contains real data and uses terminality for the compatibility proof.
It belongs to the canonical map already introduced in this node, rather than a
new independent notion. No other theorem or definition is introduced.

Hypotheses and objects, matched clause by clause:

- The three schemes are `(S U R : Scheme.{u})`; their structure maps are
  `(f : U ⟶ S)` and `(r : R ⟶ S)`.
- The given commutative ring is `(A : Type u) [CommRing A]`, and its given
  affine presentation is `(e : U ≅ Spec (CommRingCat.of A))`.
- The relative square `V` is `pullback f f`, with its recorded Mathlib
  projections `pullback.fst f f` and `pullback.snd f f`.
- The absolute square `P` is
  `pullback (terminal.from U) (terminal.from U)`. The terminal scheme in
  Mathlib is `Spec (ULift ℤ)` (AlgebraicGeometry/Limits.lean), the integers
  placed in the ambient universe. Thus this is the stated square over Spec Z,
  with no restriction on the universe of the schemes or the ring.
- The canonical `k` is `Scheme.relativeToAbsoluteSquare f`. Its actual data
  are the pullback lift of the two relative projections. The compatibility
  proof is `Subsingleton.elim _ _`, because both composites have terminal
  target. Its projections therefore are the relative projections by
  `pullback.lift_fst` and `pullback.lift_snd`.
- The map into the relative square is `(j : R ⟶ pullback f f)`.
  Its S-linearity is exactly
  `(hj : j ≫ pullback.fst f f ≫ f = r)`; the corresponding equation using
  the other projection follows from the pullback condition.
- `[Mono j]` is categorical left cancellation against every scheme and every
  pair of maps from it, exactly the node's assumption.

Conclusions, matched clause by clause:

- The existential `eP` is an isomorphism from `P` to
  `Spec (CommRingCat.of (A ⊗[ℤ] A))`.
- Its first projection equation uses
  `Algebra.TensorProduct.includeLeftRingHom`, sending `a` to `a ⊗ 1`,
  and identifies the composite with `pullback.fst ... ≫ e.hom`.
- Its second equation uses the ring map of
  `Algebra.TensorProduct.includeRight : A →ₐ[ℤ] A ⊗[ℤ] A`, sending `a`
  to `1 ⊗ a`, and identifies it with `pullback.snd ... ≫ e.hom`.
- `Mono (Scheme.relativeToAbsoluteSquare f)` asserts that `k` is monic.
- `Mono (j ≫ Scheme.relativeToAbsoluteSquare f)` asserts that `q` is monic.
- `IsSeparated (j ≫ Scheme.relativeToAbsoluteSquare f)` asserts that `q`
  is separated, using the recorded closed-diagonal definition.
- `IsSeparated (terminal.from R)` asserts separatedness of the absolute
  structure map of `R`, exactly the final conclusion.
- There is no finite-type hypothesis on `j` and no separatedness hypothesis
  on `S`. There is no nonemptiness, nontrivial-ring, or size hypothesis.

Recorded dependency declarations were read with their signatures and docstrings:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-affine-spectrum`: the same module, `AlgebraicGeometry.Spec`
  and `AlgebraicGeometry.Spec.map`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and
  its universal map `pullback.lift`; scheme pullbacks exist by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  whose imported `AlgebraicGeometry.IsSeparated` is exactly the
  closed-immersion condition on the diagonal. Properness itself is not an
  assumption or a conclusion.

Proof-dependency interfaces were also read: `AlgebraicGeometry.pullbackSpecIso`
in `Mathlib.AlgebraicGeometry.Pullbacks` and its projection lemmas;
`AlgebraicGeometry.IsSeparated.isSeparated_of_mono` and
`AlgebraicGeometry.IsSeparated.hasAffineProperty` in
`Mathlib.AlgebraicGeometry.Morphisms.Separated`. All are available through
the imports. The docstring records the node's four proof steps, with their
DAG identifiers and the corresponding declarations. No proof is supplied.

Source checked: `literature/stacks-project/spaces.tex`, Tag 0265, first
proof paragraph (lines 1476 ff.). It uses monicity of the comparison with the
absolute affine square and separatedness of monomorphisms. This matches the
split statement and needs no statement correction.

Edge cases checked before writing: the zero ring gives empty `U` and squares;
monicity of `j` then forces `R` empty, and all conclusions hold. With `j` the
identity, monicity of the comparison and separatedness of the relative square
are retained. A nonseparated base `S` causes no problem: the canonical comparison
is required to be monic, without being required to be a closed immersion.
No locally finite type assumption is introduced, so monomorphisms such as
`Spec ℚ → Spec ℤ` are not excluded. The schemes and ring share their ambient
universe, and the terminal integer spectrum is lifted within that universe.

Searches for an existing combined statement:

- `msearch.py ... leanfinder`, query "For affine U over any scheme S a
  monomorphism R into U times S U gives a monomorphism into Spec of A tensor
  over integers A and R is separated": eight component hits, including
  affine-scheme separatedness, monomorphism separatedness, and the affine
  property of separatedness; no combined statement.
- `msearch.py ... loogle`, query
  `AlgebraicGeometry.IsSeparated, CategoryTheory.Mono`: one exact component,
  `AlgebraicGeometry.IsSeparated.isSeparated_of_mono`; no combined statement.
- `msearch.py ... grep`, query
  `isSeparated_of_mono|pullbackSpecIso|instIsSeparatedOfIsAffine` in
  `AlgebraicGeometry`: 25 hits, including the affine fibre-product
  isomorphism and monomorphism-separated instance; no combined statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for absolute/affine-square
  names and the exact node identifier found unrelated K-flat square modules
  and no declaration for this statement.
- `rg` in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for
  `relativeToAbsoluteSquare`, `absoluteSquareComparison`, and
  `affine_square_monomorphism_absolute_separated` found no pre-existing
  declaration with any of these names.

There are no new nodes, dependency repairs, statement corrections, or disputed
mathematical claims. The node copy changes only `lean`, with the theorem's
signature verbatim and both declarations listed.

Validation: the prescribed `scompile.py` compiled the delivered file against
the live published server library as both a sandbox module and its library
module, with exit code zero and no unexpected warnings (1.5 seconds each).

The existing Q103 report and PASS are a stage-1 split: that report explicitly
says it wrote no Lean source and ran no compiler, and the base node has no
`lean` record. This delivery supplies its first stage-2 statement.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
