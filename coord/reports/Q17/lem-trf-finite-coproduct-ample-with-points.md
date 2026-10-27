## Worker report

The new module `Sheaf.AlgebraicGeometry.FiniteCoproductAmpleWithPoints` states
`AlgebraicGeometry.Scheme.Modules.finite_coproduct_isAmple_iff_with_points`.
Its only proof is `sorry`. There are no new definitions, new nodes, dependency repairs,
or statement corrections. Only the item's `lean` field changes.

Clause-by-clause correspondence:

- Finite sets I and J are `{I : Type v} {J : Type w} [Finite I] [Finite J]`.
  The index universes are independent of the scheme universe; finite types are small,
  so Mathlib's coproduct API includes all these cases.
- The scheme families are `Y : I → Scheme.{u}` and `P : J → Scheme.{u}`.
- Integrality of each point summand is `[∀ j : J, IsIntegral (P j)]`.
  This includes the required nonemptiness and reduced irreducibility.
- Dimension zero is exactly `hP : ∀ j : J, topologicalKrullDim (P j) = 0`.
- Z is Mathlib's actual chosen coproduct `((∐ Y) ⨿ (∐ P))`.
  Its canonical a_i is `Sigma.ι Y i ≫ coprod.inl`; b_j is
  `Sigma.ι P j ≫ coprod.inr`. No replacement maps or extra hypotheses occur.
- L is `L : ((∐ Y) ⨿ (∐ P)).Modules` with `[L.IsInvertible]`.
- The first conclusion is `∀ j, (∃ (K : Type u) (_ : Field K),
  Nonempty (P j ≅ Spec (CommRingCat.of K))))`: an actual isomorphism to a field
  spectrum, expressed propositionally. A field of universe u suffices since the
  local ring of the scheme at its point lies in that universe.
- The same universal quantifier then asserts `∀ (N : (P j).Modules)
  (hN : N.IsInvertible), @IsAmple (P j) N hN`, covering EVERY invertible module,
  independently of L and of the restriction to this summand.
- The final conjunct is `IsAmple ((∐ Y) ⨿ (∐ P)) L ↔ ∀ i, ...`.
  Its right side uses `(tensorPullback (Sigma.ι Y i ≫ coprod.inl)).obj L`.
  The existential proof `h` of its invertibility only supplies IsAmple's dependent
  proof argument; it is not a new mathematical condition, since pullback preserves
  invertibility. Crucially, there is no extra invertibility assumption on the theorem.
- `Scheme.Modules.IsAmple` is the absolute definition including quasi-compactness and
  an affine nonvanishing neighbourhood from a positive tensor power. The project also
  has a different projective-over-a-field predicate `AlgebraicGeometry.IsAmple`;
  this theorem does not use that predicate.
- No condition on b_j pullbacks is needed: they are invertible by pullback and hence
  covered by the universal assertion for N above.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms,
  `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral` (nonempty,
  and sections on each nonempty open form a domain).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, defined as
  `Order.krullDim (IrreducibleCloseds T)` with values in `WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.Limits`: the small discrete colimit instance,
  `AlgebraicGeometry.sigmaOpenCover`, `AlgebraicGeometry.disjoint_opensRange_sigmaι`,
  and the actual `Sigma.ι`/binary coproduct construction. This uses the recorded
  Mathlib match of `lem-weil-pbc-scheme-coproduct-family`, which needs no Lean record.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, the locally rank-one predicate.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`, with the public
  upstream `tensorPullback` functor whose data is inverse image and change of rings.
  The statement uses that actual functor, not the earlier abstract adjoint pullback.
- `Mathlib.Algebra.Field.Defs`: `Field` (the dependency's Mathlib match).
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and `nonvanishingLocus`.

The module also imports the stated proof dependencies via FunctionField,
Morphisms.Affine, PresheafModuleStalkFunctor, AmplePullback,
Modules.InvertiblePullbackTensor, and RingedSiteModules. Shared statement/proof
modules are public imports; imports needed only for the proof plan are plain imports.
The theorem docstring records all six DAG proof steps, including the field construction,
global frame on each singleton, affine pullback, finite subcovers, and gluing by zero
on the complementary clopen subscheme. No extra theorem is postponed.

Sources opened: `literature/stacks-project/properties.tex`, definition-ample (01PS),
and `literature/stacks-project/varieties.tex`, lemma-ampleness-in-terms-of-degrees-components
(0B5Y), including the proof's isolated residue-field point summands. The former's
quasi-compactness plus pointwise affine-section condition is exactly the recorded
absolute predicate. The supporting node itself requires no properness, finite type,
Noetherianity, or base field, and neither does the Lean theorem.

Edge cases checked before writing: I and J both empty gives the empty scheme and
vacuous pointwise ampleness; I empty leaves only finitely many field spectra; J empty
gives the ordinary finite-coproduct criterion. Empty Y_i are allowed because there
is no nonemptiness binder for them and the ampleness pointwise condition is vacuous.
P_j cannot be empty because integrality includes nonemptiness; its dimension condition
is zero rather than minus infinity. Arbitrary fields, including positive characteristic,
are covered. No finite-type assumption is needed: a singleton integral scheme is affine
and its ring equals its local ring, which is a field. Infinite index sets are deliberately
excluded, since infinitely many nonempty affine points need not be quasi-compact.

Searches actually run using `batch2/msearch.py Q17 <item>`:

- LeanFinder: "An invertible module on a finite disjoint union is ample if and only if
  its restrictions are ample, and all line bundles on zero dimensional integral schemes
  are ample". Eight hits: finite affine coproducts, affine-open unions, sigma inclusion
  disjointness and affine-local morphism properties. No matching ampleness statement.
- Loogle: `AlgebraicGeometry.Scheme.Modules.IsAmple, AlgebraicGeometry.IsIntegral`.
  Zero hits; unknown identifier for the project's IsAmple in the Mathlib search service.
- Mathlib grep: `IsAmple|isAmple|ample.*[Cc]oprod` under AlgebraicGeometry. Zero hits.
- LeanSearch: "Absolute ampleness of an invertible sheaf on a finite coproduct of
  schemes and on integral schemes of dimension zero". Eight hits on coproduct existence,
  finite affine coproducts, coproduct presheaf sections and unrelated morphism properties;
  no matching absolute ampleness theorem.
- Direct `rg` of the specified `lean/WeilConjectures` and `lean/Sheaf` trees for IsAmple,
  ampleness and coproduct patterns found the existing absolute definition, pullback
  theorem, and a very-ample-disjoint-union theorem. The latter is projective-over-a-field
  very ampleness and is not this statement. The absolute-affine unit result also does
  not state this coproduct criterion or the arbitrary-invertible-module point clause.
- Direct `grep -rn` for this item's id in `lean/WeilConjectures` returned no declaration.

Validation: `scompile.py Q17 lem-trf-finite-coproduct-ample-with-points <file>` returned
exit 0 after its successful current-server-source fallback (1.5 s). Its initial local
attempt reported OSError 28, no space left on device; this did not prevent server
compilation. No compiler error or non-sorry warning remains.

## Second reading by Q17

I reread the node and the completed Lean signature after compilation. The dispatcher
requires this worker to operate alone and forbids starting other agents, so this is
an explicit second pass by the same worker, not a claim of independent review.
The maintainer's independent review remains the independent reading of this delivery.

The two Finite instances match both finite-set hypotheses without choosing Fintypes.
IsIntegral and hP match each point-summand hypothesis; there is no assumption on Y_i.
The L binder uses the exact nested coproduct from the node. The first conjunct returns
both a field-spectrum isomorphism and ampleness for every invertible module on each
P_j, rather than only for L's restriction. The second conjunct uses the exact canonical
a_i tensor pullback and absolute IsAmple. Its existential invertibility proof supplies
a proof parameter, with no extra input or restriction. It omits conditions on b_j
precisely as required, and the first conjunct explains why they are automatic. The
empty-index and empty-Y cases are preserved. The explicit universes exclude no finite
family, since Mathlib provides smallness for finite index types. No statement mismatch
or correction was found. All declaration variables and universe variables are explicit,
and the file has no diagnostic commands or declarations other than the named theorem.
