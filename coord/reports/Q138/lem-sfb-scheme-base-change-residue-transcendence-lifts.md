## Worker report

Item: `lem-sfb-scheme-base-change-residue-transcendence-lifts`.
Group: Q138. Stage 2.

The module `Sheaf.AlgebraicGeometry.BaseChangeResidueTranscendenceLifts` states
`AlgebraicGeometry.residue_trdeg_base_change_le_and_exists_eq`. Its one theorem has
proof `sorry`; there are no new definitions or auxiliary theorems. The node changes
only in `lean`. All five recorded statement dependencies have usable Mathlib interfaces.

The inherited BLOCKED ending concerned an accepted stage-1 split by O2, not a
stage-2 statement. The current node has `reviewed.result = pass`, no `lean` or
`reviewed_lean`, and its `coord/queue.tsv` entry has stage 2, action `state`.
There is no released repair note. This delivery preserves the accepted split.

Source checked: `literature/stacks-project/morphisms.tex`,
`lemma-dimension-fibre-after-base-change`, Tag 02FY, parts (2) and (3).
Part (2) gives precisely the transcendence-degree inequality; part (3) gives a
compatible lift attaining equality. The node asks only for these transcendence-degree
clauses, not the additional local-dimension conclusions in that source.

Clause-by-clause rendering:

| Node data or clause | Lean rendering |
| --- | --- |
| Schemes U, B, B' | `{U B B' : Scheme.{u}}`, with explicitly declared `universe u` |
| Morphism f from U to B | `(f : U ⟶ B)` |
| f locally of finite type | `[LocallyOfFiniteType f]` |
| Arbitrary morphism g from B' to B | `(g : B' ⟶ B)`, with no property assumption |
| U' = U times_B B' | `(pullback f g : Scheme.{u})` |
| q and f' | `pullback.fst f g` and `pullback.snd f g` |
| Every u' | Universal quantifier in the first conjunct, over the points of the scheme pullback |
| u = q(u') | Every right-hand residue-field expression in the first conjunct uses `(pullback.fst f g) u'` |
| b' = f'(u') | Every left-hand base field uses `B'.residueField ((pullback.snd f g) u')` |
| b = f(u) | Right-hand base field `B.residueField (f ((pullback.fst f g) u'))` |
| Canonical residue-field extensions | The explicit algebra argument of each `@Algebra.trdeg` is the appropriate `(Scheme.Hom.residueFieldMap ...).hom.toAlgebra` |
| Degree inequality | The first conjunct compares these two `Algebra.trdeg` cardinals with `≤` |
| Every u and b' with g(b') = f(u) | `∀ (u : U) (b' : B'), g b' = f u → ...` in the second conjunct |
| Existence of u' | `∃ u' : (pullback f g : Scheme.{u}), ...` |
| q(u') = u | `(pullback.fst f g) u' = u` |
| f'(u') = b' | `(pullback.snd f g) u' = b'` |
| Equality of degrees for the lift | Last conjunct equates the canonical degree along `pullback.snd f g` at u' to that along f at u |
| Base field of the lift is kappa(b') | The degree is written at `f'(u')`, and the preceding projection equality identifies this point with b'; no arbitrary algebra or transport hypothesis is introduced |
| No flatness, surjectivity, separation, quasi-compactness, Noetherian assumption | None appears among the binders |
| Empty schemes permitted | No nonempty or point-existence hypothesis appears |

All variables and universes are explicit. A single universe for these scheme objects
is Mathlib's ambient category of schemes; its universe is arbitrary. No separate
small universe of test objects or field extensions is quantified over. The degrees
are cardinal-valued `Algebra.trdeg`, with no truncation to natural numbers.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (only the locally finite type clause is needed).
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies existence for schemes.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`. The former is the quotient
  of the local stalk by its maximal ideal; the latter is induced by the stalk map.
- `def-kun-transcendence-degree`:
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`.

The proof dependencies are retained as plain imports, using upstream modules rather
than retired Sheaf twins: `WeilConjectures.RingTheory.FibrePrimesResidueFields`,
`WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension`, and
`WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg`. The remaining proof
dependencies are Mathlib leaves, imported through Pullback.IsPullback.Basic,
FiniteType, Spectrum.Prime.Noetherian, Flat.FaithfullyFlat.Basic and .Algebra,
RingHom.FaithfullyFlat, Ideal.KrullsHeightTheorem, and Ideal.MinimalPrime.Basic.
The affine-spectrum tensor isomorphism is in the public Pullbacks import, which
also provides the scheme pullback needed by the statement. The theorem docstring
records all seven proof steps with their DAG dependency identifiers.

Edge cases checked mathematically before writing:

- Empty U or B': there are no pullback points and no compatible pairs, so the
  respective universal clauses are vacuous. No lift is asserted without a pair.
- Identity base change: the unique corresponding lift preserves the degree.
- The generic point of affine one-space over k, base-changed to K = k(a), with a
  transcendental: the lift `(t-a)` has degree zero over K, while the original
  generic point has degree one over k. The generic lift `(0)` has degree one.
  Thus the inequality can be strict, and the existence clause must not require
  equality for every lift. The Lean makes exactly that distinction.
- A degree-zero point and a field extension: all lifts have degree at most zero,
  and existence remains the nonempty tensor-product prime assertion.
- Nonreduced schemes (e.g. k[t]/(t²)) are allowed: only their residue fields enter.
- Non-Noetherian bases and non-quasi-compact morphisms are permitted; the proof
  obtains Noetherian rings only on finite type charts over residue fields.

Searches performed for this assignment (logs in `searches.jsonl`):

- `msearch.py ... leanfinder`, query "Residue field transcendence degree decreases
  under arbitrary base change of a locally finite type scheme morphism and there
  is a lift attaining equality": eight hits, consisting of residue-field maps,
  preimmersions from residue fields, an etale factorization lemma,
  `finite_appTop_of_universallyClosed`, transcendence-degree tower inequalities,
  and `RingHom.EssFiniteType.residueFieldMap`. None states these two clauses.
- `msearch.py ... loogle`, query `"trdeg", "residueField"`: zero hits.
- `msearch.py ... grep`, query `trdeg|transcendence`, subdirectory
  `AlgebraicGeometry`: zero hits.
- `rg` on `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry`, query `trdeg|transcendence`: inspected the
  residue-degree, finite-type dimension-formula and field-specialization matches;
  none asserts arbitrary scheme base change together with equality lifts.
- `rg` over all `lean/WeilConjectures` and `lean/Sheaf` for the exact node id:
  no hits. Broader searches `trdeg.*(pullback|residueField)|residueField.*trdeg`
  and `residueFieldTrdeg` found results over a fixed field, local dimension
  formulas, and support bounds, not the present two-clause assertion.
- The existing `Scheme.residueFieldTrdeg` in
  `WeilConjectures.AlgebraicGeometry.Sites.SupportDimension` is specialized to a
  morphism to Spec K. Its definition and `residueFieldHomOfOver` were read;
  neither replaces the relative residue-field extension here. This delivery
  uses `Algebra.trdeg` and the already recorded canonical residue maps directly,
  and introduces no parallel notion.
- Name-clash search in Mathlib, upstream, Sheaf, and `dag/lean_names_upstream.json`
  found no `residue_trdeg_base_change_le_and_exists_eq`.

No statement correction, new nodes, dependency repair, or disputed statement is needed.

## Second reading by Q138

The dispatcher explicitly forbids starting another agent; this is a second clause
audit by the same worker, not a claim of independent review. The maintainer supplies
the independent reading after delivery.

Reopened the node and the complete theorem signature. Checked all three schemes,
both morphisms, the locally finite type assumption only on f, the two projections,
the canonical scalar structures in all four transcendence-degree expressions, the
universal first clause, the compatible-pair condition, the existential point, both
projection equalities, and the final equality. The degree at `f'(u')` in the last
clause is exactly the degree at b' using its explicitly asserted projection
equality. No clause or hypothesis differs from the node. No new mathematics was
added. The first compiler pass needed an explicit `: Scheme.{u}` annotation on
the polymorphic pullback in the two point binders; this changes no mathematical
object and avoids elaborating a pullback in the category of types.

## Validation

`scompile.py Q138 lem-sfb-scheme-base-change-residue-transcendence-lifts` compiled
the delivered file cleanly in sandbox and library modes (1.4 seconds each),
with no errors or warnings. `deliver2.py ... --no-push` then reported
`OK (dry run)`: the delivery passes server preflight and per-file compilation.
