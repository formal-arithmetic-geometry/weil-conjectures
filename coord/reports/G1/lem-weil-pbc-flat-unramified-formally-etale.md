## Worker report

The module states `AlgebraicGeometry.flat_unramified_formally_etale`. Its explicit
hypothesis `[Flat f]` renders that `f` is flat. The hypothesis
`h_unramified : LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)`
renders unramifiedness as the node specifies. For affine schemes `T,T'` over `S`,
`IsFirstOrderThickening i` renders the first-order thickening and the `Over S`
instance renders the structure morphism; the equation
`a ≫ f = i ≫ (T' ↘ S)` says that `a` is over `S`. The conclusion
`∃! a', i ≫ a' = a ∧ a' ≫ f = T' ↘ S` gives exactly one lift over `S` with
restriction `a`, clause by clause. The final conjunct `FormallySmooth f` records
the existence half (the definition already quantifies over the same affine
first-order thickenings), while the unique-lift conjunct is the Stacks definition
of formally étale.

Dependency declarations used: `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` (Mathlib); `AlgebraicGeometry.Flat` (Mathlib);
`AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.IsOpenImmersion` (Mathlib);
`AlgebraicGeometry.IsFirstOrderThickening` from
`Sheaf.AlgebraicGeometry.Thickening`; `AlgebraicGeometry.Scheme.Over` (Mathlib);
and `AlgebraicGeometry.FormallySmooth` from
`Sheaf.AlgebraicGeometry.FormallySmooth`.

Edge cases checked: the binders allow arbitrary schemes and arbitrary affine
first-order thickenings, including the identity thickening and zero ideal; no
finite-presentation, nonempty, characteristic, or dimension hypothesis was added.
The universe is shared (`Scheme.{u}`) throughout, so no smaller test universe is
excluded.

Searches made: `msearch.py ... leanfinder` for a scheme-level flat-unramified
lifting theorem (only ring-level formal étale results); `msearch.py ... loogle`
for `AlgebraicGeometry.Flat, AlgebraicGeometry.FormallyUnramified` (related
étale characterizations, no lifting property); `msearch.py ... grep` over
Mathlib AlgebraicGeometry for `FormallySmooth|FormallyEtale|thickening` (no
scheme-level declaration); `rg` over `WeilConjectures` and `lean/Sheaf` for the
item and formal étale declarations (no existing statement). Thus a new theorem
module is required.

## Earlier second reading (a previous round; superseded)

Reading the node and module together: `f : X ⟶ S` is the same scheme morphism;
flatness and unramifiedness are rendered by the two hypotheses without extra
assumptions. Every node clause is present: affine `T,T'`, first-order thickening
`i`, the given map `a` over `S`, existence and uniqueness of `a'`, its restriction
and its structure-map equation, plus the formally smooth and formally étale
consequences. No object or condition is strengthened or dropped.


## Second reading by G1

Read the delivered node, its seven proof steps, all six statement-dependency
nodes and their declaration bodies/signatures. The repository's recorded
`literature/stacks-project/more-morphisms.tex` is absent on this machine;
the local Stacks source at `/home/ubuntu/c1-stacks-review/more-morphisms.tex`
was read instead: lines 1490–1655 (02HG, 04FE, 04FF) and 3064–3106 (02H0).
The accompanying tags/tags verifies all three tags. These source statements
assume arbitrary schemes, with no surrounding base-field, Noetherian,
finite-presentation, separatedness or characteristic hypotheses.

Object/hypothesis/conclusion checklist (all verdicts: exact):

- Schemes X and S: `{X S : Scheme.{u}}`; `Scheme` and `Scheme.Hom` in
  Mathlib/AlgebraicGeometry/Scheme.lean are schemes and locally ringed-space
  morphisms, as def-pc-scheme requires.
- Morphism f: `(f : X ⟶ S)`; its structure map is the very morphism in the node.
- Flatness: `[Flat f]`; the class in Morphisms/Flat.lean is affine-local ring
  flatness, with `Flat.iff_flat_stalkMap` giving exactly the stalk condition
  of def-weil-flat-morphism.
- Unramifiedness: `h_unramified : LocallyOfFiniteType f ∧
  IsOpenImmersion (pullback.diagonal f)`. Read the finite-type class and open
  immersion abbreviation: this is precisely the conjunction recorded by
  def-weil-unramified-morphism, with the actual scheme fibre-product diagonal.
- Affine test schemes T and T': `{T T' : Scheme.{u}}`, `[IsAffine T]`,
  `[IsAffine T']`. Read `IsAffine` in AffineScheme.lean: canonical Spec map
  is an isomorphism, equivalent to the node's affine notion.
- Closed immersion i with square-zero defining ideal:
  `(i : T ⟶ T')`, `IsFirstOrderThickening i`. Read the recorded Thickening
  module: this is `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`, with no hidden
  data or proof holes. Nilpotence supplies equality of underlying spaces.
- Structure map T' to S: `[T'.Over S]`, `T' ↘ S`. Read Scheme.Over in
  Mathlib/AlgebraicGeometry/Over.lean: exactly a structure morphism. T's map
  is the composite `i ≫ (T' ↘ S)` as the node specifies; a separate Over
  instance on T is unnecessary and would only repeat that data.
- Given S-morphism a: `∀ (a : T ⟶ X), a ≫ f = i ≫ (T' ↘ S) →`.
  The equality is exactly the solid square, without extra conditions on a.
- Existence and uniqueness of the S-lift with restriction a:
  `∃! a' : T' ⟶ X, i ≫ a' = a ∧ a' ≫ f = T' ↘ S`.
  Unique existence applies to the conjunction, hence precisely to lifts over
  S. The order of all test objects, hypotheses, a and a' agrees with the node.
- Formally etale consequence: the full universally quantified unique-lift
  conjunct is Definition 02HG itself. There is no scheme-level formally
  etale predicate to import and no new private predicate was introduced.
- Formally smooth consequence: final `∧ FormallySmooth f`. Read the recorded
  FormallySmooth module: it uses exactly these same affine tests and square
  and concludes existence with the same two equations, Definition 02H0.

Edge cases: empty schemes (including Spec of the zero ring), identity
thickenings and zero defining ideals are permitted. If T is empty, square-zero
closed immersion forces T' empty, consistent with unique lifting. No index set,
integer n, nonzero-ring, dimension, characteristic or field assumption occurs.
The single arbitrary universe u includes X, S and all test schemes in the
same category Scheme.{u}; the tests do not live in a smaller independent
universe. This matches the existing FormallySmooth dependency. Every variable
and universe was checked by eye to be bound.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: “flat scheme morphism with open diagonal unique lifting square
  zero closed immersion”; found Flat and the open-diagonal/formal-unramified
  instances, no existence-and-uniqueness lifting theorem.
- Loogle: `"FormallyUnramified.hom_ext"`; opened the hit in
  Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:193. It gives
  only at most one lift, assumes formal unramifiedness, and gives no existence.
- LeanSearch: “A flat unramified scheme morphism has a unique extension across
  square zero affine closed immersions”; service returned Internal Server
  Error, recorded as unavailable, with no absence inference from that service.
- Scoped Mathlib grep `FormallyEtale|FormallySmooth|hom_ext` in
  AlgebraicGeometry/Morphisms, plus direct rg through all Mathlib
  AlgebraicGeometry, all WeilConjectures and lean/Sheaf for formal etaleness,
  smoothness and thickenings. Ring-level formal etaleness and stalk-level
  smoothness do not state this scheme lifting theorem. Project definitions
  FormallySmooth and IsFirstOrderThickening are reused. No existing theorem
  or competing scheme-level formally etale predicate was found.

Mismatch repaired: H8, the original proof docstring compressed the seven
steps to “flatness and the diagonal argument give existence”. Replaced that
paragraph with all seven steps, naming the node dependencies and explaining
conormal base change, restriction to the diagonal, vanishing, the square-zero
ideal argument and the universal lift. H9: removed the unused PullbackCarrier
import; no statement, hypothesis, conclusion, dependency or definition changed.
The node lean.statement now reproduces the unchanged signature verbatim,
including its line breaks. No new nodes or dependency modules were needed.
The only theorem proof is still `sorry`; no definition was added or hollowed.

Validation: scompile.py on the repaired module returned exit code 0, compiled
in 1.7 seconds, with no warnings or errors. deliver2.py --no-push printed OK: the commit
passes preflight and compiles. The final push uses deliver2.py.
