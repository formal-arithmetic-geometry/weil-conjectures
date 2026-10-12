## What changed

The original theorem `AlgebraicGeometry.Scheme.exists_finiteFree_refinement_of_isStrictlyPerfect`
now constructs its complex as termwise restriction of P. Apply the new finite-family sheaf
trivialization lemma to the finite interval of degrees. Restriction preserves the original
bounds; outside the interval use the zero-object isomorphism with the free rank-zero sheaf.
The derived restriction comparison is proved using overFunctorMap,
mapDerivedCategoryNatIso, mapDerivedCategoryCompIso and mapDerivedCategoryFactors.
The existing signature and definitions are unchanged. The new geometric statement has its
own module `Sheaf.AlgebraicGeometry.FiniteRetractSheavesAffineTrivialization` and node.
Its import and `Mathlib.Data.Int.Interval` are proof-only imports of the original module.

## Proved and sorry left

Closed existing syntactic hole:
`AlgebraicGeometry.Scheme.exists_finiteFree_refinement_of_isStrictlyPerfect`.
Added hole:
`AlgebraicGeometry.Scheme.exists_affine_trivialization_of_finite_retracts`
(node `lem-pc-finite-retract-sheaves-affine-trivialization`). This is the only delivered
sorry, a public named theorem with a complete docstring proof. It states simultaneous
trivialization of a finite family of split finite free sheaf summands, without a complex,
differential, degree bounds or derived-category data. The target combines this geometric
part with actual proofs of boundedness, rank-zero terms and derived transport.
This is a decomposition: one old hole closed, one new hole added, net zero; zero of the
one original theorem is proved without sorryAx in its dependency closure. No arbitrary
complex data is chosen from an unproved existence theorem: F is explicitly the restriction
of the given P. No new definitions are introduced.

## No longer needed

Removed from the item's direct imports:
`Sheaf.RingTheory.FiniteProjectiveStandardFreeCover` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
They now belong to the geometric helper's proof plan and remain proof-only imports there.
Correspondingly the old direct proof dependencies
`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-finite-projective-standard-free-cover` move to the new node.
They remain indirect dependencies, so no library module is claimed globally pruned.
`def-pc-perfect-complex` remains a direct dependency. The unit's realized fields are
unchanged; this node realizes no unit statement or unit step.

## Where the brief, the DAG or earlier work was wrong

The first draft changed the spelling of the existing target signature; it is restored
byte for byte. Its refinement-data hole still contained nearly the whole complex
construction. The restriction-isomorphism hole was unnecessary: a proved private
restrict_model in PerfectCommonAffineModels already supplies the direct comparison
argument. The bounds helper was unused. The three draft new nodes lacked actual search
records and full Lean signatures; two had placeholder mathematical statements, and the
original node still described the previous proof. All are replaced by one precise node
for just the geometric step and an updated proof plan. The draft change records concerned
unlanded draft interfaces, not any existing library interface, so they were removed.
The cited Stacks .tex files are absent on this machine. The source tags were read directly
at https://stacks.math.columbia.edu/tag/00NX, /tag/01IA and /tag/08C4 rather than treating
definition tags as a proof of the construction. The geometric argument is the existing
plan's idempotent/finite-projective reduction, not a new unsupported route.

## New nodes

`lem-pc-finite-retract-sheaves-affine-trivialization`: simultaneous local trivialization
of finitely many retracts of finite free sheaves, in its own module. Its node records
complete hypotheses/conclusion, affine idempotent splitting and finite projective free
cover steps, their dependency union, source, searches, blueprint provenance and verbatim
Lean signature. LeanSearch returned Internal Server Error; LeanFinder, Loogle and local
grep found no exact statement. No change record is necessary for an existing signature.

## Second reading by V2

1. Compared delivered modules against repository source with diff. The sole existing
declaration's signature is byte for byte unchanged; its docstring is unchanged. No target
statement or definition changed. The helper module is new.
2. Compiled both modules locally through lcompile.py in import order, with no errors or
warnings. Only the named geometric theorem contains sorry. No axiom, unsafe, opaque,
implemented_by or extern declarations and no definitions were added. Explicit scratch
#print axioms checks and deliver3's declaration probe verify the allowed axioms plus
sorryAx from the recorded open geometric step.
3. Read the new sheaf statement and its proof, including the localized-site equivalence
and affine splitting of an idempotent. Checked empty finite family, zero summands, varying
ranks, empty degree interval and empty U; none needs extra hypotheses. It is strictly the
termwise geometric part, with the complex and derived conclusions proved separately.
Searched with different language (finite families, retracts, idempotents and simultaneous
trivialization). No applicable library theorem supplies this interface. Every remaining
hole has a real node and a complete proof docstring.
4. Reused the existing nested restriction comparison proof; removed its needless hole
and the unused bounds helper. Restored the shortest reduction from the given complex
instead of existentially choosing another. Imports used only by proofs are private.
All old direct proof dependencies are either retained or explicitly relocated above;
no claim of global pruning. Checked sk-thm-picard-duality.realized: this item is absent,
and the unit's route and records are preserved.
5. Rewrote the original node's proof and dependency union to match the Lean argument.
Replaced incomplete draft nodes with one fully recorded geometric node in its own module.
The new statement cites base scheme/sheaf notions, not the original theorem, so there is
no circular statement dependency. Its proof uses the existing algebraic cover and affine
tilde-Gamma nodes. The exact signature is recorded in lean.statement.

Second reading changed: restored signature, removed unused helper and artificial change
records, replaced near-restatement holes with one sheaf-only geometric lemma, proved
bounds/zero terms/derived transport, moved the lemma into its own module, repaired DAG,
searches and report. Verdict: valid decomposition, not a complete proof.
