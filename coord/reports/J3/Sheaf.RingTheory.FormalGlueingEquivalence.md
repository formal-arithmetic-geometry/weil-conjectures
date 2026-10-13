## What changed

The existing signature of `FormalGlueing.exists_canonical_equivalence` is unchanged.
Its proof now combines three strictly smaller statements with real Lean proofs of
comparison/swap bijectivity and faithfulness. Faithfulness uses the injectivity clause
of `RingTheory.formalGlueingComplexExact`: equality of canonical maps is transported
through the supplied HEq equations, evaluated on `1 tensor m` and `m/1`, and injectivity
recovers equality of the original linear maps.

Three new modules isolate the remaining source arguments, one public holed theorem
per module: `Sheaf.RingTheory.FormalGlueingCanonicalFunctor`,
`Sheaf.RingTheory.FormalGlueingMorphismLifting`, and
`Sheaf.RingTheory.FormalGlueingEssentialSurjectivity`. The first only constructs the
prescribed functor (without flatness); the second only proves surjectivity on Hom sets;
the third only algebraizes an object. None restates the entire equivalence. No new
definitions choose data from an unproved existence theorem; the functor is extracted
locally in the upper theorem's proof, and its object and map data are fully prescribed.
The essential-surjectivity lemma needs only the prescribed objects, not map equations.

The DAG route now records these three obligations and the direct faithfulness proof.
The eleven original source steps remain in the new nodes grouped as 1–2, 3–4 plus 6,
and 7–11; step 5 is implemented in the upper theorem. The unit's realized steps are
unchanged and no unit is bypassed. Every remaining theorem has its source and a full
natural-language argument in its docstring and DAG node.

All four modules compile together in import order without errors or warnings using
`lcompile.py --all`. The upper theorem has no syntactic sorry, but depends on the three
new holes and the pre-existing holed canonical-map and exact-complex lemmas.

## Proved and sorry left

Closed upper hole: `FormalGlueing.exists_canonical_equivalence`
(`prop-weil-pbc-formal-glueing-equivalence`). Its component-bijectivity and faithfulness
arguments are actual proofs from existing declarations. The full equivalence is a
**decomposition**, not a sorry-free proof of the mathematical result.

Added holes, each with proof exactly `:= by sorry`:

- `FormalGlueing.exists_canonical_functor`
  (`lem-weil-pbc-formal-glueing-canonical-functor`).
- `FormalGlueing.canonical_map_surjective`
  (`lem-weil-pbc-formal-glueing-morphism-lifting`).
- `FormalGlueing.canonical_essentially_surjective`
  (`lem-weil-pbc-formal-glueing-essential-surjectivity`).

No sorry remains in the item's module; no definition or private declaration contains
sorry. Holes closed: 1. Holes added: 3. This is a decomposition, nominal net -2 before
ledger accounting of the pinned target closure. No claim of net proof progress is made.

Edge cases checked against the source argument before stating the lemmas: t = 0
(the quotient hypothesis forces the ring map to be an isomorphism); zero generators
(zero localizations); I = R (ideal-power torsion terms vanish); zero modules; arbitrary
universes (all constructions stay inside max u v w). The functor construction does
not require flatness or a quotient isomorphism. Morphism lifting asserts no uniqueness;
uniqueness is proved by faithfulness in the upper theorem. Algebraization asserts no
fully-faithful property and requires no prescribed morphism components.

## No longer needed

Removed direct proof imports from the item's module:

- `Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso`.
- `Sheaf.Paper.TorsionModuleFlatBaseChangeIso`.
- `Sheaf.RingTheory.FormalGlueingH0Localization`.
- `Sheaf.RingTheory.TorsionExtensionFlatDescent`.

These remain needed inside the new essential-surjectivity obligation and its imports;
this is relocation of dependencies, not pruning them out of the target closure. Their
node IDs, respectively, are `lem-weil-pbc-torsion-submodule-flat-base-change-iso`,
`lem-weil-pbc-torsion-module-flat-base-change-iso`,
`lem-weil-pbc-formal-glueing-H0-localization`, and
`lem-weil-pbc-torsion-extension-flat-descent`. The other original proof dependencies removed from the upper node are
`def-weil-pbc-module-localization` (used in the canonical-functor obligation) and
`lem-weil-pbc-localization-module-exact` (used in essential surjectivity). They are
also relocated, not globally pruned. None of the original eleven source-step
dependencies is globally dispensable by this decomposition. No globally pruned node
or module is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement correction or forced adaptation is made. The canonical-map declaration
supplies fraction formulas and bijectivity but does not itself state the canonical
object square/cocycle or naturality equations; construction still requires those
arguments. A direct attempt to construct the object exposed that a chart localized
as an R_f-module, then restricted to R using Module.compHom, is not definitionally
the same bundled R-module as the original localization. The scalar actions must be
identified and structural maps transported. This is a missing glue argument, not a
false statement. The functor-construction docstring records it explicitly.

LeanFinder searches returned flatness/localization lemmas and filtered-colimit
surjectivity, not the required formal glueing clauses. Loogle found
`LinearEquiv.ofBijective` and its application identities. Grep of Mathlib's ModuleCat
and RingTheory sources found no formal-glueing equivalence. Whole-blueprint searches
found no duplicate of the three isolated obligations. LeanSearch was unavailable
(Internal Server Error) for all three obligation queries; its unavailability is
recorded without a no-match verdict in each new node.

The local literature directory contains lists but not the Stacks source text. The
source statements/proofs were checked on the authoritative tag pages:
https://stacks.math.columbia.edu/tag/05EL,
https://stacks.math.columbia.edu/tag/05EM, and
https://stacks.math.columbia.edu/tag/05ER. These confirm the cited construction,
left-quasi-inverse, and extension-descent route. Existing source paths are retained
in the DAG so they agree with the project's literature catalogue.

## New nodes

`lem-weil-pbc-formal-glueing-canonical-functor`:
`FormalGlueing.exists_canonical_functor`, in the new canonical-functor module.
It isolates original steps 1–2: object coherence, map compatibility and functor laws.
Its statement does not assert equivalence or any flat/quotient hypothesis.

`lem-weil-pbc-formal-glueing-morphism-lifting`:
`FormalGlueing.canonical_map_surjective`, in the new morphism-lifting module.
It isolates original steps 3–4 and 6: compatible families, unique preimages from the
exact complex, linearity and agreement of all components. It asserts only existence
of a lift; the upper theorem supplies injectivity.

`lem-weil-pbc-formal-glueing-essential-surjectivity`:
`FormalGlueing.canonical_essentially_surjective`, in the new essential-surjectivity
module. It isolates original steps 7–11: H0, local bijectivity, torsion kernel/cokernel,
vanishing kernel, extension descent and a componentwise isomorphism.

All nodes are under `dag/nodes/sec-proper-base-change/`, inherit chapter and unit,
record their exact Lean signatures, source steps, proof-dependency unions, blueprint
ancestor, and search results. No change record is needed because no existing
statement, definition or public import was changed.

## Second reading by J3

1. Compared the delivered target module with the repository version. The theorem signature of
`FormalGlueing.exists_canonical_equivalence` is unchanged byte for byte; only proof text and
proof-only imports changed. Verdict: pass.

2. Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds without
errors or warnings. The target has no remaining `sorry`; the three split theorem bodies are the
only new sorries, each named and documented. No `axiom`, `unsafe`, `opaque`, `extern`, or hollow
definition was introduced. Scratch copies with `#print axioms` for all four declarations
show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter
comes from the explicitly open statements. Scratch copies were removed. Verdict: pass.

3. Checked the three split statements against their declarations and the source route. Each is a
strictly smaller obligation: construction of the canonical functor, surjectivity on Hom sets, and
essential surjectivity on objects. None restates the composite equivalence, and the edge cases
listed above are covered by their hypotheses and conclusions. Verdict: pass.

4. Checked the proof route and imports. The upper proof uses comparison/swap bijectivity,
canonical-map equations, and injectivity of the formal glueing complex; the unresolved source
arguments remain isolated in the three smaller theorems. Removed imports are proof-only and are
listed above; no unit step is bypassed. Verdict: pass.

5. Checked the DAG nodes against the Lean declarations, including signatures, proof dependencies,
proof origins, chapter and unit, and the unit's realized route. The three new nodes carry complete
source proof descriptions and the upper node records the direct faithfulness route. Verdict: pass.

Changes made in this second reading: completed `## No longer needed` with the two omitted
relocated node dependencies, normalized the existing node's Lean signature record to the exact
source formatting, and appended this review. No Lean proof or statement required repair.
Independent fresh LeanFinder, Loogle and grep searches found no shorter matching theorem;
Stacks tags 05EL, 05EM and 05ER were reread on their authoritative pages.
