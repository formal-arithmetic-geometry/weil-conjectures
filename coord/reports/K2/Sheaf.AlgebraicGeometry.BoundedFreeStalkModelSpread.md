## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.Scheme.spread_boundedFree_stalkModel`
with a compiling reduction to two strictly smaller intermediate statements. The original
signature, universes, instance binders, declaration name and visibility are unchanged.
The original node's proof, proof dependencies and proof origin follow the new Lean argument.
No definition or existing statement was changed, and no other group's module was adapted.

Added two modules, imported privately by the item's module:

- `Sheaf.AlgebraicGeometry.BoundedFreeStalkComplexLift` lifts a bounded free stalk complex
  as a complex, with its original ranks, without any given derived object or comparison.
- `Sheaf.AlgebraicGeometry.PerfectStalkDerivedIsoSpread` extends a derived stalk comparison
  between two existing local perfect models. It neither constructs a complex nor prescribes
  its ranks or bounds.

The combining proof constructs the finite-free retractions making the lifted complex
strictly perfect, transports the local representative along `eG`, and composes `eF.symm`
with the derived image of the complex-stalk isomorphism. After shrinking, it transports
bounds with `Functor.map_isZero` and ranks with `overFunctorMap`, `mapFreeIso` and
`overMapUnitIso`. Finally it composes the derived restriction of `eG.symm`,
`mapDerivedCategoryFactors`, and the descended comparison. These are real Lean proofs;
no anonymous, private or in-definition holes were introduced.

Validation: all three modules compile together in import order through `lcompile.py`,
without errors or warnings. A textual comparison checked the original theorem signature
verbatim against the repository. All delivered Lean lines are at most 100 characters.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.spread_boundedFree_stalkModel`, node
`lem-sc-bounded-free-stalk-model-spread`. There are no `sorry`s left in the original module.

Added, each in its own module with proof exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_boundedFree_stalk_complex_lift`, node
  `lem-sc-bounded-free-stalk-complex-lift`.
- `AlgebraicGeometry.Scheme.exists_affine_restriction_iso_of_perfect_stalk_iso`, node
  `lem-sc-perfect-stalk-derived-iso-spread`.

This is a decomposition, not an unconditional proof: one upper hole closed and two lower
holes added. The combining theorem still depends on these two unfinished theorems.
No claim of a positive net hole reduction is made.

Edge cases checked mathematically before stating the helpers: a point's stalk ring is
nonzero, so a rank-d free module that is zero forces d = 0. Thus empty degree intervals
and d identically zero give the zero complex without missing degrees. A stalk complex
can lift without a prescribed global derived object: lift its finitely many differential
matrix entries and the square-zero equations, then use ordinary direct image from the
chosen open as the auxiliary global complex. This direct image need only preserve zero
objects and the stalk inside the open; no false exactness claim about direct image is used.
The comparison extension requires both local perfectness assumptions: no claim that an
arbitrary stalk isomorphism spreads is made. Affine refinements are taken inside an open
intersection, not by assuming that an intersection of affine opens is affine. No Noetherian
or separatedness hypothesis is added. The stalk and sheaf derived universes remain separate.

## No longer needed

Removed all six original proof-only imports from the item's module:

- `Sheaf.Algebra.Homology.AffinePerfectColimitDescent`.
- `Sheaf.AlgebraicGeometry.AffinePerfectHomColimit`.
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`.
- `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`.
- `Sheaf.Algebra.Homology.ModuleStalkExact`.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.

The first and third modules, with nodes `lem-pc-affine-perfect-colimit-descent` and
`lem-weil-pbc-finite-projective-standard-free-cover`, are no longer needed on this proof
route, including by either new helper. Direct lifting of free differential matrices
retains the prescribed ranks immediately, so the route does not first descend projective
terms and then find a free cover and identify ranks. Descendants used only for these two
nodes are likewise unnecessary on this route. Other target paths may still reach them;
this report does not claim they vanish from the entire target closure.

The other four removed direct imports remain needed by the new comparison helper, and
localization is also needed by the lifting helper. They were relocated, not pruned.
The two original public imports remain: the original statement uses their declarations.
No blueprint unit statement or realized step was bypassed; the item's unit
`sk-prop-av-cube` has empty realized-node lists, which were not modified.

## Where the brief, the DAG or earlier work was wrong

No false existing statement was found. The original plan is mathematically valid, but
its ring-level declarations do not directly supply the scheme/over-site/stalk comparisons
needed to apply them. The two new statements isolate that glue and separate the construction
from the comparison. The plan's projective descent and subsequent free-cover detour is
unnecessary for an already finite-free stalk complex with specified bases.

The original spreading discussion cites 00CM for the principal-localization colimit;
its recorded dependency actually cites 00CR, which is the relevant source used here.
The local `literature/stacks-project/*.tex` sources are absent on this machine. Read
Stacks Tags 0BCD, 0BC7 and 09RE on the official Stacks website; the source paths retained
in nodes are the project's canonical document identifiers. The finite matrix/direct-image
expansion is recorded as written by a worker, following those arguments.

Searches: LeanSearch was attempted separately for both new statements and returned
Internal Server Error, without a verdict. LeanFinder returned eight hits for each query,
all ordinary stalk/localization/spreading tools, with no complex lift or perfect derived
comparison extension. Loogle returned no hits for `CochainComplex, "stalk"` and
`"perfect", "stalk"`. Mathlib and project source grep found ordinary stalk isomorphisms,
free loci and rank functions, but no matching complex theorem. Project single-degree
homotopy-spreading modules start with existing complexes and use a different carrier;
the internal-Hom stalk-localization lemma assumes Noetherianity and a coherent degree-zero
source, so neither supplies these statements. Blueprint searches for `stalk complex`,
`bounded free`, `stalk isomorphism` and `09RE` found no matching imported node.

## New nodes

`lem-sc-bounded-free-stalk-complex-lift` records the first half of the spreading argument:
construct a bounded complex by lifting finite differential matrices and their equations,
retaining ranks, without reference to `E`, `G`, local perfectness or a derived comparison.
It is sourced to the finite-presentation argument in 0BC7 and the spreading paragraph of
0BCD, with 00CR. It uses ordinary direct image only as an auxiliary global extension.

`lem-sc-perfect-stalk-derived-iso-spread` records the other half: descend a derived
isomorphism and its inverse between already available local perfect models, then detect
both inverse identities after shrinking. It is sourced to the affine full-faithfulness
argument of 09RE and 0BC7 (2), with 06Z0 and 00CR. It is independent of prescribed ranks
and model construction. Both nodes inherit the original chapter and unit and point to
its existing blueprint ancestor. No change record is needed because no existing interface
was changed.

## Second reading by K2

1. **Unchanged interface: PASS.** Read all three modules and diffed the original module
   against the repository. The existing theorem signature, including all universes,
   binders, hypotheses and conclusion, is byte for byte identical. No definitions,
   existing visibility or public imports changed; no forced adaptations or change
   records are needed. The only changes to the existing node are proof, proof_deps
   and proof_origin.
2. **Proof and kernel checks: PASS as a decomposition.** Compiled all three modules in
   import order using lcompile.py, with no errors or warnings. Independently compiled
   scratch copies with #print axioms for each of the three declarations: each reports
   exactly propext, Classical.choice, Quot.sound and sorryAx. The sole original hole
   is closed; exactly the two reported named public helper theorems retain := by sorry.
   No prohibited declarations or data definitions occur. Existential witnesses are
   eliminated inside the theorem proof, not chosen to define arbitrary public data.
3. **Split statements: PASS.** The complex-lift statement needs no derived comparison;
   finite differential matrices and their finitely many square-zero equations descend,
   and ordinary open direct image gives a bounded global auxiliary complex. The second
   statement fixes both complexes and only descends a comparison and inverse identities
   between locally perfect models. Neither restates the original statement. Checked
   zero ranks, empty degree intervals, one-term complexes, empty schemes (no point),
   and nonseparated schemes (take an affine refinement inside the intersection).
   Both have complete sourced docstrings and matching new nodes. Independently read
   Stacks [0BCD](https://stacks.math.columbia.edu/tag/0BCD),
   [0BC7](https://stacks.math.columbia.edu/tag/0BC7),
   [09RE](https://stacks.math.columbia.edu/tag/09RE) and
   [00CR](https://stacks.math.columbia.edu/tag/00CR).
   New LeanFinder searches for square-zero matrix descent with fixed bases and descent
   of inverse identities between perfect objects found only ordinary module and scheme
   results; Loogle's Perfect/Iso query found unrelated results. Read the project's
   affine free-complex lift, stalk chain-map pair lift and homotopy shrinking modules:
   they assume existing sheaf complexes or single-degree comparison targets, so do not
   close either helper. Source grep of Mathlib, Sheaf and WeilConjectures found no
   matching shortcut. Neither helper can be closed by a short application of these APIs.
4. **Top-down route and pruning: PASS.** Checked every composition direction, finite-free
   retraction, bound transport, restriction-composition and free-sheaf comparison in
   the combining proof. The original six proof-only imports are accounted for under
   No longer needed: two are bypassed, four remain behind the comparison helper.
   The original perfect-complex definition remains used. The new helpers retain
   proof-plan imports privately; their statement imports supply the actual carriers.
   No new proof-only public import was introduced into the existing module. The
   unchanged sk-prop-av-cube realized record is {statement: [], steps: [[]]}; this
   reduction is below its unit route. One hole closed and two added is a decomposition,
   with net -1 holes on this route, not an unconditional or positive-net proof.
5. **DAG agreement: PASS after clarification.** Checked all Lean statement records
   verbatim and every proof_deps set against the union of step uses. New nodes have
   their sources, searches, creation, blueprint ancestry, chapter/unit and Lean records.
   The combining node names the two helpers used by Lean. Its Mayer-Vietoris dependency
   is retained because that node also owns moduleRings and the open-restriction
   additive/exactness instances used by this proof; the exact-sequence theorem itself
   is not invoked.

Second-reading changes: clarified the existing node's final proof step to identify
which declarations of lem-sc-derived-hom-mayer-vietoris are used, and appended this
review with independent searches and axiom checks. The Lean proof and statements
needed no repairs. All scratch axiom-probe copies were removed before delivery.
