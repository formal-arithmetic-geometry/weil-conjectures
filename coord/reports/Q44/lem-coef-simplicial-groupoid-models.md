## Worker report

The delivery states `lem-coef-simplicial-groupoid-models` in
`lean/Sheaf/CategoryTheory/SimplicialGroupoidModels.lean`.  Its hypothesis
`(X : SSet.{u})` is an arbitrary simplicial set in the fixed small universe, and
`(hX : SSet.KanComplex X)` renders the source convention that the small space is
represented by a Kan complex.  The conclusion is rendered clause by clause as
follows:

* `∃ G : SimplicialGroupoid.{u}` supplies a small simplicial category with one
  constant object type.
* `G.IsFibrant` is `IsLocallyKan G.carrier`, namely
  `∀ x y, SSet.KanComplex (hom G.carrier x y)`.
* `∃ e : nerveFunctor.obj G.carrier ⟶ X` supplies the coherent-nerve comparison
  map, and `SSet.Enhanced.IsWeakHomotopyEquivalence e` renders the requested
  equivalence of spaces using the project's existing weak-homotopy convention.

The theorem uses the recorded declaration
`CategoryTheory.coherent_nerve_comparison` from
`Sheaf.CategoryTheory.CoherentNerveComparison` through the public import of the
new definition module; this is the node's `lem-coef-coherent-nerve-comparison`
dependency.  The item's other dependency,
`SSet.Enhanced.Algebroid.completeCategory` and its supporting declarations, is
recorded in the node and is part of the source universe convention; the theorem
module does not need to unfold it.

The missing notion required by the statement is supplied by the new definition
node `def-coef-simplicial-groupoid`, in
`lean/Sheaf/CategoryTheory/SimplicialGroupoid.lean`.  Its `SimplicialGroupoid`
structure has a `carrier : SCat.{u}`, simplicial inverse maps
`inv : ∀ x y, hom carrier x y ⟶ hom carrier y x`, and `left_inv`/`right_inv`
fields quantified over every degree and simplex.  The helper definitions
`simplicialGroupoidComp` and `simplicialGroupoidId` render enriched composition
and the simplicial identity simplex.  The inverse maps are simplicial maps, so
compatibility with all simplicial operators is part of their type.  The
`IsFibrant` predicate is the local-Kan condition on all mapping simplicial sets.

Edge cases checked before writing the statement were the empty space (the
existential permits an empty object type), a point, a discrete space, a
nonconnected space, empty mapping simplicial sets, degree zero, and arbitrary
simplicial degree.  No basepoint, connectedness, nonempty mapping-set, or extra
universe equality is imposed.

Searches for the missing notion were run with:

* `msearch.py ... leanfinder "strict simplicial groupoid with degreewise inverses
  and Kan mapping simplicial sets"`: only quasicategory and strict-Segal hits;
  no simplicial-groupoid declaration.
* `msearch.py ... loogle "CategoryTheory.SimplicialCategory, Groupoid"`: zero
  joint hits (the tool reported `Groupoid` as unknown in that query).
* `msearch.py ... grep "simplicial.*groupoid|groupoid.*simplicial"
  AlgebraicTopology`: zero hits in Mathlib.
* `rg` over `WeilConjectures` and the project's `lean/Sheaf`: no declaration of
  a strict simplicial groupoid with degreewise inverses.

## New nodes

`def-coef-simplicial-groupoid` is the new definition node described above; its copied DAG record is included in the delivery. There are no dependency-module repairs.

The new node is therefore listed by its copied DAG record;
the item copy adds `def-coef-simplicial-groupoid` to `stmt_deps` and changes no
other item statement field.  Both modules compile cleanly with `scompile.py`.

## Second reading by Q44

Independent maintainer second reading of immutable delivery
`8fb4d55db90f65bbaf67b50ab8421dba0723f158`; the reviewer did not write the delivery.
The following supersedes the delivered placeholder. The review approved the mathematics
and supplied the complete documentation, citation and proof-import repairs below.

## Material read and statement comparison

Read `packet.md`, the full `check-brief2.md`, the stage-2 standing brief and delivery-errors
H, snapshot AGENTS/stage-2 rules, all four snapshot node records, both delivered modules,
and the delivered report. The two prerequisite records agree with the read-only Q44
clone. The item differs from that clone only in `lean` and the added statement dependency
`def-coef-simplicial-groupoid`; the mathematical statement and proof have not changed.
No released repair note for this item was found.

The item introduces the following objects and clauses; each has the required Lean meaning:

1. An arbitrary small space: `(X : SSet.{u}) (hX : SSet.KanComplex X)`.
   The Kan condition is the representation convention explicitly specified in
   `def-coef-complete-algebroid`, not an added mathematical assumption. The universe
   `u` is arbitrary, not fixed to zero or identified with a coefficient universe.
2. A small simplicial groupoid: `∃ G : SimplicialGroupoid.{u}`. The structure's
   `carrier : SCat.{u}` uses the recorded `EnrichedCat` construction, not a private
   category definition. Its object type is in `Type u`, and every mapping set is
   in `SSet.{u}`. Objects are constant across simplicial degrees.
3. Strict inverses in every degree: `inv x y` is an actual simplicial map
   `hom carrier x y ⟶ hom carrier y x`. `left_inv` says that first f and then
   its inverse is the identity at x; `right_inv` says the reverse composite is
   the identity at y. Both quantify over every n and every n-simplex. The helpers
   evaluate the existing enriched composition and the degeneracy of the identity
   vertex. Enriched unit compatibility identifies this with the degreewise identity.
   Naturality of `inv` gives compatibility with every simplicial operator. The
   category axioms plus these two equations imply involutivity and reversal of
   composition, so no additional inverse axiom is missing.
4. Fibrancy: `G.IsFibrant` unfolds to `IsLocallyKan G.carrier`, namely Kan fillers
   in each `hom G.carrier x y`. It does not mean only that the nerve is Kan.
5. The coherent nerve and equivalence: `nerveFunctor.obj G.carrier` is the recorded
   Mathlib `SimplicialNerve` of `underlying G.carrier`. The existential e has exactly
   source N_hc(G) and target X. `Enhanced.IsWeakHomotopyEquivalence e` requires
   bijections on realization path components and all positive based homotopy groups.
   Strict degree-zero inverses make pi_0(G) a groupoid; the recorded locally Kan
   groupoid clause makes N_hc(G) Kan. Thus this is an equivalence of spaces, rather
   than a weaker assertion about arbitrary nonfibrant simplicial sets. An equivalence
   between Kan complexes has an actual simplicial representative in this direction:
   all simplicial sets are Kan--Quillen cofibrant. No canonical map or functorial
   choice was requested, so an existential comparison map is appropriate here.

Read the source and docstrings of `CoherentNerveInfrastructure.lean` (SCat, hom,
underlying, IsLocallyKan, nerveFunctor), `CoherentNerveComparison.lean` (including
`CoherentNerveComparisonStatement.groupoid_nerve_kan` and
`CategoryTheory.coherent_nerve_comparison`), and `EnhancedDiagramsCones.lean`
(`IsWeakHomotopyEquivalence`, space conventions). Read the relevant universe,
object-diagram, IsComplete and completeCategory interfaces in `CompleteAlgebroid.lean`.
The latter supplies conventions; no monoidal coefficient object, presentability,
UnitSection or extra coefficient hypothesis leaks into this theorem.

## Sources and proof plan

The primary item source was read online:
[Gepner--Haugseng, Remark 4.2.5](https://arxiv.org/html/1312.3178).
It specifies constant objects, strict simplicial groupoids and Kan mapping-space
fibrancy, and asserts the required model for every space. Its nearby Corollary 4.2.8
and the proof of 4.2.9 use exactly this conclusion.
Also inspected [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Proposition 1.2.5.1 (printed p.35) and Theorem 2.2.5.1 (printed p.89), and
[Kerodon 3.3.6](https://kerodon.net/tag/00ZA).
These support the groupoid/Kan criterion, coherent-nerve Quillen comparison and
finite-product-preserving Ex-infinity replacement.

Read the exact additional proof interfaces in the Q44 clone:
`CofibrantSimplicialInversion.Statement.total_inversion_nerve` and
`cofibrant_simplicial_inversion`, `SSet.ex_infinity_finite_products`, and the
coherent derived-adjunction interface of `ModelInfinityDerivedAdjunction.lean`.
The proof's six steps are valid applications: rigidification of the initial
cofibration gives cofibrant A; total inversion applies to its identity cofibration;
finite-product and terminal comparisons transport composition, identities and both
inverse equations; the Ex unit is local weak equivalence and fixes objects, hence
DK; derived nerve comparison identifies the locally Kan G without requiring R(G)=G;
small colimits, finite words, quotients and countable Ex iteration retain smallness.
The repaired docstring records all six steps, the dependency identifiers, and the
representative for the inverse equivalence. The proof itself remains only `sorry`.

## Searches, records and edge cases

Independently searched Mathlib, WeilConjectures and the Q44 side CategoryTheory
modules for `simplicial.?groupoid`, `groupoid.?model`, degreewise inverse language,
and the proposed declaration names. Read Mathlib `SimplicialNerve.lean:193` and its
TODO list: it defines the coherent nerve, not this presentation theorem. Read
`SimplicialGroupoidLocalization.lean:72`: despite its name it concerns localization
of a simplicial shape into a Kan complex, not strict enriched groupoids. The
existing degree-category construction is reused conceptually; the new helpers merely
evaluate enriched operations, and do not define a second enrichment or nerve.
The delivery records LeanSearch, LeanFinder/Loogle and grep searches. The joint
Loogle query was unsuccessful, but LeanFinder and LeanSearch provide independent
search coverage. No existing exact definition or theorem was found.

The new node has the required definition kind, split status, chapter/unit, ancestor
route, created metadata, empty proof/proof_deps, null mathlib_match, searches,
none audits, lean record and citation by the item. Every named declaration in its
record is in its module. There are no dependency modules or dependency repairs.
Both lean.statement fields agree exactly with the signatures using the delivery
tool's documented whitespace normalization; no binder or conclusion token differs.
The new structure's signature ends before `where`, as required by that extractor.

Checked the empty space using the empty object type (all mapping requirements
vacuous), a point, arbitrary discrete and disconnected spaces, empty mapping sets,
degree zero and all higher degrees, and arbitrary u. There is no basepoint,
connectedness, inhabitation, truncation, field, finiteness or characteristic assumption.
No pro-etale site or substitute is involved. No source-based statement correction
was needed, so a statement_change and citer audit are not required. The two consumers
`lem-coef-operad-groupoid-operator-map` and `lem-coef-many-object-operad-accessibility`
retain exactly the strict-inverse and model-existence interfaces they use.

## Findings and complete fixes

- **H1/H11:** the delivered `## Second reading by Q44` was a placeholder saying no
  reading occurred. Replaced that section with this independent, concrete reading
  while retaining the real Worker report and New nodes sections.
- **H8:** the theorem docstring compressed the proof and omitted several node steps
  and their dependencies. Replaced it with the six-step plan above. Added a
  source/blueprint docstring to the coercion instance.
- **Stage 2 section 3(7), H9 import convention:** the stated inversion, Ex-infinity
  and derived-adjunction proof modules were absent from the item's imports.
  Added their ordinary, non-public imports. Statement dependencies and the
  enhanced-diagram convention remain available through public imports.
- **H12 source citation:** the new node's URL `dwyer-kan-1.pdf` opens *Simplicial
  localizations of categories*, not *Homotopy theory and simplicial groupoids*;
  its numbered 2.5 and 3.3 are not the claimed theorems. Replaced the new node's
  source with the directly checked Gepner--Haugseng Remark 4.2.5 and aligned the
  definition-module docstrings. The old PDF remains a legitimate source for the
  inherited proof step citing DK I section 9; that item field was not changed.

`fixes/` contains exactly four complete replacements accepted by the stage-2
`--apply-fixes` layout: the two delivered modules at their `lean/Sheaf/...` paths,
`def-coef-simplicial-groupoid.json`, and
`lem-coef-simplicial-groupoid-models.report.md`. No Lean signature, mathematical
node statement, hypothesis, conclusion or dependency predicate was changed.
No hollow data or proof inside a new definition, no axiom, no local theorem proof
beyond the one `sorry`, no private substitute and no unbound variable was found.
Lines are at most 100 characters and namespaces have no Sheaf prefix.

## Compiler evidence and review boundaries

The worker report recorded clean per-file compilation but gave no transcript.
Independently reproduced it for both immutable modules with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q44 lem-coef-simplicial-groupoid-models snapshot/lean/Sheaf/CategoryTheory/SimplicialGroupoid.lean snapshot/lean/Sheaf/CategoryTheory/SimplicialGroupoidModels.lean
```

Exit 0; no errors or warnings. The wrapper compiled the private overlay,
preliminary sibling, both sandbox files and both library-path checks individually;
the final library-path checks took 1.5 s and 1.9 s.
Repeated for the two complete fixed modules under `fixes/lean/Sheaf/CategoryTheory/`:
exit 0, no errors or warnings; final library-path checks 1.6 s and 1.9 s.
Each invocation retained the wrapper's 60-second per-file limit.
The installed scompile.py identifies itself as the 2026-10-17 server-overlay wrapper
and uses private `.lbuild` overlays with wire confirmation; unlike the older brief,
it is now server-only. I used that prescribed wrapper, with no direct SSH command
or alternate compiler. No global build, live Lean write, direct repository mutation,
claim, merge or delivery/preflight operation was run. Only review.md and fixes were
written. The immutable snapshot and branch head were not changed.
