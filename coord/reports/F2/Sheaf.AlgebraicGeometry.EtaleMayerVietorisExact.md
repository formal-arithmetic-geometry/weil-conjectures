## What changed

Replaced the only `sorry` in `AlgebraicGeometry.Etale.etale_mayerVietoris_exact` by a
compiling reduction. Its complete signature is unchanged. Four new proof-only imports
supply three proved helpers and one remaining general homological-algebra statement:

- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisSections` proves the section injection and
  kernel/image statement for **every** abelian étale sheaf, using the cover and gluing.
- `Sheaf.CategoryTheory.InjectiveSheafMonoRestriction` proves restriction surjectivity
  for an injective abelian sheaf along **any** site monomorphism, using already-proved
  free Yoneda helpers from `WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion`.
- `Sheaf.CategoryTheory.RightDerivedZeroTransformation` proves the augmentation equation
  for the zeroth right derived map of a natural transformation of additive functors.
- `Sheaf.CategoryTheory.RightDerivedPairSequence` states the remaining passage from a
  pair/difference sequence exact on injectives to the natural derived long exact sequence.

The main proof constructs all four evaluation functors and their four restriction maps,
reflects the intersection inclusion's monomorphism from schemes, proves surjectivity of
its difference map by the pair `(liftedSection, 0)`, and discharges the general theorem's
hypotheses. It proves the initial derived injection separately by transporting the
proved section injection through the degree-zero augmentation isomorphisms and their
transformation equation. The remaining theorem does **not** assert this initial injection,
does not mention schemes, opens, a covering, or a sheaf, and assumes only the termwise
exactness needed for the homological part of the argument. This is a reduction of the
geometric theorem, not a renamed copy of it.

Updated the item's DAG proof, proof dependencies, and proof origin to this route.
Added the four helpers' nodes, signatures, sources, and complete proof plans.
There are no changes to existing statements, definitions, public imports, target
signatures, or unit records. A change record documents the preflight parser issue
described below; it records no mathematical interface change.

## Proved and sorry left

The item's only original `sorry` is replaced by a complete Lean proof from the remaining
named intermediate theorem:
`AlgebraicGeometry.Etale.etale_mayerVietoris_exact`
(node `lem-weil-pbc-etale-mayer-vietoris-exact`). It still transitively depends on the
one pending theorem listed below; this is not a claim of axiom-free target completion.

The delivery also proves, with no `sorry` in their proofs:

- `AlgebraicGeometry.Etale.etale_mayerVietoris_sections`
  (`lem-weil-pbc-etale-mayer-vietoris-sections`).
- `CategoryTheory.injective_sheaf_mono_restriction`
  (`lem-weil-pbc-injective-sheaf-mono-restriction`).
- `CategoryTheory.rightDerived_zero_transformation`
  (`lem-weil-pbc-right-derived-zero-transformation`).

The **only** `sorry` left anywhere in the delivery is:
`CategoryTheory.rightDerived_pair_sequence`
(`lem-weil-pbc-right-derived-pair-sequence`), in
`lean/Sheaf/CategoryTheory/RightDerivedPairSequence.lean`.
Its proof is exactly `:= by sorry`. Its docstring and node specify the degreewise
short exact evaluated resolution sequence, product-homology identification, transport
through `isoRightDerivedObj`/`rightDerived_app_eq`, and connecting-map naturality through
resolution lifts. Those are the remaining parts of original steps 4–6, without the
geometric section input or the independently proved initial injection.

All five modules compile together in import order through the prescribed `lcompile.py`,
with no warnings. The first delivery dry run passed local and server compilation and the axiom probe,
but preflight required a record for its parser false positive. The record documents
the issue; the final dry run checks the repaired delivery.

## No longer needed

No import from the original item's file was removed: its public imports support the
unchanged signature and the abelian/enough-injectives instances. The original file had
none of its planned `Sheaf` proof dependencies imported; the delivery adds only the four
proof imports actually used. There is no claim that any module is unreachable from
**other** project targets: the following are removed from this proof branch.

The Čech route is eliminated completely:

- `def-weil-pbc-cech-complex` and its planned import
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`.
- `lem-weil-pbc-injective-sheaf-cech-acyclic` and its planned import
  `Sheaf.CategoryTheory.InjectiveSheafCechAcyclic`, including its free Čech resolution,
  cocycle computation, and Čech comparison dependencies on this branch.

`lem-weil-pbc-module-sheaves-enough-injectives` and its planned import
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives` are also unnecessary here: the
existing Grothendieck abelian sheaf and enough-injectives instances already supply the
resolution infrastructure used by the unchanged statement and by the proof.
The module-valued assertion of that lemma is not used for abelian evaluation.

Retained indirectly, rather than pruned: the open-fibre-product fact and étale open
immersion instances are used by the proved sections helper; injective resolutions,
complex long exactness, and its naturality are used by the remaining general helper;
the degree-zero comparison is used by the main injection proof. The node routes record
these dependencies instead of re-adding unused Čech imports.

The second reading checked the complete old dependency list. The following old direct
edges now occur through the new helpers rather than directly from the item:
`lem-weil-pbc-etale-composition-cancellation`, `lem-weil-pbc-open-fibre-product`,
`def-sp-injective-resolutions`, `lem-weil-pbc-complex-ses-homology-long-exact`, and
`lem-weil-pbc-complex-ses-long-exact-naturality`. The definitions
`def-weil-pbc-etale-site` and `def-weil-pbc-abelian-etale-sheaves` remain statement
prerequisites and prerequisites of the sections helper. The only old direct edge
retained directly is `lem-weil-pbc-left-exact-injective-resolution-degree-zero`.
Together with the three pruned nodes listed above, this accounts for all eleven
old proof dependencies; none of the transferred dependencies is claimed pruned.

The second reading removed `Mathlib.Algebra.Category.Grp.AB` from the two new geometric
helpers and exposed only `Mathlib.Algebra.Category.Grp.Basic` for their group types.
In the injective restriction helper, `Mathlib.CategoryTheory.Sites.Sheafification`
supplies the public sheafification hypothesis, while abelianness is supplied by the existing proof-only upstream
import (which already imports `Sites.Abelian` and `Grp.Abelian`). The oversized public AB imports were unnecessary. The existing
item's public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The mathematics of the statement is unchanged and is not disputed.

The first preflight run falsely classified the changed proof as a public-command
change: `tools/leanindex.py` treats the input file's unindented `∃ δ : ...`
continuation as an `other` command and includes its entire proof body in the command
interface. The dedicated declaration parser finds no signature changes. No tool was
edited or bypassed. The requested record
`coord/changes/etale-mayer-vietoris-exact-proof-parser.md` documents the unchanged
old/new signature and the two users reported by `tools/downstream.py --uses`; neither
needs adaptation. This reports the process failure for the maintainer to repair. The DAG's Čech
surjectivity route was longer than necessary: Stacks Tag 0A50 explicitly gives the
alternative via restriction along the monomorphism `U ∩ V → U`, citing Tag 093X. This
alternative is now fully proved, so Čech acyclicity is not deferred elsewhere.

Mathlib's Mayer–Vietoris sequence is for its Ext-based sheaf cohomology, not the displayed
right derived evaluation functors. Its signatures and the upstream right derived
long-exact-sequence module were checked: the latter derives one fixed functor on a
short exact sequence of coefficient objects, whereas this argument needs a sequence
of evaluation functors exact on injective objects. Neither directly proves this item.
The general missing helper is therefore the homological part of the source proof.

Edge cases were checked in the construction: no assumption excludes empty opens, the
empty scheme, `U = V = X`, zero coefficient sheaves, or degree zero. Covering is checked
by the union-of-ranges criterion; mixed gluing relations lift through the actual
scheme pullback; same-index relations cancel the monomorphic open immersion. The
injective restriction proof uses only a monomorphism and available sheafification,
not a cover or a subcanonical topology. The derived helper assumes only additive
functors and injective resolutions; termwise exactness forces its zero-composite
relation on every evaluated resolution term. In a split or zero sequence its
construction gives the usual zero boundaries.

The literature `.tex` files named in the existing node are absent in this clone.
The source proofs were read directly from the official Stacks pages:
https://stacks.math.columbia.edu/tag/0A50,
https://stacks.math.columbia.edu/tag/093X, and
https://stacks.math.columbia.edu/tag/0156.
No unit statement or realized unit step is bypassed: this remains the Mayer–Vietoris
step of the strictly henselian comparison route in `sk-thm-p1`.

## New nodes

`lem-weil-pbc-etale-mayer-vietoris-sections` records the fully proved raw section
injection and exactness theorem, with the explicit covering, intersection pullback,
amalgamation, uniqueness, and conversion to function exactness. Its module is
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisSections`.

`lem-weil-pbc-injective-sheaf-mono-restriction` records the fully proved Tag 093X
abelian-sheaf specialization for arbitrary sites and monomorphisms, including universe
lifting of representables and extension through the sheafified free mono. Its module
is `Sheaf.CategoryTheory.InjectiveSheafMonoRestriction`.

`lem-weil-pbc-right-derived-zero-transformation` records the fully proved compatibility
of `toRightDerivedZero` with `NatTrans.rightDerived 0`; it assumes additive functors,
not left exactness. Its module is `Sheaf.CategoryTheory.RightDerivedZeroTransformation`.

`lem-weil-pbc-right-derived-pair-sequence` records the single pending abstract theorem
for four additive functors and a section sequence exact on injectives. It isolates
original steps 4–6 and explicitly omits the initial injection, which the main proof
proves. Its module is `Sheaf.CategoryTheory.RightDerivedPairSequence`.

All four nodes have the three prescribed search kinds, recorded by `msearch.py` in
`searches.jsonl`. LeanSearch returned Internal Server Error; that is recorded as an
unavailable service, not as evidence of absence. LeanFinder and source grep were read;
they found relevant APIs but no direct match for these exact helper signatures.
The blueprint and existing DAG were searched for duplicate statements before creation.
The sole change record is
`coord/changes/etale-mayer-vietoris-exact-proof-parser.md`, documenting the parser issue
without any statement or definition change.


## Second reading by F2

1. **Unchanged interfaces: pass.** Read the whole diff of the existing module against
   the read-only repository. Its theorem signature is byte-identical (also checked by
   substring comparison), and its public imports are unchanged. There are no existing
   definition changes. The only existing node changes are `proof`, `proof_deps`, and
   `proof_origin`. The four other Lean modules and four other nodes are new. The parser
   change record accurately describes identical old/new mathematical interfaces.
2. **Proof and trust checks: pass with one declared open theorem.** Compiled all five
   modules in import order using only `lcompile.py`, with no warnings or errors.
   Read every proof, including the private cover and pullback helpers. Searched for
   forbidden declarations and all `sorry` occurrences: exactly the public named
   `rightDerived_pair_sequence` has a whole-proof `sorry`; no hollow definition or
   forbidden axiom mechanism occurs. A scratch axiom probe reports only `propext`,
   `Classical.choice`, and `Quot.sound` for all three proved public helpers. The main
   theorem and pending helper additionally report `sorryAx`, as the report declares.
3. **Split statements: pass.** The sole pending helper is a genuine homological
   reduction: it takes four arbitrary additive functors and exactness on injectives,
   omits all geometry and the initial injection, and is used only after the main proof
   establishes its geometric hypotheses. Checked the zero-functor, split-sequence,
   injective coefficient and degree-zero cases. Exactness on injectives suffices,
   since all resolution terms are injective; natural transformations commute with
   the differentials, and homology of a finite product is its product homology.
   The stated docstring gives the full resolution, homology, comparison and naturality
   argument. Independently read Stacks [0A50](https://stacks.math.columbia.edu/tag/0A50),
   [093X](https://stacks.math.columbia.edu/tag/093X), and
   [0117](https://stacks.math.columbia.edu/tag/0117).
   Repeated searches using different queries with LeanFinder, Loogle and source grep,
   and read the upstream long-exact-sequence and Mathlib augmentation APIs. No direct
   theorem closing this functor-sequence helper was found; the upstream theorem varies
   the coefficient object in one fixed functor. Closing the remaining helper requires
   substantial complex and comparison construction, beyond a few-minute repair.
   Empty opens, the empty scheme, equal opens and zero sheaves do not invalidate the
   proved geometric helpers: the proof uses only actual covers and monomorphisms.
4. **Route and pruning: pass after import cleanup.** The geometric proof follows the
   first Stacks route, with the section sequence and mono restriction fully proved.
   The degree-zero injection is proved independently, rather than deferred in the
   general helper. All four new proof imports are used. Checked `sk-thm-p1.json`'s
   `realized` statement and steps; this remains the same Mayer–Vietoris input to the
   strictly henselian comparison and bypasses no realized unit step. Expanded the
   pruning account above to cover every old direct proof dependency explicitly.
5. **DAG agreement: pass.** Read all five node records alongside their modules. Every
   recorded Lean statement occurs verbatim in its file, every `proof_deps` is precisely
   the union of the proof steps' `uses`, and the new nodes carry source, provenance,
   searches, creation, chapter, unit, blueprint and Lean fields. The existing node's
   proof now describes the implemented argument. The pending node accurately identifies
   the remaining homological construction and its dependencies.

**Changes made by this second reader:** removed oversized public AB imports from the
new sections and injective-restriction helpers; kept sheaf abelianness supplied through the proof-only upstream import
and exposed only the needed sheafification API; completed the dependency/pruning
account; added this independent review. No theorem statements, definitions, proof
bodies, existing public imports or unit records were changed.
