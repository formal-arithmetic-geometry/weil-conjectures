## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.exists_affine_hypercover_geometry` with its
signature unchanged. The proof follows Stacks Tag 09A1(2): build the finite-basis
hypercover in the qcqs subsite, realize its finite families by affine disjoint unions,
and compare the matching maps through sheaf realization. The finite component
bijections and the component lifting properties come directly from the existing
finite-family geometry and affine weakly-contractible singleton-cover results.

The main module contains fully proved private categorical helpers for independent
object/morphism universes and lifted sheaf Yoneda. They construct the family functor,
prove that realization preserves finite limits, prove that component covers realize
to epimorphisms, and compare the selected proper-face cones with the requested
terminal, binary-product and boundary matching cones. These adapt the existing
realization proofs to the full site's universe sizes; they introduce no public API.
The full-site finite coproduct hypotheses are used in the full sheaf category, while
finite matching limits are constructed first in the qcqs slice. No finite coproduct
property of all sheaves on the qcqs finite precoverage is assumed.

Generalized two unclaimed modules, `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverStep`
and `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence`: use independent category
universes, formal indices in `Type (max u v)`, and omit three unused precoverage axioms.
The induction invariant's content and both existing proofs are retained. This is
necessary because qcqs objects have universe `u+1` and their morphisms universe `u`.
Both changes are documented in:

- `coord/changes/F2-SiteFiniteBasisHypercoverStep-universes-and-precoverage.md`
- `coord/changes/F2-SiteFiniteBasisHypercoverExistence-universes-and-precoverage.md`

The DAG's geometric proof now records the actual route and dependencies; the two
finite-basis nodes record their generalized statements and Lean signatures.
The blueprint unit's statement and steps are preserved. The source was checked at
https://stacks.math.columbia.edu/tag/09A1 and the realization explanations at Tags
0DB1 and 0DB2. No repository or library files outside the sandbox were edited.

Validation: all three files compiled together with `lcompile.py --all`, without
warnings. The second reader's temporary `#print axioms` checks confirmed that the
geometry theorem, the finite-basis existence and extension theorems, and the principal
private realization and matching-comparison helpers use only `propext`,
`Classical.choice` and `Quot.sound`. The geometry theorem's current axiom closure
contains no `sorryAx`: the earlier report of open transitive dependencies is stale.
The temporary checks were removed from the delivery source.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ProEt.exists_affine_hypercover_geometry`
(node `lem-weil-pbc-proetale-affine-acyclic-hypercover-geometry`).
No `sorry` remains in the item. No holes were added and no statement was split off.
The two generalized dependency modules also contain no `sorry`.
This is one proof from existing library declarations, not a decomposition.
The current geometry theorem's transitive axiom check is also free of `sorryAx`.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.SiteHypercoverDisjointUnion` and
removed `lem-weil-pbc-site-hypercover-disjoint-union` from the item's proof dependencies.
Its API requires a small category, ordinary same-universe sheaf Yoneda, and a covering
hypothesis for arbitrary matching cones. The proof instead uses the actual matching
cones returned by finite-basis existence and a local proof with lifted Yoneda.
The small-category realization modules
`Sheaf.CategoryTheory.FormalCoproductSheafRealization` and
`Sheaf.CategoryTheory.FormalCoproductSheafCoverEpi` are likewise not imported by this
route; their mathematical arguments are implemented by fully proved private helpers.
Whether those modules leave the entire targets' closure depends on other parents;
this report only prunes them from this item's realization route.
No other planned finite-basis or qcqs-geometric node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan omitted the singleton basis-cover input needed to apply finite-basis
existence. The existing `ProEtaleQcAffineContractibleCover` theorem supplies it and
is now a direct dependency.

The finite-basis statements unnecessarily identified object and morphism universes
and imposed three precoverage axioms their proofs never use. A finite pretopology
presentation does not itself supply the strong `Precoverage.IsStableUnderBaseChange`
class: its definition quantifies over arbitrary cartesian presieves, including
infinitely many isomorphic repetitions of a finite family. The actual construction
requires only the finite-cover and adjoining-arrow hypotheses, which finite-family
geometry supplies. Generalizing the already complete proofs fixes this interface;
no target hypothesis was added or dropped.

The small-category disjoint-union theorem does not directly fit the pro-etale site's
universes or the chosen-cone interface of the finite-basis theorem. The local lifted
realization and proper-face comparison solve those mismatches without new holes.

The two generalized nodes have statement-change records with all original citers
marked as still holding: the step's citer is finite-basis existence, and existence's
citer is this unchanged geometric hypercover theorem. The change-record schema calls
its attribution `F2 stage 2`; the changes themselves are authorized stage-3 interface
repairs in this delivery. No other-group module required adaptation.

## Second reading by F2

1. **Signatures and visible definitions: pass.** Compared all three delivered modules
   with the repository using `diff` and the declaration scanner. The complete statement
   of `AlgebraicGeometry.Scheme.ProEt.exists_affine_hypercover_geometry` is byte for byte
   unchanged. The only changed existing public interfaces are
   `IsFiniteBasisTruncation`, `exists_finite_basis_truncation_extension`, and
   `exists_site_finite_basis_hypercover`; both change records contain the old and new
   text, the reason, and users. At equal universes the invariant is unchanged, and
   removing unused assumptions strengthens the proved theorems. The remaining changed
   signatures belong to private helpers in these same dependency modules. Searches of
   `lean/Sheaf` confirmed the reported direct callers. No target interface changes.

2. **Proof and trust: pass.** Recompiled all three modules in dependency order with
   `lcompile.py --all` (2.6, 3.8, and 7.9 seconds), without errors or warnings. Read the
   realization equivalence, coproduct comparison, component-cover cancellation, and
   matching-cone conjugation proofs. No delivered source contains `sorry` or a forbidden
   trust escape. Scratch-copy axiom checks of the geometry theorem, both finite-basis
   theorems, the invariant, and the main private comparison helpers show exactly the
   three permitted axioms and no `sorryAx`. All new data definitions are explicit
   constructions or use proved universal properties; choices of geometric witnesses
   remain local to the existential theorem proof.

3. **Split-off statements and edge cases: pass.** There are no new public statements,
   nodes, or split-off holes. Checked the generalized construction at degree zero,
   with empty finite families and empty covering fibres: the terminal singleton and
   empty proper-face diagram give the augmentation; separatedness proves cancellation
   even for an empty covering family. The finite-enlargement induction starts at the
   given cover, including an empty one, and uses only the stated adjoining hypothesis.
   An independent Lean Finder search for formal coproducts of representables preserving
   finite limits returned no applicable replacement; Mathlib and project text searches
   confirmed that the existing realization API uses the incompatible small-category
   universe specialization.

4. **Route, imports, and pruning: pass.** Read Stacks
   [09A1](https://stacks.math.columbia.edu/tag/09A1),
   [0DB1](https://stacks.math.columbia.edu/tag/0DB1), and
   [0DB2](https://stacks.math.columbia.edu/tag/0DB2). The proof retains finite-basis
   hypercover construction and finite disjoint-union realization. It uses full-site
   sheaf coproducts, without assuming them for the qcqs finite precoverage. The public
   imports supply statement vocabulary; added realization imports are proof imports.
   The old proof-dependency set loses exactly
   `lem-weil-pbc-site-hypercover-disjoint-union`, already listed under No longer needed.
   Read `dag/units/sk-thm-properbasechange.json`: its statement and realized steps are
   retained, and no unit-level node is bypassed.

5. **DAG and change records: pass.** Read all three delivered nodes and compared their
   changed fields with the repository. Each `proof_deps` equals the union of its proof
   steps' uses. The geometry node now describes the actual singleton-cover input,
   lifted sheaf realization, and proper-face matching comparison. The dependency nodes'
   Lean statements match the generalized source, with declared statement changes and
   unchanged proof routes. No new node schema or source obligation arises.

Second-reading changes: corrected the stale claim that the geometry theorem still
depends on `sorryAx`, and added this review. No Lean proof or statement needed repair.
