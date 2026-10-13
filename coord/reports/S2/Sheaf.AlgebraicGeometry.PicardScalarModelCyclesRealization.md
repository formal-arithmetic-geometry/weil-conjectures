## What changed

Reduced `AlgebraicGeometry.Scheme.picard_scalar_model_cycles_realization` to two independent
comparison statements, without changing its signature or its existing docstring.

- `PicardScalarDerivedCycles.lean` isolates the scalar-cycle argument for an arbitrary
  derived object `E`. It knows nothing about `f`, `L`, properness, or geometric fibre maps.
- `PicardDirectImageTestSections.lean` identifies derived test sections of a direct image
  with sections of the base-changed invertible module, compatibly with fibre restriction.
  It knows nothing about `K`, its bases, `d`, or annihilating scalars.
- `PicardDerivedModelSections.lean` defines the common interface explicitly: derived Hom
  from the pulled-back degree-zero structure sheaf, restriction by conjugation with the
  canonical derived composition comparison, and the residue point's open immersion lift.
  The residue lift's composite identity is proved with Mathlib's `lift_fac`.

The item's complete Lean proof composes the residue additive equivalences, takes a derived
cycle lift, transports it to a section using `q`, and combines the two restriction equalities.
It does not simply apply a renamed version of its original statement. Neither new theorem
has both the model and direct-image hypotheses of the item.

The new holed modules import the existing declarations named by their proof plans.
The item uses proof-only imports of the two new comparison modules. Its public imports are
unchanged. A scoped heartbeat allowance handles definitional comparison of the chosen derived
pullback functors. No file outside this sandbox was edited by the worker.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.picard_scalar_model_cycles_realization`
(node `lem-sc-picard-scalar-model-cycles-realization`). Its proof is complete relative to the
following two new named holes:

- `AlgebraicGeometry.Scheme.picard_scalar_derived_cycles`
  (`lem-sc-picard-scalar-derived-cycles`).
- `AlgebraicGeometry.Scheme.picard_direct_image_test_sections`
  (`lem-sc-picard-direct-image-test-sections`).

Also proved `AlgebraicGeometry.Scheme.picardResidueLift_comp`; the supporting definitions
contain no holes. This delivery is a decomposition: one hole closed, two holes added, net
minus one. It does not establish a sorry-free proof of the item.

Edge cases checked mathematically: `m = 0` gives all scalars as cycles; the marked point
rules out empty U and V; non-affine V is permitted because a connective complex's total
hypercohomology in degree zero is global sections of its degree-zero kernel. The direct-image
comparison allows empty fibres and uses no hypothesis on a model. Its family `q` is additive,
so no unprovided linear structure on derived Hom is assumed. No arbitrary existence witness
is used to define data: the chosen composition is pinned by the existing canonical counit
formula, and the residue factor is the actual Mathlib open immersion lift.

## No longer needed

Removed from the item's direct imports:
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` and
`Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare`.
Both are retained as proof dependencies of `PicardDirectImageTestSections`; they are relocated,
not globally pruned. The original definition dependencies remain necessary to state the item
and its two parts. No existing node or module is claimed to leave the target closure.

Every former `proof_deps` entry is accounted for:
- `def-pc-base-change`, `def-pc-derived-category`, `def-pc-derived-direct-image`,
  `def-pc-perfect-complex`, `def-sc-invertible-module`, `def-weil-residue-field`, and
  `lem-pc-module-pullback-adjunction` remain signature dependencies and are used in the
  new statements or their proof plans; their modules remain in the import closure.
- `lem-pc-rf-perfect-base-change`, `lem-pc-canonical-degree-zero-mate-square`, and
  `lem-pc-module-pullback-identity-composition` are no longer called directly by the
  item's proof. They are relocated to the direct-image comparison's proof plan.
None is globally pruned. The item's two current `proof_deps` are exactly the two theorems
that its proof calls.

No unit-level route was changed: the unit `sk-prop-av-cube` has no realization attached to
this item, and the scalar-cycle and canonical-base-change steps remain in the new nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original proof plan combines three interfaces that the
existing Lean declarations do not directly supply: sheafification of the scalar bases,
connective derived Hom cycle computation, and the natural identification with geometric
sections. The two new statements expose that missing glue without changing the item.

The local `blueprint_refs.py ancestor` query returned `blueprint.from.node = None` for this
created item; the new records therefore preserve the item's explicitly recorded ancestor
`thm-sc-theorem-of-cube` and prepend the item to its recorded `via` list.

Searches used Lean Finder, Loogle, local rg, and the logged msearch grep. LeanSearch returned
Internal Server Error and is recorded as unavailable. Stacks Tags 0BF2, 0B91 and 08HY were
read from the Stacks website because the local blueprint text is absent on this machine.

## New nodes

`def-sc-picard-derived-model-sections`: real derived Hom and canonical conjugation definitions,
plus the explicit residue factor and its proved composite identity. Module
`Sheaf.AlgebraicGeometry.PicardDerivedModelSections`.

`lem-sc-picard-scalar-derived-cycles`: the model-only half of the argument. Its statement is
independent of any direct image or family of line bundles. Module
`Sheaf.AlgebraicGeometry.PicardScalarDerivedCycles`.

`lem-sc-picard-direct-image-test-sections`: the geometry-only half, for all base changes and
all derived test sections. Its statement is independent of any finite-free model or scalar
cycle. Module `Sheaf.AlgebraicGeometry.PicardDirectImageTestSections`.

Change record: `coord/changes/picard-derived-model-sections.md` (new public interfaces only;
no existing signature, visibility, definition, or public import changed).

Validation: all four modules compiled in dependency order. The first required dry run
reported OK, with only the second reading deferred; a final dry run checks the retained
proof-plan imports as well. No push was performed.

## Second reading by S2

Independent second reader, 2026-10-13. Read all four delivered modules, all four node
records, the change record, the repository original, the unit realization, and the
existing comparison declarations cited in the proof plans.

1. **Unchanged interface — pass.** The diff changes only the original theorem's proof,
   its scoped heartbeat option, and two proof-only imports. Its complete signature is
   byte-for-byte identical to the repository version; its docstring and public imports
   are unchanged. The existing node changes only `proof`, `proof_deps`, `proof_origin`.
   All other declarations in the delivery are new and recorded in the change record.
2. **Proof and data — pass, relative to two named holes.** All four modules compile
   locally in import order (20.5, 5.5, 4.0, 13.6 seconds). An appended scratch probe ran
   `#print axioms` for every delivered declaration. The derived-section abbreviation,
   canonical restriction, residue lift, and residue-lift composite theorem have only
   `propext`, `Classical.choice`, and `Quot.sound`. The two new comparison theorems and
   the original theorem additionally have `sorryAx`. There are exactly two local
   `sorry`s, both reported public named theorems, and no forbidden declarations or
   holes in definitions. The canonical composition comparison is determined by its
   left-derived counit formula, and the open lift is unique over W; no arbitrary
   unproved existence witness defines data. The upper proof composes actual additive
   equivalences and substitutes two independent restriction identities.
3. **Split statements — pass.** The scalar theorem involves an arbitrary E and its
   fixed local model, with no f or L. The geometric theorem involves f and L, with no
   scalar model or differential. Neither restates the item; each is a strictly smaller
   part of its argument. Checked m=0, a=0, U=V, non-affine V, and empty fibres: zero
   negative terms remove boundaries; connective hypercohomology has only the (0,0)
   term in total degree zero even on non-affine V. Empty fibres make both groups in the
   geometric comparison zero and cannot satisfy a rank-one residue-model hypothesis
   in the scalar application. The one residue equivalence is fixed before varying V.
   Read [0BF2](https://stacks.math.columbia.edu/tag/0BF2),
   [0B91](https://stacks.math.columbia.edu/tag/0B91), and
   [08HY](https://stacks.math.columbia.edu/tag/08HY). Properness plus local finite
   presentation gives finite presentation, and invertibility plus flat f gives the
   relative flatness required by 0B91. Derived adjunction and full faithfulness give
   the geometric identification; canonical mates give its restriction law.
   Repeated Lean Finder, Loogle, logged Mathlib grep, and local library searches using
   different terms. Hits include singleFunctor full faithfulness and global-section
   naturality; the library supplies flat-complex pullback, structure-sheaf pullback,
   perfect direct-image base change, and the canonical degree-zero mate square.
   These are ingredients, not either full statement. Neither open comparison can
   be closed by applying one existing lemma in a few minutes.
4. **Route and pruning — pass.** The proof follows the shortest available composition
   of the independent comparisons. All imports needed only by proofs are plain
   imports. The open comparison modules retain their planned proof-dependency imports.
   Every former proof dependency is now accounted for under `## No longer needed`;
   none is claimed globally pruned. The unchanged unit `sk-prop-av-cube` has empty
   realization lists for its statement and step; this auxiliary split changes no
   unit or chapter route and retains the scalar and canonical-base-change arguments.
5. **Nodes — pass after repair.** The original node's two proof steps and dependencies
   match the two applications in Lean. All new statements have source, mathematical
   proof, matching node, chapter/unit, ancestry, created/Lean records and recorded
   searches. Replaced the two normalized theorem signatures with their verbatim
   multiline Lean signatures, and replaced the abbreviated definition record with
   the verbatim multiline abbreviation signature (its derived-Hom type is inferred from
   its actual body). Their mathematical statements are unchanged.

Second-reading changes: corrected the three new node `lean.statement` records and
completed the dependency accounting in the report. No Lean proof, statement, definition,
public import, or unit realization was changed. This remains a decomposition of one
original hole into two independent holes, net minus one; it is not a sorry-free proof.

The first second-reader dry run rejected inclusion of the abbreviation body in its
`lean.statement` field. Corrected that field to the verbatim signature before `:=`;
no Lean source changed.
