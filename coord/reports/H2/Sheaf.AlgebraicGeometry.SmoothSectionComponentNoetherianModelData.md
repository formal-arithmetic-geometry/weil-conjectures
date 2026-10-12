## What changed

Replaced the hole in `Smooth.exists_section_component_noetherian_model_data` with a
complete Lean reduction. Added the proof-only import
`Sheaf.AlgebraicGeometry.NoetherianApproximationSmoothStage` and a proved private helper
`exists_smooth_noetherian_model_with_section`. Existing signatures and visibility are unchanged.

The argument constructs the affine restriction and its section by pullback lifts, descends
the finitely presented morphism through the existing proved AffineTransitionLimit API,
uses eventual smoothness, and then descends the section as a morphism. Its section identity
is proved by the second projection; comparison compatibility is proved with pullback.hom_ext.
Both cartesian model squares are proved with IsPullback.of_right. This section construction
adapts the already proved `exists_noetherian_model_with_section`, without importing or
restating its public theorem.

## Proved and sorry left

Closed: `AlgebraicGeometry.Smooth.exists_section_component_noetherian_model_data`
(node `lem-sbc-smooth-section-component-noetherian-model-data`), 1 of 1 original holes.
The private helper is fully proved.

Added: `AlgebraicGeometry.Scheme.NoetherianApproximation.exists_smooth_stage`
(node `lem-sbc-noetherian-approximation-smooth-stage`), the only remaining sorry in the
delivery. This is a decomposition: one original hole closed, one strictly smaller hole
added, net zero. The new statement asserts only eventual smoothness of the second
projection of an already supplied model; it asserts no section, section identity,
section compatibility, neighbourhood, new model existence or noetherianity conclusion.
All those parts are proved in the item's module.

Both modules compile cleanly with lcompile.py --all. The statement was checked against
Stacks Tags 0C0C and 081D. Stage schemes are qcqs by noetherianity; the source is qcqs
because p is finitely presented over a noetherian scheme. Cofiltered tails preserve
the limit. Tests in words include an identity morphism (every stage works), an already
smooth model (base-change stability), an empty source (eventual smoothness still applies),
and an empty limit base (the finite-presentation descent result still includes this case).
No injectivity or surjectivity of the limit projections is assumed.

## No longer needed

None. The original module had only its required public Mathlib Smooth import and no
proof dependencies. The proof still uses the source's noetherian approximation,
finite-presentation descent and morphism-descent declarations. No blueprint unit statement
or realized proof step is bypassed; the unit's realized arrays are empty.
The section identity is constructed by a pullback lift, so a separate application of
01ZM(3) to the section identity is unnecessary, but no module or node representing
that application was imported in the original file.

## Where the brief, the DAG or earlier work was wrong

The original node packaged all descent steps in one non-elementary step with no dependencies.
Its revised proof lists the actual noetherian approximation, finite-presentation descent,
morphism descent and eventual-smoothness dependencies. The source statement is unchanged.
Tag 055Q descends flatness; the smooth version uses the separately cited Tag 0C0C.

The existing blueprint ancestry script reports None for this item because its creation
chain contains module names. The new node records the actual slicing ancestor
`sbc-lem-slicing`, matching the existing section-descent node's ancestor. Blueprint
searches for 0C0C, smooth descent and smooth limits found no matching blueprint statement.

The new node uses the existing smooth-algebra filtered-colimit descent and spreading-out
nodes as tools to expand the affine-local argument of 0C0C. They are proper subarguments,
not alternate routes around the slicing unit. No tool_uses maintainer field was edited.

## New nodes

`lem-sbc-noetherian-approximation-smooth-stage`, in
`lean/Sheaf/AlgebraicGeometry/NoetherianApproximationSmoothStage.lean`, records exactly
Stacks 0C0C specialized to a supplied noetherian approximation and cartesian model.
Its docstring and node explain the finite affine chart reduction, smooth algebra descent,
eventual comparison isomorphisms, and locality. Its Mathlib searches are copied from
the searches actually run (LeanSearch unavailable; Loogle, LeanFinder and grep found no
exact scheme-level theorem). No change record is needed: no existing interface changed.

## Second reading by H2

1. **Visible declarations: pass.** Diffed the target module against the repository
version and independently compared the theorem signature byte for byte. The existing
signature and visibility are unchanged. There are no definition changes, forced
adaptations or change records. The additions are a proved private helper, a plain
proof-only import, and the new split theorem in its own module.

2. **Proof and axioms: pass.** Both delivered modules compile cleanly with
`lcompile.py --all`. A scratch copy with `#print axioms` for the target, private helper,
and split theorem compiled and showed only `propext`, `Classical.choice`, `Quot.sound`
and `sorryAx`. The one remaining sorry is exactly the report's named split theorem.
There is no hollow definition, arbitrary data construction from an unproved existence
statement, forbidden axiom, unsafe declaration, opaque declaration or external implementation.
The approximation is a genuine construction, and the restricted and descended sections
are explicit pullback lifts.

3. **Split statement: pass.** Read Stacks Tag 0C0C and Situation 081D online
(https://stacks.math.columbia.edu/tag/0C0C and
https://stacks.math.columbia.edu/tag/081D). Noetherianity supplies qcqs of each stage;
finite presentation of p over that stage supplies qcqs of its source. The cartesian
square identifies f with the limit base change. Restricting the cofiltered system to
Over i preserves its limit, so the conclusion is precisely eventual smoothness.
The docstring supplies the finite chart argument and comparison descent. Identity
morphisms and already smooth models work at the current stage by base-change stability.
Empty sources and empty limit bases need no surjectivity assumption; the same descent
argument includes them. This statement is strictly a part of the target argument and
contains no section or model-data existence conclusion.

Repeated searches with different wording: LeanFinder for "A finitely presented morphism
in a cofiltered inverse system of schemes is smooth at some finite stage if its limit
base change is smooth" found smoothness definitions and local finite presentation,
not the scheme-level descent theorem; Loogle for `"Smooth", "IsLimit"` returned no hits;
grep for `smooth.*stage|smooth.*inverse|smooth.*cofiltered` returned unrelated manifold
results. Also searched lean/Sheaf and lean/WeilConjectures for descent, limit and eventual
smoothness and read the existing SectionNoetherianDescent proof and Mathlib smooth
noetherian descent API. No existing theorem closes this split in a few minutes.

4. **Route and pruning: pass.** Read the proof from its target downward and checked
its affine restriction, finite-presentation descent, smooth stage, section descent,
and pullback identities. The imports are needed: Smooth by the statements and
AffineTransitionLimit by the approximation in the new theorem's signature. The target's
new stage import is correctly plain `import`. The original node had no proof dependencies,
so `## No longer needed` is complete. The unit sk-prop-normal-form's realized statement
and step arrays are empty; the slicing unit's route is preserved. This is a decomposition
(one hole closed, one added), not a completed proof with the permitted axiom set.

5. **Nodes: pass.** Compared the old node with the repository version; only proof,
proof_deps and proof_origin changed. Its mathematical statement and stmt_deps are
unchanged. Both Lean statements match their node records verbatim, and both proof_deps
lists equal the union of the steps' uses. Checked the existing descent declarations
against their nodes. The new node has source, complete proof steps, searches, ancestry,
creation metadata and its Lean record.

Second reading changed only this report, adding the independent checks and verdicts;
no Lean proof, statement, definition, import or node required repair.
