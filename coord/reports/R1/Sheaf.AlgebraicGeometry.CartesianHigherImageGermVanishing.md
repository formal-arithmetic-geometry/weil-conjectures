## What changed

Proved `exists_cartesianHigherImage_germ_eq_zero` by representing a stalk element on an etale neighbourhood, refining the zero equality to an affine etale neighbourhood, applying the new affine-section vanishing statement, and transporting the result by stalk naturality. Added the proof-only import of `Mathlib.AlgebraicGeometry.Sites.AffineEtale` and the new statement module `CartesianHigherImageAffineSectionVanishing`.

## Proved and sorry left

The target theorem `exists_cartesianHigherImage_germ_eq_zero` is proved. The new theorem `exists_cartesianHigherImage_affine_section_eq_zero` remains `sorry` as the geometric continuity substep; its DAG node is `lem-sc-cartesian-higher-image-affine-section-vanishing`.

## No longer needed

Change record: `coord/changes/cartesianHigherImage_stalk_colimit.md`. The original stalk-colimit and filtered-colimit-map-zero proof dependencies are no longer needed. The temporary derived-class, raw-local-zero, and derived-stage modules explored during the proof were removed because the final proof uses only the affine-section reduction.

## Where the brief, the DAG or earlier work was wrong

The original DAG route assumed a ready stalkwise filtered-colimit theorem for the varying-base cartesian higher image. The available continuity results do not state that theorem directly. The delivered route isolates the genuinely geometric affine-section continuity statement instead.

## New nodes

`lem-sc-cartesian-higher-image-affine-section-vanishing` records the strict affine-section subproblem and its source-based proof plan.

## Earlier second reading (a previous round; superseded)

1. **Signatures and definitions.** Compared the delivered germ module with the repository
version byte-for-byte. The target theorem signature is unchanged. The only existing public
declaration removed is `cartesianHigherImage_stalk_colimit`, covered by
`coord/changes/cartesianHigherImage_stalk_colimit.md`; no definition or target statement was
changed. The added affine-section theorem has the stated affine-object hypothesis and its
signature agrees with its new DAG node.

2. **Proof status.** Compiled both delivered modules with `lcompile.py --all`. There are no
forbidden `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions. The target germ theorem
is proved; the sole remaining `sorry` is the named affine-section continuity theorem recorded
in its node and report (so only the permitted transitive `sorryAx` remains in the target).

3. **New statement.** Checked the affine-section split against the target's local reduction:
it is a strict local subproblem (an affine etale object and a section), with exactly the
hypotheses needed by the target proof. It is not duplicated elsewhere in `lean/Sheaf` or
Mathlib. Its docstring gives the source and the complete geometric proof plan.

4. **Route and pruning.** The target proof represents a stalk element, refines to an affine
etale neighbourhood, invokes the affine-section theorem, and transports the zero equality by
stalk naturality. This preserves the unit route while eliminating the unused stalk-colimit and
filtered-colimit route. The corresponding old node and import are listed as no longer needed;
the new affine node is the only proof dependency.

5. **DAG agreement.** Checked the target and affine node statements, `proof`, `proof_deps`,
`proof_origin`, module paths, and declarations against the Lean files. The target node now
depends on the affine-section node, and the new node records its source, split status, and
proof plan.

Changed the target proof to use the affine-section reduction, added
`CartesianHigherImageAffineSectionVanishing.lean`, removed the unused stalk-colimit theorem
and its filtered-colimit import, added the corresponding change record and node, and retained
the one unresolved affine continuity theorem as a named split-off statement.

## Second reading by R1

1. **Signatures and definitions.** Compared the delivered germ module with the repository
version. The signature of `exists_cartesianHigherImage_germ_eq_zero` is byte-for-byte
unchanged. The removed `cartesianHigherImage_stalk_colimit` declaration is covered by the
change record, and no definition or target statement was altered. The affine-section module
introduces exactly the declaration recorded by its new node.

2. **Proof status.** Compiled both sandbox modules with `lcompile.py --all`; both compile
without errors or warnings. The only remaining `sorry` is
`exists_cartesianHigherImage_affine_section_eq_zero`, and it is a named public theorem with
a source, a complete proof plan in its docstring, and a matching split node. No forbidden
axiom, unsafe, opaque, extern, implemented-by, or hollow definition occurs.

3. **New statement.** Read the affine-section theorem against the target reduction and the
source plan. It is a strict affine-local continuity subproblem: it fixes an affine etale
object and one section, while the target theorem handles the stalk representation and
transport. Its hypotheses and conclusion are exactly those used by the target proof. Search
of the project and Mathlib found no duplicate declaration.

4. **Route and pruning.** The proof represents the stalk element, refines equality with zero,
refines to an affine etale neighbourhood, applies the affine-section theorem, and transports
the resulting zero through stalk naturality. This retains the unit's affine-local route. The
stalk-colimit and filtered-colimit dependencies are unused by the delivered proof and are
listed as no longer needed; the proof-only affine-etale import is private to the new module.

5. **DAG agreement.** Checked the target and affine-section node statements, Lean records,
proof steps, proof dependencies, source origins, chapter, and unit against the delivered
files. The target node depends on the affine-section node, and the new node records the
remaining split theorem and its source-based proof plan.

The second reading found no further changes necessary.
