## What changed

The signature of
`AlgebraicGeometry.Scheme.GaloisCover.exists_pointed_stage_of_affine_limits`
is unchanged. Its proof now descends an unpointed torsor, lifts the given point into
its pullback over `K`, descends that map over a refinement, and constructs the
point in the base-changed torsor. Pullback cancellation proves the final cartesian
comparison. All of this assembly is explicit Lean.

Three new modules isolate the needed arguments:

- `Sheaf.AlgebraicGeometry.Morphisms.GaloisCoverStageDescent` states only unpointed
  torsor descent. This is the remaining hole and has none of the second system,
  section, or point hypotheses of the original theorem.
- `Sheaf.AlgebraicGeometry.Morphisms.PointedSectionStageDescent` proves fixed-stage
  factorization for a locally finitely presented map. It restricts the diagram to
  `Over i`, preserves the limit by initiality, and applies Mathlib's
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange` proves base change of a
  finite Galois torsor. Its total space is the actual fibre product. The action is
  constructed by pullback lifts. Universality of finite coproducts and pullback
  cancellation prove that the new torsor comparison is invertible. The finite
  coproduct argument follows the existing proof pattern in
  `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreTorsorIdentity`, without importing
  that module or its generic-fibre extension dependencies.

All four modules compile together through `lcompile.py --all`, without warnings.
No existing declaration signature, visibility, definition, or public import changed.
No forced adaptations were needed. The blueprint unit's limit-reduction route remains.
The referenced Stacks statements 0BTV, 01ZM, and 0EZJ were read from their official pages;
the repository's local literature mirror is absent on this machine.

The second reading restored the remaining unpointed-descent module's proof-plan
imports: `Mathlib.CategoryTheory.Presentable.Directed`,
`Sheaf.AlgebraicGeometry.DescendFinite`, `Sheaf.AlgebraicGeometry.DescendSurjective`,
`Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`. They are plain
imports because only the postponed proof needs them. This keeps the remaining
hole's dependencies in the import closure, as required by the stage-3 contract.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_pointed_stage_of_affine_limits`
(node `lem-sbc-pointed-galois-cover-limit-descent`).

Also fully proved:

- `AlgebraicGeometry.Scheme.exists_map_at_refinement_of_affine_limit`
  (node `lem-sbc-pointed-section-stage-descent`).
- `AlgebraicGeometry.Scheme.GaloisCover.exists_baseChange`
  (node `lem-sbc-galois-cover-base-change`), including its private comparison lemma.

One new named hole remains, with proof exactly `:= by sorry`:
`AlgebraicGeometry.Scheme.GaloisCover.exists_stage_of_affine_limits`
(node `lem-sbc-galois-cover-stage-descent`). Its module and node contain the source
and complete proof in words: reindexing, finite étale surjective model descent,
finite action descent, and descent of the torsor comparison inverse and equations.

This is a decomposition: one original hole closed, one strictly smaller hole added,
net zero direct holes. It is not a claim of an axiom-free proof of torsor descent.
There are no other sorries in the delivery and no definitions depending on an
arbitrary witness of an unproved existence theorem.

Edge cases: fixed-stage factorization does not assume `P` qcqs or finite; only its
map is locally finitely presented. The actual proof obtains cofilteredness and
initiality for `Over i` from Mathlib. Base change works over empty schemes, for the
trivial finite group, and for disconnected torsors; the proof never uses a point,
connectedness, or commutativity. Unpointed descent retains the affine-transition
assumption, and its finite equations include the torsor inverse equations and
surjectivity, so no weaker cover notion is substituted.

## No longer needed

Removed the target module's proof imports:

- `Sheaf.AlgebraicGeometry.DescendFinite`
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`

The target uses the three new modules instead. The old parent proof dependencies
`lem-weil-pbc-descend-finite`, `lem-weil-pbc-descend-etale`, and
`thm-pd-spreading-out` now belong to the remaining unpointed-descent node's proof
plan and are imported by that module. Thus these are relocated direct imports,
not modules pruned from the target's closure. The reindexing and surjectivity
dependencies of that plan are also imported there. No blueprint unit or step is
bypassed; no whole mathematical dependency is claimed unnecessary.

The pointed step needs neither the large `Sheaf.Paper.EtaleFiniteDataDescent`
theorem nor a new section-descent sorry: Mathlib supplies factorization directly.
The base-change step needs neither generic-fibre hom extension nor generic-fibre
torsor identity as a dependency. Those were considered during search, not imported.

## Where the brief, the DAG or earlier work was wrong

No error was established in the original statement or unit route. The original
DAG's final section-descent step can be formalized using existing Mathlib without
another hole; its finite-stage torsor base change can also be proved directly.
The named finite/étale descent dependencies alone do not supply descent of the
finite group action and torsor comparison. That combined unpointed step is now
explicitly isolated, rather than leaving the entire pointed argument as a hole.

## New nodes

`lem-sbc-galois-cover-stage-descent` in
`dag/nodes/sec-smooth-base-change/lem-sbc-galois-cover-stage-descent.json`
states unpointed finite torsor descent. This is the sole new sorry, strictly a part
of the parent's argument. It inherits the unit and blueprint ancestry and records
reindexing, finite/étale/surjective descent, and finite-presentation descent as its
proof dependencies.

`lem-sbc-pointed-section-stage-descent` in
`dag/nodes/sec-smooth-base-change/lem-sbc-pointed-section-stage-descent.json`
records the proved generic factorization lemma. Its proof uses only Mathlib.

`lem-sbc-galois-cover-base-change` in
`dag/nodes/sec-smooth-base-change/lem-sbc-galois-cover-base-change.json`
records the proved base-change construction, including the comparison-isomorphism
argument. Its proof uses only Mathlib and the existing GaloisCover fields.

The parent node's proof, proof_deps, and proof_origin follow the actual Lean proof.
No change record is needed: no existing interface changed.

## Second reading by M1

1. Interface: PASS. Compared all four delivered modules with the repository.
   Only the pointed module already exists; its diff changes three plain imports
   and the proof body. Its existing signature, docstring, visibility, and public
   imports are byte-for-byte unchanged. The other three modules are new. No
   definition or target statement changed, and no change record is required.
2. Proof and axioms: PASS. Compiled all four modules in import order through
   `lcompile.py --all`, without errors or warnings. Scratch copies with
   `#print axioms` confirm that `GaloisCover.exists_baseChange`, its private
   `torsor_comparison_baseChange`, and `exists_map_at_refinement_of_affine_limit`
   use only `propext`, `Classical.choice`, and `Quot.sound`. The pointed theorem
   and `GaloisCover.exists_stage_of_affine_limits` additionally use `sorryAx`,
   exactly as expected from the single declared residual hole. Text inspection
   finds exactly that named theorem's `:= by sorry`, no forbidden declarations,
   and no hollow definitions. The base-change cover is explicitly built from a
   pullback; no data is defined by choosing an arbitrary witness of a sorry.
3. Split-off statements: PASS. Read each signature and natural-language proof.
   The sole remaining hole discards the second system, its section and limiting
   cone, and the given point; it is strictly the unpointed part of the original
   argument. The point and refinement argument is proved independently, so this
   is a genuine decomposition, with one original hole closed and one added,
   rather than net proof progress. The unpointed descent proof follows the
   finite-etale equivalence of [Stacks 0BTV](https://stacks.math.columbia.edu/tag/0BTV)
   and finite map/equality descent of
   [Stacks 01ZM](https://stacks.math.columbia.edu/tag/01ZM); the finite action,
   inverse and inverse equations descend at a common refinement. Checked empty
   schemes, the trivial group, disconnected covers, and a singleton indexing
   category: no connectedness or nonempty-base hypothesis is hidden. For the
   section lemma, local finite presentation suffices and no qcqs hypothesis on
   P is added. Repeated searches with `msearch.py` using leanfinder (finite group
   action descent), loogle (Scheme/IsLimit/IsFinite), and grep (torsor stage,
   inverse, base change), plus `rg` over both library roots, found no existing
   bundled result replacing the residual theorem. No short proof closing it was
   found; the two auxiliary results already have complete Lean proofs.
4. Route and pruning: PASS after repair. Read the original proof dependencies,
   their recorded declarations, Mathlib's factorization theorem and initiality
   machinery, and `dag/units/sk-prop-input-spreading.json`. The limit-reduction
   step remains the same: cover and action descent, point descent, then base
   change. The unit's existing `realized` arrays are empty; this delivery does
   not alter them or bypass a node recorded there. All three old parent
   dependencies are listed above as relocated, and none is claimed globally
   pruned. Restored the residual module's five plain proof-plan imports to
   prevent accidental removal of still-needed branches from the import closure.
   The actual auxiliary proofs have no unused direct imports: the section
   proof needs `Filtered.Final` for initiality, and the base-change proof needs
   the existing GaloisCover definition and its Mathlib dependencies.
5. DAG: PASS. Parsed all four JSON files; checked every Lean statement field
   verbatim against its declaration and every `proof_deps` list against the
   union of step `uses`. The existing node changes only `proof`, `proof_deps`,
   and `proof_origin`. Each new node has the required source, search records,
   creation metadata, blueprint ancestry, chapter/unit and Lean record. The
   parent's three steps match the explicit Lean assembly; the two proved nodes
   describe their Mathlib proofs, and the residual node records its postponed
   argument and dependencies.

Changed during second reading: restored five plain imports in
`GaloisCoverStageDescent.lean`, corrected the report's pruning description,
and recorded these review findings. No proof, signature, or node statement was
rewritten.
