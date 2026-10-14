## What changed

Repaired the queued upstream-review #1428 duplicate. Retired the public declaration
`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`. Forward-ported the exact
upstream `AlgebraicGeometry.Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`
interface into its module, since upstream Curve/Jacobian.lean is absent from the
pinned library. The former cokernel proof is now the private proved `picQuotient`.
The canonical theorem uses existing torsion/divisibility components and explicit
additive/multiplicative transports, without any new proof holes. The sole caller,
PicProperNTorsion, uses the canonical theorem's second clause and keeps its exact
statement and imports. Both DAG proof routes and the component lean record are updated.

Change record: coord/changes/picard-cokernel-canonical-interface.md.

## Proved and sorry left

This is a duplicate-interface repair, not a reduction in holes: the assigned module
already had zero sorry at dispatch. Holes closed: 0. Holes added: 0. Sorries left in
both delivered modules: none. `picQuotient`,
`Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`, and the unchanged-signature
`Scheme.Hom.pic_proper_ntorsion` have complete compiling proofs.

The n=0 case is excluded by the nonzero cast hypothesis; n=1 is covered by the same
quotient and kernel calculations. No positive-genus hypothesis is introduced, so
genus zero remains covered. The over-scheme hypotheses translate using smooth
relative dimension one and connectedness. No definitions or target meanings change.

## No longer needed

This delivery removes the baseline imports Mathlib.Algebra.Group.TypeTags.Hom
and Sheaf.AlgebraicGeometry.Curve.PicardDecomposition, using the direct degree-map
route through WeilConjectures.AlgebraicGeometry.Curve.Picard. No DAG node or whole module is
pruned. The degree-surjectivity part of the decomposition node, torsion and divisibility
components remain needed. The second reader replaced the sandbox full decomposition
with the delivered direct degree-map proof and removed its direct import
Sheaf.AlgebraicGeometry.Curve.PicardDecomposition in favor of the proof-only import
WeilConjectures.AlgebraicGeometry.Curve.Picard. No whole module is newly pruned. The retired public cokernel declaration has no remaining callers.

## Where the brief, the DAG or earlier work was wrong

The dispatcher describes an item with sorry, but the source at dispatch already
compiled without sorry. coord/repairs.txt supplies the actual task: the upstream
review duplicate. The cited upstream Curve/Jacobian.lean and its canonical theorem
exist in the upstream PR snapshot but not the pinned source library or build;
therefore a direct import is unavailable. This delivery forward-ports the canonical
interface using available proofs instead of claiming that unavailable import works.
The canonical interface covers all three components, with the cokernel node mapping
to its second clause. When the newer source module is adopted, drop this forward-port.

## Forced adaptations

Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion (unclaimed): the original line 70
fails against the delivered dependency with:

```
error(lean.unknownIdentifier): Unknown constant
  AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker
```

Only that have-command is replaced by the hypotheses needed for the canonical
upstream theorem and the quotient-notation transport. The theorem signature,
visibility, imports, and the surrounding ht/hd/conjunction proof lines are unchanged.
The unmodified original was compiled against the changed dependency and failed;
the adapted module compiled in the same overlay. The delivery tool repeats this
counterfactual check. Both files compile in under five seconds locally.

## Earlier second reading (a previous round; superseded)

1. Compared both Lean modules with the repository using diff and the declaration
   parser. The caller has no changed signatures, visibility, or imports. The only
   public interface replacement is the declared retirement of
   Scheme.Hom.pic_proper_ntorsion_coker in favor of the canonical upstream theorem;
   the change record covers it. Compared the new signature with the upstream
   Curve/Jacobian.lean snapshot, including its section variables: identical
   hypotheses and all three conclusions. No definition or target changes.
2. Compiled both modules in import order with lcompile.py, cleanly. No local sorry,
   axiom, unsafe, opaque, implemented_by, extern, or hollow definition. Scratch
   #print axioms checks for picQuotient, the canonical theorem and the aggregate
   show only propext, Classical.choice, Quot.sound and inherited sorryAx from
   still-open upstream dependencies. These are complete local proofs, not claims
   that the whole import closure is axiom-free. The delivery repeats the axiom
   and original-caller counterfactual checks.
3. No new split-off statement, new node, or proof hole. The private helper is
   completely proved. Checked n=0 is excluded by hn, n=1 gives trivial torsion
   and quotient, genus zero gives trivial torsion, and relative dimension one
   excludes Spec k. All transports are explicit group equivalences; no arbitrary
   data is chosen from an unproved existence theorem in a definition.
4. Found the shorter direct degree-map route in the source library. Used it
   as the private helper instead of the baseline full Picard decomposition; used
   the source-library surjective_picDegreeHom, degree-zero divisibility and
   Mathlib's quotient first-isomorphism theorem. Searched the library by degree
   surjectivity and by both theorem names, and read the upstream canonical proof.
   The canonical module is absent from the pinned library, so its public
   interface must be forward-ported here. Imports for torsion and picardZero
   signatures are public; component proofs and Curve.Picard are plain imports.
   No old proof-dependency node becomes unused: the decomposition node still
   supplies degree surjectivity. The unit realized fields remain untouched.
5. Checked node Lean records against signatures and proof_deps against the
   union of uses. Restored the current degree-map route and its dependencies
   in the cokernel node, adding the torsion dependency used by the canonical
   interface. The aggregate node records the forced canonical-theorem call.
   No new-node obligations apply. Restored repository-owned review metadata.

Second reading changed the private cokernel proof, its proof-only import and
DAG route, and clarified pruning and inherited axioms in this report. Holes
closed: 0; holes added: 0. This delivery repairs a duplicate interface.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-o9h8hrug/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:70:13: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
/tmp/forced-adaptation-o9h8hrug/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:68:77: error: unsolved goals
k : Type u
inst✝⁴ : Field k
inst✝³ : IsAlgClosed k
C : Scheme
f : C ⟶ Spec (CommRingCat.of k)
inst✝² : IsConnectedCurve f
inst✝¹ : Smooth f
inst✝ : IsProper f
n : ℕ
_hn : ↑n ≠ 0
ht : Nonempty (↥(powMonoidHom n).ker ≃* Multiplicative (Fin (2 * genus f) → ZMod n))
⊢ Nonempty (↥(powMonoidHom n).ker ≃* Multiplicative (Fin (2 * genus f) → ZMod n)) ∧
    Nonempty (C.Pic ⧸ (powMonoidHom n).range ≃* Multiplicative (ZMod n)) ∧ ∀ L ∈ picZero f, ∃ M ∈ picZero f, M ^ n = L

(with the modules compiled into /tmp/forced-adaptation-o9h8hrug/.lbuild) [2.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by Y3

1. PASS: diffed both delivered modules against the read-only repository. The
   aggregate caller's complete pre-proof text (including signature and imports)
   is byte identical. The retired cokernel declaration and replacement canonical
   interface are covered by the change record. Compared the canonical statement
   and section hypotheses with the local upstream snapshot
   `maint/stmtpr/upstream/WeilConjectures/AlgebraicGeometry/Curve/Jacobian.lean`:
   the interface matches. No target statement or definition changes.
2. PASS: compiled both modules in import order using lcompile.py, without errors
   or warnings. Scanned both for forbidden declarations and local sorry: none.
   Scratch-copy #print axioms checks of picQuotient, the canonical theorem, and
   Scheme.Hom.pic_proper_ntorsion show only propext, Classical.choice, Quot.sound
   and inherited sorryAx. The inherited holes prevent claiming a fully closed
   import closure; no local hole is introduced or hidden in a definition.
3. PASS: no split-off theorem, new node, or new sorry. Read the private helper
   and all additive/multiplicative transports. For n=0 the cast hypothesis is
   impossible; n=1 gives the trivial torsion and quotient; genus zero gives the
   trivial torsion group. Dimension one excludes Spec k. The root witnesses
   occur only within theorem proofs, not in data definitions. Searched the
   library for the old and canonical names and degree-map APIs, and ran msearch
   loogle for quotient/range APIs: no shorter available canonical interface.
4. PASS: the direct degree-modulo-n map uses existing degree surjectivity,
   degree-zero divisibility, and Mathlib's first isomorphism theorem. All old
   proof-dependency nodes remain used; no whole module is pruned. The removed
   imports and retained degree-surjectivity part are listed under No longer
   needed. Read dag/units/sk-thm-curveestimate.json: its realized fields and
   chapter/unit route are unchanged. Public imports support the signature;
   component theorems and Curve.Picard are proof-only imports.
5. PASS: checked both node records, Lean signatures, proof steps and the exact
   union of their uses against proof_deps. Existing node changes are confined
   to lean, proof, proof_deps and proof_origin. The cokernel node attaches to
   the canonical theorem's second clause; its route also records the torsion
   and divisibility clauses now provided by that interface. No new-node
   obligations apply.

This reading changed only picQuotient's docstring, replacing the stale product
splitting description with its actual direct degree-map argument, and appended
this review. The Lean proof terms needed no repair. Holes closed: none (0);
holes added: none (0); split off: none (0). This is the queued duplicate-interface
repair, not a net proof-hole reduction. Delivery checks independently recompile
both modules, inspect their axioms and test the original caller against the
changed dependency before accepting its forced adaptation.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-k50m5ziy/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:70:13: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
/tmp/forced-adaptation-k50m5ziy/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:68:77: error: unsolved goals
k : Type u
inst✝⁴ : Field k
inst✝³ : IsAlgClosed k
C : Scheme
f : C ⟶ Spec (CommRingCat.of k)
inst✝² : IsConnectedCurve f
inst✝¹ : Smooth f
inst✝ : IsProper f
n : ℕ
_hn : ↑n ≠ 0
ht : Nonempty (↥(powMonoidHom n).ker ≃* Multiplicative (Fin (2 * genus f) → ZMod n))
⊢ Nonempty (↥(powMonoidHom n).ker ≃* Multiplicative (Fin (2 * genus f) → ZMod n)) ∧
    Nonempty (C.Pic ⧸ (powMonoidHom n).range ≃* Multiplicative (ZMod n)) ∧ ∀ L ∈ picZero f, ∃ M ∈ picZero f, M ^ n = L

(with the modules compiled into /tmp/forced-adaptation-k50m5ziy/.lbuild) [2.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
