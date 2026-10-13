## What changed

Repaired reviewer X-07e79 E1 / H3 in
`Sheaf.AlgebraicGeometry.ReducedGenericFibreMapCore`: added precisely
`haE : aE = ((algebraMap k' E).comp e.toRingHom).toAlgebra` to
`AlgebraicGeometry.exists_reduced_generic_fibre_map_core`. Removed the resolved
STATEMENT-DISPUTED comment. The existing proof hole and docstring are retained.
Updated the node's `lean.statement` verbatim; its informal statement already
requires the induced algebra, so its statement and proof plan stay unchanged.

Delivered the forced caller adaptation in
`Sheaf.AlgebraicGeometry.ReducedGenericFibreFieldEmbeddingCore`: append `rfl`
to the existing call, without changing any signature, visibility, or import.
Change record: `coord/changes/exists_reduced_generic_fibre_map_core.md`.

## Proved and sorry left

Holes closed: none. Holes added: none. The retained named hole is
`AlgebraicGeometry.exists_reduced_generic_fibre_map_core`, node
`lem-sbc-reduced-generic-fibre-field-embedding-core-map`.
This delivery repairs a false intermediate statement; it claims no proof,
no decomposition, and zero net hole progress. The caller
`AlgebraicGeometry.exists_reduced_generic_fibre_field_embedding_core`
retains its complete assembly proof from the corrected core theorem.

## No longer needed

No existing import, module, or node is pruned in this repair. The previously
rejected helpers `ReducedGenericFibreMapCoreDominant` and
`ReducedGenericFibreMapCoreBase` and their nodes remain absent. No new module
or node is added; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original Lean signature omitted the node's induced-algebra condition.
The reviewer counterexample k = Q(t), L = E = Q(u), supplied t ↦ u², and
arbitrary aE given by t ↦ u² + 1 refutes it. The added equality excludes
this incompatible structure and matches the intended affine tensor argument.
The caller already constructs exactly the required structure, so `rfl`
supplies its compatibility. The rejected two-helper decomposition is not
restored. The old second-reading section described the returned version and
has been removed for a fresh independent second reading.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ReducedGenericFibreFieldEmbeddingCore` is unclaimed.
Compiled its original source against the corrected core in the sandbox:
it fails at line 63:9 with `Tactic rcases failed`, because the expression has
type `aE = ((algebraMap k' E).comp e.toRingHom).toAlgebra → ∃ h, ...`
and is not an inductive datatype. Its sole changed line is line 64, appending
`rfl` after `aE`. This discharges the new equality using the existing local
construction; every existing signature, public visibility, import and other
proof line stays identical. Both delivered modules compile together. The dry
run additionally checks the original against the compiled baseline and then
against the changed dependency, as well as compiling the adapted module.

## Second reading by S1

1. **Interfaces and scope: pass as a documented statement repair.** Compared both
   delivered modules with the repository using `diff -u`. The core has precisely
   one new hypothesis, `haE`, recorded verbatim in the change record; its other
   binders and entire conclusion are unchanged. The caller differs only by the
   final `rfl` argument. Its signature, visibility, definitions, and imports are
   byte-for-byte unchanged. `tools/downstream.py --uses` and source search find
   only that caller and the declaration itself using the changed name. The 149
   transitive importers retain the unchanged caller interface. No target or
   definition is changed.

2. **Compilation and proof integrity: pass with the reported existing hole.**
   Independently compiled the two modules together, in import order, through
   `lcompile.py --all`: both compile without errors or warnings. A scratch probe
   importing these exact sandbox artifacts printed axioms for both declarations:
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter
   comes from the retained named core theorem. There is exactly one `sorry` in
   the core module and none in the caller; no forbidden construct or hollow
   definition occurs. The explicit local algebra construction in the caller
   is genuine data and does not choose an arbitrary witness from the open theorem.

3. **Truth and split statements: pass; none newly split off.** The arbitrary
   algebra in the old statement really is a fault: for the specified quadratic
   rational-function example its requested scalar map requires a square root
   of `u² + 1` in `Q(u)`, impossible by the odd valuation at that irreducible.
   The new hypothesis fixes precisely this incompatibility. For the corrected
   statement, injectivity of the original fibre ring into L survives tensoring
   by k'. The tensor of L with the purely inseparable extension has one prime;
   its map to E has that prime as kernel, hence induces an injection of its
   reduction. Injectivity also detects nilpotence in the smaller tensor ring.
   Localization at the integral base's generic point commutes with reduction,
   giving the required fibre injection and scalar map. When k' is the identity
   extension the argument reduces to the original injection and field extension;
   in positive characteristic the single-prime argument allows nilpotents and
   removes them. An empty original fibre cannot satisfy the dominant field-point
   hypothesis. Thus the retained theorem is true, and `rfl` supplies exactly the
   needed compatibility in its existing caller. No new theorem or hole is added.

4. **Route, search, and pruning: pass for this repair.** Repeated search with new
   wording through Lean Finder (reduction, generic-point fibre, dominance), Loogle
   (including the fully qualified purely inseparable tensor-spectrum theorem),
   and grep, and searched both local Lean roots. No direct replacement for the
   complete affine construction was found. Loogle's unqualified dominance query
   could not resolve the identifier; the qualified tensor-spectrum query succeeds
   and supplies an ingredient only. Closing the retained geometric construction
   is not a few-minute corollary of those results. The four public Mathlib imports
   supply notions used in signatures; the core's import in the caller is already
   proof-only. No import or old proof dependency is removed. The unit record
   `sk-prop-normal-form` has empty `realized` entries in the existing repository;
   this repair leaves it and every unit step unchanged, and introduces no bypass.

5. **DAG agreement: pass for the delivered core node.** Verified by exact string
   comparison that `lean.statement` equals the corrected Lean signature. The
   informal statement already specifies the induced algebra; only its Lean record
   changes. The unchanged `proof`, empty `proof_deps`, and `proof_origin` continue
   to describe the retained affine argument. There is no new node to validate.
   The caller node's older informal affine proof plan is outside this forced
   one-line adaptation; its Lean statement remains unchanged.

Second reading changed only this report and scratch verification files; the
submitted Lean, node, and change record needed no further repair. This delivery
closes zero of the item's one hole, adds zero holes, and prunes nothing. It is a
correction of a false intermediate statement, not proof progress.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ReducedGenericFibreFieldEmbeddingCore
Original against changed dependencies failed:
```
/tmp/forced-adaptation-mb84l70t/lean/Sheaf/AlgebraicGeometry/ReducedGenericFibreFieldEmbeddingCore.lean:63:9: error: Tactic `rcases` failed: `x✝ : aE = ((algebraMap k' E).comp e.toRingHom).toAlgebra →
  ∃ h,
    IsSchemeTheoreticallyDominant h ∧
      h ≫ Scheme.Hom.fiberToSpecResidueField ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q) η' =
        Spec.map (CommRingCat.ofHom (algebraMap (↑(S'.residueField η')) E))` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-mb84l70t/.lbuild) [2.5 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
