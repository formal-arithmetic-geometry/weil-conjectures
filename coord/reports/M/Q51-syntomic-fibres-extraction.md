# Q51 syntomic fibre definition extraction

The return of Q51 head ca68d1b97d4c requires the two fibre predicates to have a
definition owner instead of making the locality statement cite the unrelated
locus theorem. The retained worker packet implements this correctly, but the
old owner is outside the locality item's prerequisite closure on both the base
and repaired delivery. `stage2_delivery.read_delivery` excludes its node, then
rejects its module as unowned. The last retry reproduces this after compiling
all three modules. No provider error caused these repair failures.

This maintenance change performs the shared extraction first:

- `def-sfb-complete-intersection-fibres` owns the two existing predicates in
  `Sheaf.AlgebraicGeometry.CompleteIntersectionFibres`.
- `SyntomicLocusBaseChange` publicly imports that module and removes only those
  definition blocks. The definitions' signatures, bodies and documentation move
  verbatim except for their blueprint owner tags. All theorem statements,
  private helpers and proof bodies remain byte-for-byte unchanged.
- The old owner's node cites the new definition and removes only the moved names
  from its declaration inventory; its Lean note explains the extraction.

The original return's request to include the old-owner repair in the consumer
delivery is now fulfilled by this prerequisite maintenance commit. The next Q51
worker should deliver only its locality node, locality module and report. Cite
the landed definition node and import its module; do not restore an unused
theorem edge or introduce a statement correction. Remove the already-landed
definition/old-owner copies from the active sandbox after preserving `.bak`
copies, and run the normal `deliver2.py --no-push`, then delivery. The independent
review of the locality statement still applies normally.

No launcher-owned code, preflight gate, review service or landing tool changes.
Existing modified files have sibling `.maint-Q51-syntomic-1792846320.bak`
preimages. Newly created files have `.bak` copies of their initial contents.
Validation results are recorded in the maintenance session's REPORT.md.

Validation: tools/lean_file.sh compiled CompleteIntersectionFibres (14.5 s),
SyntomicLocusBaseChange (22.8 s) and the retained locality module (8.6 s),
one file at a time in group maint-Q51-syntomic with the default 60 s limit,
without Lean diagnostics. nt_incremental2.check found no DAG delta findings;
the new definition record check passed. Exact text comparison verified the
extraction and preservation of every existing proof.
