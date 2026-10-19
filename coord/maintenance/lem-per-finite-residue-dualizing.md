# NX lem-per-finite-residue-dualizing maintenance, 2026-10-19

The last six failures at returned head ca455f296d6d were reproducible stage-2
preflight refusals. The return's first suggested H13/H4 repair uses module
Sheaf.Paper.ProEtaleFixedModuleConstructible while retaining N6's primary
AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf. That declaration
is exported by the module's public import of ProEtaleConstructibleSheaf.
The export probe and the item compile, but check_existing in
 tools/stage2_delivery.py searches only the named module's direct text.
The gate rejects with:

    (d) dependency node def-weil-proetale-constructible-sheaf:
    IsConstructibleProEtaleModuleSheaf is not declared in
    lean/Sheaf/Paper/ProEtaleFixedModuleConstructible.lean

Workers repeatedly selected this first route and their brief forbids editing
the validator. The second explicitly permitted route avoids the mismatch:
leave N6's record intact and own the fixed interface in the item delivery.
The repair installs that route in the NX sandbox and records it in the
launcher route note, so future retries have a concrete working continuation.

The item declares finiteResidueProConstructibleSheaf, a transparent abbrev to
the existing Scheme.IsConstructibleProEtaleFixedModuleSheaf, and lists it in
lean.declarations. finiteResidueProBoundedConstructible uses the alias. No
mathematical predicate is copied or proved, and no new assumption is added.
The complete old/new bounded predicate equality checks by rfl. The theorem
signature and every FiniteResidueDualizingAssertion field are unchanged.
The dependency JSON is restored to current server content, including N6's
module, declaration, signature, declarations and full compatibility note;
it is omitted from the delivery delta. All prior accepted H3/H5 repairs and
the canonical evaluation-comparison statement dependency are retained.

Validation:
- Full isolated no-push delivery passed (candidate b129300b22); its exact
  staged set was the item module, item JSON, and report only.
- The installed worker sandbox also passed the normal no-push check
  (candidate d5754cf5db), with the same three-file delta.
- A full copy of the module plus the old/new bounded-predicate equality
  passed tools/lean_file.sh in 4.6 s, nice 19, two Lean threads, limit 60 s.
- The initial scratch equality check redeclared an already present universe;
  only that scratch setup was corrected before the successful check.

All changed existing sandbox files have .bak.maintenance-1792354238 copies.
An exact patch for the item source and records is archived beside this note.
It starts from the retained superset packet, not arbitrary current main.
The report was rewritten to describe the second repair and validation.
The launcher route note is installed both locally and in the project's
 tools/launcher/route-notes/lem-per-finite-residue-dualizing.md.

Next worker: read report.md, preserve the installed item-owned alias and the
unchanged shared dependency record, run deliver2.py with --no-push against
current sources, finish the required self-check, then deliver normally.
Do not reselect the incompatible public-import superset route. If another
worker overwrote the repaired packet, use the archived patch carefully and
restore the current dependency node exactly from live server records.

No protected launcher, review service, or landing tool was edited. The proper
longer-term validator enhancement would resolve the primary declaration
through public imports from the immutable base while preserving namespace,
source provenance and signature checks; this is reported, not implemented.
No concurrency controls, global build, or process termination were used.
An older attempt had HTTP 429, but the six diagnosed failures were the concrete
non-provider refusal above; no provider behavior was changed. The item remains
subject to ordinary worker delivery and the maintainer's independent review.
