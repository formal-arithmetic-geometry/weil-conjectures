# Q18 factor-squares selector extraction maintenance

The return for lem-sf-relative-product-base-change-factor-squares at 191b54044d2
requires extracting the existing PodCoefficientStage selectors from the theorem
module PodCtfAdjunctions. That theorem is outside the consumer prerequisite closure
after the requested H2 repair. stage2_delivery.py excludes its node, then rejects
the companion module as having no delivery owner. Repeated Lean compiles cannot
resolve this dependency-classification mismatch.

Maintenance landed the existing worker extraction separately, as one interface set
20261024T175027-L-3988132, using tools/land_set.sh. All 20 existing public declaration
signatures and masked bodies are identical across the original and extracted files.
The new definition owns all eight moved selectors. PodCtfAdjunctions publicly imports
it and its DAG node now cites it. All other theorem node fields are preserved.
Single-file tools/lean_file.sh checks passed: selectors 9.1 s; adjunctions 14.8 s;
60 s per file. Name, import, and new-definition metadata checks passed.

Next Q18 worker: rebase the retained repair on current sheaf-dag. Keep the item
module's CtfCoefficientStageSelectors import, direct definition citations and signed
symmetry replacement. The selector definition and former-owner repair now exist
on the base; do not redeliver old copies of those nodes/modules. Deliver only the
item node, item module, and report, through normal deliver2.py dry-run/delivery.
Do not reintroduce an unused theorem dependency. The original return remains the
review record; this maintenance does not complete the consumer's stage-2 review.

Backups: local/maintenance/Q18-factor-squares-1792863238/<original path>.bak
(empty .bak plus .bak.absent records a previously absent path).
No launcher, preflight, review, landing tool, admission, or concurrency setting changed.
