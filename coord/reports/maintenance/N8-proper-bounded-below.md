# N8 maintenance: bounded-below proper direct image

The repeated stage-2 BLOCKED answers were caused by the item's empty stmt_deps,
not a Lean compile or proof failure. The stage-1 split (side commit 9aec0dade9,
worker delivery 52d9596b60) supplied its five-step proof but omitted the notions
needed to state it. The bottom-up queue therefore offered the item although its
coefficient, constructibility and derived module interfaces had no Lean binding.
The first five counted failures and later retries all reproduce that defect.
The dispatcher intentionally disables runtime waits; failure counts remain
historical evidence and have not been reset or used to gate dispatch.

Maintenance adds these existing interface owners to stmt_deps in both the side
project and the authoritative live DAG:

- sk-def-sfb-condensed-ring and sk-def-sfb-qlbar-condensed: the specified E and
  finite-subextension Qbar_l condensed coefficient conventions.
- sk-def-sfb-pulled-back-coefficients and sk-def-sfb-module-objects: Lambda_X and
  the actual coefficient module categories.
- sk-def-sfb-constructible: the finite constant local models underlying Cons.
- sk-def-sfb-derived-categories: the ambient unbounded derived categories and
  their bounded-below parts.
- def-sfb-module-lower-star and sk-def-sfb-module-derived-pushpull: the underived
  module pushforward and its total derived functor, as used by proof step 1.
- def-weil-derived-cohomology-sheaves and def-weil-proper-morphism: the already
  recorded cohomology and properness definitions used in the statement.

No added dependency has a path to the item through statement or proof edges.
Only stmt_deps changes in each node; statement, proof, proof_deps, source,
review, status and Lean metadata are preserved. In particular,
sk-lem-proper-heart-bound, thm-sp-truncation-e2, kernels/cokernels and extension
closure remain proof-only dependencies. Their results are needed to prove the
item, not to choose its primitives at stage 2. The first eight interface owners
are currently unstated; the last two already have Mathlib records. The normal
queue and the unified dispatcher's existing check of held stage-2 claims now
see the actual missing interfaces. The item becomes eligible again after its
statement downstream is grounded. This is not abandonment or a failure limit.

Backups of existing files are adjacent and end
.maint-N8-proper-bounded-below-1792169776.bak. The server repair is committed
under each repository's coord/.merge.lock with SHEAF_LEAD=L-only and the human's
Git identity. Generated side queue.tsv, queue.md and blueprint-index.tsv are
backed up and refreshed, and left unstaged to preserve other concurrent work.
No Lean file changes; no Lean compile or global build is needed.

For the next worker: use the landed declarations of these existing owners;
do not duplicate them or replace them with arbitrary predicates/functors.
IndCons means sheaves isomorphic to filtered colimits of constructible sheaves
in the actual module category, and Dic means the full derived subcategory with
all cohomology sheaves in IndCons, exactly as the parent
sk-lem-proper-unbounded-window spells out. The names sk-prop-ind-heart and
sk-cor-ambient-ind-derived used by older blueprint text have no current DAG
node, so do not wait on them or fabricate a binding. Search before introducing
any still-missing independent helper definition under the normal brief rules.
Do not identify finite constant scalar local models with arbitrary locally
finitely presented ring-object modules without the needed comparison. Retain
all integer bounds and the b+2d+1 shift, including d=0 and bounded-below objects
with no upper bound. The retained sandbox has reports/searches only; no Lean
statement was delivered. Read tools/launcher/route-notes/
det-proper-unbounded-window-bounded-below.md for the handoff.
