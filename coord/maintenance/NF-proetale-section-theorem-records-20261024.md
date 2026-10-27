# NF theorem-record registration, 2026-10-24

Item: `def-pd-proetale-section-module-functors`, stage 1; returned head
`15dd87a10e0c497ce3ae8f980ebccaffcd443f93`.

The human repair requires separate unsplit nodes for three existing sorry theorems,
each with its exact `lean.declaration`. The retained NF sandbox already contains
the three statements, their sources, and five recorded searches each. Repeated
worker attempts passed preflight but correctly refused to push: stage-1 delivery
filters `lean` out of NEW nodes. This is also enforced by server preflight, which
rejects a new node carrying the maintainer-owned `lean` field. Merely adding
`lean` to the launcher's new-node whitelist would therefore fail server preflight.

Maintenance registers the three prepared nodes on the authoritative server as
unsplit records with empty proofs and exact existing declaration bindings:

- `lem-pd-section-pull-delta-isiso` ->
  `AlgebraicGeometry.ProEtale.ModuleRingedComparison.pull_delta_isIso`
- `lem-pd-section-pull-eta-isiso` ->
  `AlgebraicGeometry.ProEtale.ModuleRingedComparison.pull_eta_isIso`
- `lem-pd-section-push-normalized-exists-unique` ->
  `AlgebraicGeometry.ProEtale.ModuleRingedComparison.pushNormalized_existsUnique`

Their module is `Sheaf.Paper.ProEtaleSectionModuleFunctors`, at
`lean/Sheaf/Paper/ProEtaleSectionModuleFunctors.lean:552`, `:560`, and `:532`
respectively. Each body is still `sorry`. Registration is an assignment of work;
it asserts neither a completed proof nor an accepted parent split. No reviewed
or completion flags are set. Node contents are the retained worker JSON verbatim.
The parent node and Lean source are untouched.

The ordinary delivery tool now sees these as existing nodes and preserves their
maintainer-owned `lean` records from the base. An unchanged sandbox copy is omitted
from the delivery diff while remaining in the full delivery tree. Keep the three
sandbox copies, citations, searches, and parent split; rebase through the normal
delivery helper, inspect the full commit tree for all three bindings, and deliver
the parent split for the usual independent review.

The earlier BLOCKED diagnosis is historical once this registration is on the
delivery base. Evaluating `merge_split_node(None, ...)` alone still demonstrates
the general NEW-node policy; it no longer models these three existing records.
Compare against each actual base node instead.

No launcher, admission, review, preflight, or landing tool is changed. A general
future mechanism for stage-1 theorem registration would need matching scoped
support in packaging and server preflight; do not globally grant stage 1 ownership
of `lean` on existing nodes. This item's supported repair is authoritative record
registration under the merge lock.
