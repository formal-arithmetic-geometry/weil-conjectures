# Maintenance: independent algebraic-space set stalk

The NV H2 return on head aea8c34a8f27 required extracting pointedSetStalk and
pointedSetGerm from downstream SpaceGeometricPointsConservative. The stage-2
delivery reader excludes downstream nodes from prerequisite ownership and then
rejects the adapted consumer module as having no delivery owner. Repeated worker
retries compiled successfully but could not deliver that cross-node extraction.

This maintenance change performs the extraction directly. The two definition
blocks are identical to the accepted Q93 source after blueprint-id substitution.
The new definition node owns them, the consumer publicly imports its module,
and the consumer node gains the new stmt_dep and drops ownership of the moved
declarations. Its other signatures, data and proofs are unchanged. The still
undelivered theorem is not imported yet; the normal proof-import cycle can add
it when the repaired NV item lands.

Validation: tools/lean_file.sh, default 60 s, one file at a time with private
SHEAF_GROUP=maint-NV-1792844966: AlgebraicSpaceSetStalk 12.8 s;
SpaceGeometricPointsConservative 9.4 s; no warnings or errors. Incremental DAG
validation of both touched nodes passed. No lake build was run.

Next NV worker: keep the repaired EtaleGeometricStalksConservative module and
item node; its stmt_deps must include def-sfb-space-pointed-set-stalk. Rebase on
this commit. Omit the already-landed definition and downstream consumer files
from the pending packet. Do not cite the downstream theorem as a prerequisite:
that recreates a DAG cycle. Run deliver2.py --no-push, then deliver normally.

Landing record: 20261024T124509-L-316186-766
