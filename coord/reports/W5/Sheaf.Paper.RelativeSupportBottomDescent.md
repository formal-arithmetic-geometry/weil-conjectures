## What changed

Restored Sheaf.Paper.RelativeSupportBottomDescent from the exact quarantine archive
recorded in coord/rework.tsv. Migrated its public scalar-comparison import from the
retired Sheaf forwarding module to the canonical upstream module, preserving its
public exports. All 36 public declaration headers and all public definition bodies
remain unchanged; no other Lean module is delivered.

Proved the support-kernel additivity and injective acyclicity, exact localization,
the uniquely inclusion-normalized evaluation and global kernel isomorphisms and their
derived comparisons, scalar-forgetting naturality and derived invertibility, and the
canonical pro-etale support comparison for every scheme. The evaluation proof constructs
the isomorphism of the two open complements from equality of their ranges, transports
the evaluated kernel fork, and proves naturality and uniqueness by its monomorphism.

For scalar forgetting, injective module sheaves have acyclic underlying abelian
evaluations; the three-functor derived exact sequence gives support acyclicity,
including the degree-zero surjectivity argument. For pro-etale comparison, direct image
preserves injectives and its composite with the etale support functor is literally the
pro-etale support functor. Its derived unit gives the required acyclicity. The ordinary
unit is a kernel isomorphism with the published inclusion normalization, so its canonical
derived base-change map is invertible. This avoids a separate five-lemma argument.

The existing node records these helper proofs and the shorter comparison route. The
main smooth-pair theorem retains its original statement, original hole, and geometric
proof plan. This is a partial delivery under the brief's rule for modules with several
holes, not a claim that the main vanishing and descent theorem has been proved.

Change record: coord/changes/W5-relative-support-bottom-descent-restoration.md.

## Proved and sorry left

Closed 15 of the 16 original named theorem holes, all in namespace
AlgebraicGeometry.Etale:

- relativeSupportKernel_additive
- relativeSupport_isAcyclic
- relativeSupport_terminal
- relativeSupport_evaluationAcyclic
- relativeSupportEvaluationIso_existsUnique
- relativeSupportRestriction_additive
- relativeSupportRestriction_colimits
- relativeSupportRestriction_limits
- relativeSupportDerivedEvaluation_isIso
- relativeSupportGlobalIso_existsUnique
- relativeSupportGlobalDerived_isIso
- relativeSupportForgetIso_naturality
- relativeSupportModuleForget_colimits
- relativeSupportForgetDerived_isIso
- relativeSupportProComparison_isIso

One original hole remains: AlgebraicGeometry.Etale.relative_support_bottom_descent,
node lem-pur-relative-support-bottom-descent. In particular the smooth-pair stalk
vanishing and its combination with the specified lowest-row edge, restriction
naturality, and cover separation are still required. The original complete proof in
words remains with this declaration and in the node.

Holes added: zero. Split-off statements: zero. Every added private helper is proved;
there is no sorry in a definition. Existing imported declarations can still depend on
their own recorded holes, as permitted for this stage. The module compiles through the
prescribed single-file compiler; the delivery tool runs its independent preflight.

## No longer needed

Removed the retired public import
Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison and replaced it with
the canonical upstream owner; this is an import migration, not a withdrawal of its
mathematics. Removed the direct private Sheaf.AlgebraicGeometry.SupportLongExact import.

The pro-etale comparison proof no longer needs the support five lemma, so the item's
node no longer directly cites thm-pur-with-support-exactness or
lem-weil-pbc-module-abelian-derived-direct-image-comparison. Scalar-forgetting evaluation
acyclicity is cited through its precise existing node instead. The upstream derived
comparison module is still needed for that private helper. SupportLongExact is still
transitively imported by SupportSiteComparison; neither module is claimed globally
pruned. No module or declaration is withdrawn. The other declared dependencies and
proof imports remain needed by the retained final-theorem plan; no geometric dependency
is pruned merely because its parent proof remains unfinished.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined rather than withdrawn. Its absence from lean/ did not authorize
removing its attachment, its dependencies, or its archived consumers. The restoration
needed the public import migration already described by the forwarding-module retirement
record. The archived source otherwise gives the intended interfaces unchanged.

The support five-lemma route is unnecessary for the comparison instance: the existing
derived comparison unit and composition theorem give a shorter canonical argument.
A direct import of the adopted source's SupportCohomologyHom module collides with the
support-cohomology declarations already supplied by the Sheaf interface. The delivered
proof instead gives the required kernel argument locally using proved private helpers;
it neither imports that colliding module nor modifies adopted source declarations.

No statement is disputed, no hypothesis is changed, no new node is introduced, and no
consumer adaptation is required.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
