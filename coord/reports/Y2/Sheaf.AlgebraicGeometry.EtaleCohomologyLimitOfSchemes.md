## What changed

Replaced the one direct sorry in
`AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_of_isLimit`
with an explicit group-colimit argument. No declaration signature changed. The constant-pullback
helper and ring specialization retain their original proofs.

Added two independent modules, `Sheaf.AlgebraicGeometry.EtaleLimitCohomologyClassDescent` and
`Sheaf.AlgebraicGeometry.EtaleLimitCohomologyEventualVanishing`. Their statements are respectively
finite-stage existence of representatives and finite-stage detection of zero, rather than a
renamed colimit universal property. Each includes the original geometric hypotheses and all
identity, composition, transition and canonical-leg equations. Neither requires the other.

The assembly chooses a stage representative of an element of the actual group colimit, uses
zero detection to kill it after a transition, and applies the colimit transition relation to
prove injectivity. Existence gives surjectivity. `ConcreteCategory.isIso_iff_bijective` and
`IsColimit.ofPointIso` then give the supplied cocone's universal property. Explicitly shrinking
filtered-colimit preservation handles the index universe u and group universe u+1.

Updated the parent DAG proof and dependencies to this assembly plus its unchanged ring step.
The new nodes retain the affine-site/cofinality/Mayer-Vietoris proof route of original steps 1-8.
The unit `sk-thm-p1` and all its realized steps are unchanged.

Both new modules compile using lcompile.py. The complete assembly also compiles in
`scratchpad/lean/Sheaf/AlgebraicGeometry/ContinuityAssembly.lean`, which contains exactly the
primary declaration and omits the unchanged ring specialization. This scratch file is not a
delivery module. Its axiom output contains the three permitted axioms and sorryAx from the two
remaining statements, as expected for a stage-3 reduction.

The compiled dependency `Sheaf.AlgebraicGeometry.CompatiblePullbackSheafSystem.olean`
was initially missing, then became available through the normal library refresh. The dry run
subsequently passed its local compilation, axiom probes and server compilation. Its first
fetch failed with an SSH connection closure; the retry printed OK and passed the preflight
except for the second reading, which belongs to the second reader. No dependency was copied,
restated or edited as a workaround. The complete assigned module also compiles independently
with lcompile.py. Nothing was pushed.

## Proved and sorry left

Proved from two strictly smaller named claims:
`AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_of_isLimit`.
There is no direct sorry left in the assigned module. Its signatures match the repository's
signatures, including the already proved ring specialization.

The delivery adds exactly these two whole-theorem sorries:

- `AlgebraicGeometry.Etale.etale_limit_cohomology_class_descent`, node
  `lem-weil-pbc-etale-limit-cohomology-class-descent`.
- `AlgebraicGeometry.Etale.etale_limit_cohomology_eventual_vanishing`, node
  `lem-weil-pbc-etale-limit-cohomology-eventual-vanishing`.

These claims retain the geometric and site-theoretic work. The delivery does not assert that
continuity is already free of transitive sorry dependencies.

## No longer needed

Removed these proof imports from the assigned module, relocating their planned geometric work
to the two new independent statements:

- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.CategoryTheory.CohomologyColimitSites`
- `Sheaf.CategoryTheory.ColimitSites`

Their nodes remain needed by the two new nodes; none is pruned from the transitive geometric
proof route. In particular all the original steps' 22 dependencies remain there.

The following old direct `proof_deps` are no longer direct dependencies of the assembly;
each remains in both split-off geometric nodes, so this relocates rather than globally prunes
the work:

- `lem-weil-pbc-inverse-image-composition`
- `def-weil-pbc-abelian-etale-sheaves`
- `def-weil-pbc-category-colimit`
- `def-weil-pbc-cohomology-pullback`
- `lem-weil-pbc-cohomology-pullback-functorial`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-colimit-initial-full-subcategory`
- `lem-weil-pbc-affine-etale-site-topos`
- `lem-weil-pbc-affine-etale-site-colimit`
- `lem-weil-pbc-colimit-of-sites`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-cohomology-colimit-of-sites`
- `def-weil-pbc-scheme-conventions`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-mayer-vietoris`
- `lem-weil-pbc-etale-mayer-vietoris-pullback`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `lem-weil-pbc-five-lemma`
- `lem-weil-pbc-separated-affine-open-intersection`

Also removed the redundant imports
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. The remaining public import of
TopologicalInvariance supplies the statement vocabulary. There is no additional globally
unneeded node identified by this delivery.

## Where the brief, the DAG or earlier work was wrong

The brief correctly treats the remaining site declarations as available premises. Their
cohomology-over-an-object theorem does not immediately match this global qcqs statement:
one must transport inverse images, units, cohomology and comparison maps, then glue over finite
affine covers. The two new nodes package the existence and relation parts of this gap.

Mathlib searches with LeanFinder return structure-sheaf section descent/vanishing, which do not
prove arbitrary abelian etale cohomology continuity. Loogle finds the generic
`Concrete.colimit_exists_rep`, used after choosing the group colimit. Mathlib grep finds no
scheme-cohomology continuity theorem. LeanSearch returned Internal Server Error; that failure
is recorded as unavailable, not as evidence of absence. The source repository's fixed-scheme
filtered-coefficient results and the project's fixed-base and derived variants do not supply
an independent proof of this varying-scheme, varying-sheaf statement.

The literature checkout is absent on this machine. The source pages for Stacks 09YQ, 09YP,
0EYL and 0A50 were read directly online. The agent-written finite-affine-cover reduction in
the parent node is retained rather than attributed to an explicit Stacks proof.

Tool issues resolved on this retry: the missing compiled dependency became available through
the normal refresh. An initial dry run then encountered an SSH connection closure at fetch;
the next dry run printed OK. No delivery was pushed.

## New nodes

`lem-weil-pbc-etale-limit-cohomology-class-descent` states that every class of the specified
limit cocone is the image of a class at some stage. It retains the original cofinal affine-site
argument and finite-cover gluing, then uses surjectivity and a stage representative.
Module: `lean/Sheaf/AlgebraicGeometry/EtaleLimitCohomologyClassDescent.lean`.

`lem-weil-pbc-etale-limit-cohomology-eventual-vanishing` states that a stage class mapping to
zero is killed by one later transition. It retains the same source-supported geometric route,
then uses injectivity and finite-stage equality in the filtered group colimit.
Module: `lean/Sheaf/AlgebraicGeometry/EtaleLimitCohomologyEventualVanishing.lean`.

Neither node cites the assigned theorem as a premise, so the reduction has no dependency cycle.
Zero coefficients, empty schemes, degree zero and singleton indices are discussed in their
docstrings. No statement changes or change records are needed.


## Second reading by Y2

1. **Visible declarations — pass.** Read the full assigned module against the repository with
   `diff -u`. Both public theorem signatures and the private constant-pullback helper signature
   are byte for byte unchanged, as are the helper and ring-specialization proof bodies and all
   original docstrings. The only existing Lean changes are private proof imports and the body
   of `nonempty_isColimit_etale_cohomology_of_isLimit`. The parent node changes only `proof`,
   `proof_deps` and `proof_origin`; no statement, definition, target or unit record changes.
   There are no change records because no existing interface changes.

2. **Proof and axioms — pass as a reduction, with two open claims.** Compiled all three
   delivered files locally in import order. Read the assembly: a chosen group-colimit element
   has a stage representative; `colimit.ι_desc` turns its zero image into the zero-detection
   hypothesis; `colimit.w_apply` kills the representative after a transition. Class descent
   supplies surjectivity. `ConcreteCategory.isIso_iff_bijective` and `ofPointIso` then prove
   precisely `Nonempty (IsColimit B)`. The universe-shrinking preservation instance covers
   index universe u and group universe u+1. A scratch copy of the entire assigned module with
   four explicit `#print axioms` commands compiled: both original public theorems and both
   split statements use only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.
   Scanning the delivered Lean finds exactly the two reported whole-theorem `:= by sorry`
   proofs; no forbidden declaration, hollow definition or partial-proof sorry appears.
   Thus one original direct sorry is closed; the geometric continuity proof remains open.

3. **Split statements — pass.** Independently read [09YQ](https://stacks.math.columbia.edu/tag/09YQ),
   [09YP](https://stacks.math.columbia.edu/tag/09YP),
   [0EYL](https://stacks.math.columbia.edu/tag/0EYL) and
   [0A50](https://stacks.math.columbia.edu/tag/0A50). Both statements retain nonempty directed
   preorder I, a genuine scheme limit, qcqs stages, affine transitions, arbitrary abelian
   sheaves, identity and composition laws, the actual pullback-sheaf colimit, and the complete
   conjugation equations for its cohomology diagram and canonical cocone. Their conclusions
   are respectively existence of representatives and later annihilation of a kernel class.
   Each is only a part of the required colimit argument; neither states the universal property
   or assumes the parent theorem. The docstrings supply the affine-site transport, canonical
   unit compatibility, finite-cover gluing, two inductions, and the final element argument.
   For a singleton index the legs are the canonical cohomology isomorphisms; for degree zero
   these are descent and equality of sections; for zero coefficients and empty schemes the
   only class is zero, represented at any stage and killed by the identity. For x=0 the
   eventual-vanishing conclusion uses j=i and f=identity. No extra torsion or separation
   assumption is introduced. Neither geometric statement has a short closure from the
   existing declarations: transport across the affine-site equivalence and the finite-cover
   gluing are still required.

   Repeated searches with different terms through `msearch.py` (LeanFinder, fully qualified
   Loogle, grep) found only structure-sheaf section descent and generic filtered-colimit
   witnesses. Read local varying-complex and derived-limit imports: their class-descent route
   imports this assigned theorem, so using them would create a cycle. The now-proved upstream
   `Scheme.H_map_isColimit_of_isFiltered` treats a fixed scheme and does not prove either
   varying-scheme assertion. The sites class-descent/vanishing results underlie
   `cohomology_colimit_of_sites`, retained in the geometric route, but do not provide the
   scheme/site comparison or qcqs gluing. Added the independent search records to both nodes.

4. **Shortest route, imports, pruning and unit — pass after repairs.** The assembly uses the
   generic group-colimit API directly. Removed the two new modules' redundant public import
   of `Mathlib.AlgebraicGeometry.AffineTransitionLimit`; a scratch version with only their
   remaining public import, TopologicalInvariance, compiles, so it supplies all statement
   vocabulary. Removed the assembly's three redundant added proof imports, Filtered.Final,
   Grp.FilteredColimits and ConcreteCategory.EpiMono; the full scratch assembly still compiles
   using the existing public imports and the two claims. Kept the original geometric proof
   imports of the split modules as the plan for their unresolved proofs. Expanded
   `## No longer needed` to list all 22 former direct parent dependencies relocated to the
   split nodes. No node is globally pruned. Inspected `dag/units/sk-thm-p1.json`: its statement
   and all four realized step lists are unchanged, and the split retains the route below them.

5. **DAG agreement — pass after repairs.** The parent has the two geometric premises, the
   exact injection/surjection assembly, and the unchanged constant-pullback/ring step. Its
   `proof_deps` equal the union of its step uses. Both new nodes have the required source,
   creation, blueprint ancestry, chapter, unit, searches and verbatim Lean signature records;
   their dependencies retain the original geometric steps and exclude the parent theorem and
   each other. Added `def-weil-pbc-category-colimit` to their `stmt_deps`, since their statements
   explicitly cite it for the limit and colimit data. Corrected the cofinal-tail explanation:
   to extend a cone at i one chooses j >= i,i0, and directedness makes the composite independent
   of j. Added the missing n=0 empty-scheme base case to both nodes' two cover inductions,
   matching their docstrings. Distinguished existence and zero detection in their origins.
   These are proof-plan repairs, not changes to the two Lean statements.

Second reading changed only redundant imports, new-node dependency/proof/search metadata, and
report completeness. The Lean proof assembly and every declaration statement remain intact.
