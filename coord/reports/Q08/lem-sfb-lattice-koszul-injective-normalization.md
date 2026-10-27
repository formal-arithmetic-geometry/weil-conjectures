# Stage-1 worker report: lem-sfb-lattice-koszul-injective-normalization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-lattice-koszul-injective-normalization.json`: statement, split; not a Mathlib match. Seven explicit steps, all under 1200 characters, using existing nodes only.
- `citations.json`: 22 quotations, one for every step/node citation, copied verbatim from the statements read.
- No new nodes or Mathlib leaves. The statement, original searches, source, creation metadata and blueprint via chain are retained. The current searches are appended, with their actual queries and logged answers.

## Attachments

None. Searches in `lean/WeilConjectures/` by the blueprint tag, Koszul, lattice and invariants found no declaration stating this item. Algebraic Koszul results for regular sequences and derived tensor signs do not state a normalized invariants comparison for condensed equivariant modules.

## WANTED

None needed for this split. The blueprint paragraph gives the open-direct-image route, not the internal lattice calculation; the proof is explicitly agent-written, using the existing module comparison and general homological statements. It does not claim that a Stacks tag states the entire condensed comparison.

## Findings and changes

The imported node had no proof. Its statement is retained without correction. In particular this concerns ordinary derived categories, condensed internal R-modules, and bounded-below complexes of equivariant injectives; no discrete-coefficient or sectionwise exactness substitution is made. A monomorphism into a bounded-below complex forces its source to vanish in the same sufficiently negative degrees, so the quantifier over monomorphic resolutions is compatible with the total functor's D+ domain.

The essential simplifications are reuse of `lem-sc-finite-strip-row-augmentation` and of the already normalized module theorem, rather than new acyclicity or comparison nodes. The row criterion uses upper bound **r+1** for Koszul degrees 0 through r. Naturality is proved for all derived morphisms via K-injective Hom bijectivity, not just for module maps. The computation unit is kept explicitly in c_s; it prevents accidentally identifying values of the derived functor by an arbitrary isomorphism.

The ancestor command printed `None`. This is the inherited null ancestor of the nonimported lattice expansion. Searches of the whole blueprint for Koszul, lattice, derived invariants, injective and finite strip found no blueprint node with the item's full statement. Its existing exact source place and via chain are retained and `same_as` is empty.

## Generic tools outside the unit

These are recorded in `split_report.tool_uses`, for the maintainer to judge and copy into the accepted tool list. They implement general homological operations and preserve the blueprint's open-direct-image route.

- `lem-sc-finite-strip-row-augmentation`: a general row-to-total criterion, not supplied by this unit's condensed-group calculations.
- `lem-weil-pbc-kinjective-hom-derived`: a general localization Hom bijection (already a Mathlib leaf).
- `lem-weil-pbc-right-adjoint-preserves-kinjective`: the general exact-adjoint criterion, used to verify the next tool's hypothesis.
- `lem-weil-pbc-kinjective-fiber-triangle-comparison`: only the first clause, the fixed computation-unit shift formula. The specialized fibre calculation is not used.
- `lem-weil-pbc-complex-ses-triangle`: the canonical exact-sequence boundary in an ordinary derived category.

## Not duplicates

No new nodes were created. The module Koszul theorem is reused; its assertion about modules is not mistaken for the current assertion about bounded-below complexes and their triangulated normalization. The finite-strip row-augmentation theorem is reused with its actual arbitrary-abelian-category statement, not a new condensed special case. The shift theorem's first clause is reused with its actual extra hypothesis that Gamma preserves K-injectives, verified by exact trivial inflation.

## Review by Q08

I read the current blueprint file `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, particularly paragraph (3); the chapter and unit records; and all statements used in the seven steps. The blueprint establishes the intended ordinary-open-direct-image route but does not provide this structural computation. I read Stacks `homology.tex`, label `lemma-double-complex-gives-resolution` (0133), including its second-variable variant, and `derived.tex`, labels `lemma-injective-acyclic` (05TH), `lemma-K-injective` (070I), `lemma-K-injective-defined` (070Y), `lemma-enough-K-injectives-implies` (070K), and `lemma-adjoint-preserve-K-injectives` (08BJ). I also read the source of the project's right-derived triangulation (`lean/WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean`), whose inverse-equivalence comparison is explicitly constructed from the computation unit. This supports, but does not replace, the exact unit-normalized shift statement cited in step 5.

Step 1 uses the injective infrastructure's actual statement that the computation unit is invertible on bounded-below injectives, and the lattice module theorem's actual isomorphism and invariant-inclusion normalization. Applying them to I[0] shows that the actual inclusion, not merely some map between the objects, is a quasi-isomorphism. Cohomology factors through Q by the abstract derived-category definition, so an isomorphism after Q gives a quasi-isomorphism. I checked that the module theorem has no dependency on this item: no circular invocation of the comparison being proved occurs.

Step 2 now cites the normalized action infrastructure directly and gives the augmentation as a real chain map. Equivariance makes the Koszul differential vanish on invariant sections after every profinite base change. The cited action infrastructure defines these invariants with their inclusion, and the total-triangles statement supplies the differential and finite total. The finite-strip theorem explicitly has no vertical boundedness, injectivity or sheaf restriction, so it applies to the internal module category. Its upper strip index is exclusive, hence I used r+1. Its row augmentation is the map of step 1 and its degree-zero component is exactly the required inclusion.

Step 3 uses the total-triangles statement for preservation of quasi-isomorphisms and the infrastructure for invertibility of eta_J. The cited derived-functor definition states the canonical computation isomorphism, not just existence of a derived value. Writing c_s makes the statement's model identification precise without changing its formula.

Step 4 uses the exact Hom bijection stated in `lem-weil-pbc-kinjective-hom-derived`, on targets known to be K-injective from the infrastructure. This yields a chain-map representative for every derived morphism between resolutions, uniquely up to homotopy. The derived-unit definition supplies unit naturality; the total-triangles statement supplies the signed homotopy. The displayed naturality equation is obtained by substitution in the actual strict augmentation square. Specializing to the identity derived morphism compares two resolutions and proves independence. No assertion about lifting a derived morphism strictly under a noninjective source is assumed.

Step 5 checks an extra hypothesis that is easy to miss: the cited fixed-unit shift theorem assumes that the additive functor preserves K-injectives. The exact-adjoint theorem applies since trivial action is exact and is left adjoint to Gamma by the infrastructure. The same infrastructure at the trivial group gives K-injective resolutions in the nonequivariant module category as well. Only the first shift clause of the fibre theorem is used; it explicitly retains the fixed canonical shift and states sigma eta_{J[1]} = eta_J[1]. Iteration and inversion give all integer shifts. The Koszul shift multiplies degree a by (-1)^(an), which is 1 on the augmentation's a=0 summand. This proves the stated shift square on injectives, and on other objects by resolution naturality. There is no hidden comparison between two unspecified triangulated structures.

Step 6 takes triangulatedness of the two functors from the infrastructure and total-triangles statements. Naturality on the last arrow and the already checked shift square give the last-arrow equality, so no general uniqueness of connecting morphisms is invoked. The canonical exact-sequence triangle is provided by `lem-weil-pbc-complex-ses-triangle`, and the total-triangles statement explicitly identifies its image with the boundary from the termwise exact Koszul sequence. The boundary convention remains the cone's negative projection. In particular changing the comparison by a sign would not pass this calculation.

Step 7 is an explicit cancellation of the two augmentation maps, followed by computation-unit naturality. It establishes the canonical module invariant-inclusion normalization simultaneously, rather than making independent choices on each module. At r=0, the identity functor calculation cancels Q(s) with its inverse. Applying naturality to s proves the final resolution equation.

I tested the empty lattice (r=0), the zero module, the zero coefficient ring, and r=1, where K is [P --(T-1)--> P]. In the r=1 shifted complex the degree-one summand changes sign and the invariant degree-zero inclusion does not. For a noninjective module with trivial lattice action there can be positive Koszul cohomology; the acyclicity step uses injectivity only at the rows J^b and does not assert vanishing for arbitrary modules. The argument uses internal exactness, never exactness of evaluation on arbitrary profinite test objects. All quoted dependency statements were opened, their hypotheses matched, and their transitive dependencies checked for cycles through the item. All non-elementary steps have cited nodes; the last elementary step is a few explicit unit/augmentation equalities. There are no steps over 2000 characters and no new statements requiring a separate small-case test.

The Mathlib searches in searches.jsonl were read. The first semantic search returned t-structure bounds, not a Koszul comparison. Loogle returned generic right-derived natural transformations and comparisons, whose source shows a universal construction but no lattice complex. LeanSearch returned ordinary injective resolutions. The second semantic phrasing returned generic rightDerived, mapDerivedCategory and Ext exact-functor maps. None states this item or specializes to all of its clauses in one line. Existing recorded searches are retained as historical evidence; the appended searches are exactly those run by Q08. No search is fabricated and no unavailable service is recorded as an absence result.

## Unfinished work

None in the one-level split. No Lean was written and no compiler, Lake or build was invoked. The new DAG proof depends on the existing unsplit structural tools as allowed at stage 1; it does not certify that all dependencies have already been proved in Lean.

## Repair of the promotion return, 2026-10-23

The return entry names the reviewed head `0213bf094c1` and reports a side-project completion that had not reached the live DAG. I retained the delivered proof, report, citations and all recorded searches. The required initial dry run passed (`72bfa2b7a17`), before these repairs. The delivery command constructs its commit on the current fetched `origin/sheaf-dag` and preserves maintainer-owned fields; no manual git operation or live-DAG edit is needed or performed.

I compared the sandbox item with the current repository item: the statement, statement dependencies, source, creation metadata, chapter/unit and blueprint chain agree. The repository item remains unsplit with no proof, so there is still work to promote. The seven-step proof and logged searches are the retained delivery's work, not a replacement statement. I also read the current return entry and queue row, which still lists this item for stage 1.

For the dependency comparison I reopened all 15 distinct statement/proof dependencies. The saved citations contain the full previous statements of all 11 proof dependencies, and all 22 saved quotes agree verbatim with the current statements. Thus none of the previously cited mathematical interfaces changed. The current review records of `lem-sfb-condensed-action-injective-infrastructure`, `lem-sfb-condensed-derived-restriction-calculus`, and `lem-sfb-discrete-lattice-koszul-resolution` describe subsequent proof/review work. I read these records and their current statements: invariants still use all profinite base changes, trivial inflation is exact, the computation unit is invertible on bounded-below injectives, and the module comparison retains its invariant-inclusion normalization. The infrastructure's restriction hypothesis is now explicitly a continuous group homomorphism; this split uses only trivial inflation and the discrete lattice group, so it has no arbitrary-map application to repair. Statement-only tools remain permitted dependencies of this one-level split.

The actual proof repair has two parts. Step 2 now cites `lem-sfb-condensed-action-injective-infrastructure` directly for the invariant inclusion and its naturality; this uses the same precise normalized infrastructure as steps 1 and 5 instead of reaching through the parent restriction calculus. Its citation quote is replaced with that infrastructure's current statement, and `proof_deps` is recomputed. Step 3 now discharges the bounded-below domain condition in the node itself: if J vanishes below N, each component of the monomorphism P to J makes P vanish there too. This verifies that every resolution quantified in the statement is an allowed input of the cited total functor. Neither change alters the statement or the unit route.

I rechecked B--E against the changed steps. No new node is created, no clause is hidden behind a new restatement, the strip bound remains r+1, and no citation cycle passes through the item. Naturality uses the full K-injective Hom bijection, not a module-only lifting assertion. The fixed-unit shift tool's extra preservation hypothesis is discharged by the exact trivial-inflation adjunction. The canonical boundary comparison uses the total-triangles statement's explicit final clause. The rank-zero, rank-one sign, zero-module and zero-ring cases remain as in the signed review above. No step exceeds 2000 characters. I reread Stacks 0133 (including the second-variable variant), 070I, 070Y, 070K and 08BJ at their local labels; the blueprint's paragraph (3) is unchanged and remains only the route source. Searches were not rerun because neither the statement nor the search question changed. No Lean, build tool, repository file or launcher file was changed.
