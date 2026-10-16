## What changed

`Sheaf.Paper.ContinuousConstructibleIntegralStratum` closes its original hole with the
exact original theorem signature and variable context. It transports the coefficient
rings and local finite presentation, uses ULift to apply the existing local-triviality
result, obtains integral models on finitely many strata, applies the existing ordinary
integral gluing theorem, and transports back.

The new `Sheaf.Paper.ContinuousLisseStratifiedLattices` proves the geometric combination:
obtain a qcqs etale lattice cover, apply the proved etale stratification theorem, pull
the supplied lattice to the resulting finite etale covers, and use finite etale lattice
descent on each stratum. A zero-relation presentation and the identity stratification
make each lisse integral lattice constructible. The private coefficient and pullback
interfaces are explicit constructions from actual functors; no data is selected from
an unproved arbitrary existence theorem.

Two lower lattice obligations are stated in their own modules:
`Sheaf.Paper.ContinuousEtaleLocalLattices` and
`Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent`. Their available stated proof dependencies
are imported privately, as required for remaining holes by stages/2-statements.md §3.7.
These include the existing internal sheaf-module equivalence and continuous coefficient
realizations. Missing legacy attachments are reported below, not recreated.

The assigned module and the new stratification module use proof-only `import all
Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` to reuse the existing private
lfp_comap, free_comap, free_of_iso and free_pullback_comp_iff lemmas. Five duplicate
local helper bodies are deleted, including the now-unneeded local free_of_comap proof.
CondensedFieldLfpLocalTriviality itself is unchanged. This avoids both unnecessary
public helper exports and collisions with other modules' private helper names.

`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` changes only
`condensedPullbackHom` from `abbrev` to ordinary transparent `def`, with identical type,
body and visibility. Its explicit monoid-hom and isomorphism instances are retained.
The stratification proof times out with the original abbreviation and compiles in about
six seconds with the delivered definition. This is a definition performance repair;
no compiler limit is raised and no slow file is split.

All five delivered modules compile through lcompile.py without errors or warnings.
Scratch #print axioms checks cover the assigned theorem, the stratification theorem,
both lower obligations, the reused private helpers and the explicit coefficient transports.
Only propext, Classical.choice, Quot.sound and inherited sorryAx occur. The reused private
helpers and explicit transports have no sorryAx.

Current-source checks examined 22 direct consumers of condensedPullbackHom beyond Basic
and the unchanged local-triviality module. Twenty compile after withdrawing the helper
exposure repair, including unchanged CondensedConstructibleSerre and IntegralConstructibleKernels.
ChangeOfCoefficients, Derived.UpperLowerStar and CondensedOpenClosedRecollement also
compile in this reading (earlier timeout observations below are historical).
Two checks are unavailable against the current compiled snapshot: Colimit.Compatibility
imports the not-yet-built Sheaf.CategoryTheory.CoefficientPushCopowerCriterion, and
CondensedQbarLfpMatrixRefinement imports the not-yet-built
Sheaf.Paper.CondensedQbarFunctionPresentations. No consumer is adapted. The global build remains the full verification.

## Proved and sorry left

Closed one original hole:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_stratum`
  (`lem-weil-pbc-continuous-constructible-integral-stratum`). No sorry remains in the item.

Also proved:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_stratified_lattices`
  (`lem-weil-pbc-continuous-lisse-stratified-lattices`). No sorry remains in its module.

Added two holes, each the entire proof of a named public theorem in its own module:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_etale_lattice`
  (`lem-weil-pbc-continuous-etale-local-lattice`), in ContinuousEtaleLocalLattices.
  It asserts only an etale cover with an integral lisse lattice. Reuse the already proved
  CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence and the general
  continuous coefficient realizations. Still required are the reconstructed-coefficient
  identifications, compatibility with local freeness, scalar extension and pullback,
  application of the existing sectionwise etale-local lattice theorem, and finite affine
  refinement and assembly. The generic sheaf-module equivalence itself need not be rebuilt.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_finiteEtale_lattice`
  (`lem-weil-pbc-lisse-lattice-finite-etale-descent`), in ContinuousFiniteEtaleLatticeDescent.
  It asserts only existence of a lattice downstairs from a specified lattice on a finite
  etale cover. Its remaining proof includes the encoding compatibilities, etale-slice
  comparison, explicit sum-of-sheet-lattices submodule sheaf, local finite freeness using
  continuous matrices and DVR freeness, permutation-invariant gluing, and rationalization.
  The input lattice need not carry a descent datum and need not descend unchanged.

This is a decomposition: one original hole closed and two lower holes added, a declaration
count of minus one before accounting for dependency closures. No positive ledger net or
axiom-free target proof is claimed. The combination and transports are complete Lean;
existing imported obligations, including the local-triviality infrastructure and ordinary
integral gluing, are not closed by this delivery. No new hole is added in a definition.

## No longer needed

The assigned module removes these direct proof imports:

- Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite
- Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
- Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal

Every removed original proof dependency is accounted for:

- lem-weil-pbc-etale-separated-stratified-finite-intermediate is replaced directly by the
  new stratified-lattice helper, which uses the proved lem-weil-pbc-etale-stratified-finite.
  The separated intermediate remains below that theorem.
- lem-weil-pbc-lisse-lattice-etale-local is now below the new etale-local internal interface;
  its module is imported there as part of the remaining proof plan.
- lem-weil-pbc-lisse-lattice-finite-etale-descent is now used by the new stratified-lattice
  helper, with the declared internal-module attachment repair.

The duplicate local restriction and free-transport helper bodies are removed and reused
from their source. The new stratification module also drops its direct
Sheaf.Paper.ProfinitePointPullback import after reusing the source composition helper;
the point-pullback infrastructure remains below that source module.
No whole module is claimed as pruned. The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing finite-etale descent node names the absent
Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent file. The declared attachment repair
states the same mathematics directly for internal modules over the given continuous
coefficients. The mathematical node statement and detailed sum-of-sheets argument remain;
an initial conversion step now records the existing equivalence and coefficient
realizations, and the compatibilities still needed by this attachment.

Two further legacy attachments in that remaining descent plan are absent:
Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives and
Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport. Their missing imports are omitted,
as tools/add_proof_imports.py's no-file case requires. No substitute declarations are
invented. The etale-slice comparison remains explicitly part of the lower obligation.

The earlier report missed the proved internal sheaf-module equivalence and the general
continuous coefficient realization API now present in the shared library. Both are reused
in the lower proof plans; scratch reconstructions are not delivered or counted as progress.
The original local-triviality theorem uses a field in the scheme universe, so the explicit
ULift coefficient isomorphism remains necessary for the small field in the assigned item.

The returned duplicate-statement fault was real. The first exposure repair still repeated
free restriction in the new stratification file and exposed unnecessary finite-presentation
helpers. A direct exposure experiment also reproduced collisions with private helper names
in CondensedConstructibleSerre. This reader removed the duplicate bodies and reused the
original private source lemmas with proof-only import all. The entire source edit and its
change record were withdrawn. No mathematical statement is disputed, and no target changes
meaning.

## New nodes

`lem-weil-pbc-continuous-etale-local-lattice` is the etale-local existence step with a qcqs
cover, sourced to Bhatt--Scholze Proposition 6.8.4(6) and Lemma 6.8.13. Its generic encoding
and coefficient prerequisites are existing nodes, with their specific compatibilities left
inside this lower hole.

`lem-weil-pbc-continuous-lisse-stratified-lattices` is the proved finite-stratification
combination, sourced to the first paragraph of Bhatt--Scholze Lemma 6.8.13. It supplies
models of strata without gluing them. The existing finite-etale descent node is reused.

Change records, all open:

- coord/changes/C4-finite-etale-lattice-attachment.md
- coord/changes/C4-condensed-pullback-hom-definition.md

## Forced adaptations

None. Basic is unclaimed and its declared reducibility repair is permitted by
coord/brief-stage3.md §4. CondensedFieldLfpLocalTriviality is unchanged. No module held by
another group is adapted.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes.** Compared every delivered existing module with
the repository version. The assigned theorem signature and all existing declarations are
byte-for-byte unchanged. The only existing declaration change is the declared
`condensedPullbackHom` `abbrev` to transparent `def` change, with identical body,
signature, and visibility. The three additional Lean files are new node attachments.
**Verdict: pass.**

2. **Proof and axioms.** Compiled all five delivered Lean modules with `lcompile.py --all`.
There are no forbidden commands or `sorry` in definitions. The assigned theorem and the
proved stratified-lattice theorem compile; the only remaining `sorry`s are the two named
public split theorems in their own modules. Scratch `#print axioms` checks show only
`propext`, `Classical.choice`, `Quot.sound`, and the expected imported `sorryAx` from
those split theorems. **Verdict: pass.**

3. **Split statements.** Read both lower statements, their docstrings, and their DAG nodes;
they are strict substeps (etale-local supply and finite-etale descent), are mathematically
true in the stated coefficient interface, and do not restate the assigned theorem. The
finite-etale attachment change records the absent prior Lean file and preserves the node's
mathematical statement. Search results and repository search found no duplicate declarations.
**Verdict: pass.**

4. **Route and pruning.** Checked the proof from the target downward. It uses the existing
local-triviality and gluing results, the new stratified-lattice interface, and the unit's
finite-etale route. Removed imports and the replaced separated-stratification dependency
are recorded above; the unit's `realized` route is unchanged. **Verdict: pass.**

5. **DAG agreement.** Checked each node's `proof`, `proof_deps`, `proof_origin`, Lean
attachment, and split metadata against the declarations and imports actually used. The
new nodes contain their source, proof text, searches, and matching public theorem records.
**Verdict: pass.**

Changed during second reading: corrected the inaccurate import-pruning sentence in this
report, added this review section, and removed only the temporary scratch axiom-check file.


## Earlier second reading (a previous round; superseded)

1. **Visible interfaces: pass.** Read the diff of every delivered existing module.
   The assigned theorem's entire signature and its surrounding ℓ/E variable context
   are byte-identical to the repository. Basic differs in exactly one keyword:
   `noncomputable abbrev condensedPullbackHom` becomes `noncomputable def`, with
   identical type, body and visibility. Its change record declares the reduction
   behavior change and lists downstream users. The other three modules are new.
   No target or existing mathematical definition changes meaning. The revised
   original docstring describes the actual sum-of-sheet-lattices argument.

2. **Lean and axioms: pass, conditional on the listed lower obligations.** Compiled
   all five delivered modules in import order through lcompile.py. The only direct
   sorries are continuousLisse_etale_lattice and continuousLisse_finiteEtale_lattice;
   both are whole proofs of the public named theorems listed above. No forbidden
   declaration or hollow definition occurs. Scratch copies print the axioms of the
   assigned theorem, the stratification theorem and the principal private transport
   helpers. Only propext, Classical.choice, Quot.sound and inherited sorryAx occur.
   In particular scalarTransportIso, liftCoefficientIso, pullbackCoefficientData,
   canonicalPullbackSystem, and the constructibility transports have no sorryAx.
   The pullback structures are explicit constructions from actual functors, not
   arbitrary witnesses selected from an unproved existence theorem. The assigned
   result still depends on the imported local-triviality and gluing obligations as
   well as the two split lattice obligations; this is a decomposition, not a claim
   of an axiom-free completed target proof.

3. **Split statements and search: pass.** Read Bhatt--Scholze arXiv:1309.1198v2,
   Proposition 6.8.4(6) (pp. 58–59) and Lemma 6.8.13 (p. 61), from
   https://arxiv.org/pdf/1309.1198. The first split asserts only etale-local lattice
   existence, with qcqs supplied by a finite affine refinement; it does not descend
   or glue. The second accepts a finite etale surjection and a specified lattice
   upstairs and asserts existence of a possibly different lattice downstairs.
   Its finite sum construction does not require a descent datum on the input M.
   After splitting p, the rationalization embeds each sheet lattice in the same P;
   continuous matrix neighborhoods make their finite sum locally a constant full
   DVR lattice. Permutation invariance supplies the cocycle. Checked the empty
   base, rank zero, degree-one cover, varying ranks, and nonconnected base: the
   conclusions allow each case and do not assume normality or reducedness.
   Finite dimensionality and NormedAlgebra identify the given valuation with the
   canonical p-adic extension; no extra coefficient hypothesis is concealed.
   Read the existing sectionwise etale-local theorem and coefficient-realization
   interfaces. Repeated msearch with the different phrases "finite locally free
   internal sheaf module integral model etale descent p-adic coefficients" and
   "IsLocallyFinitelyPresented, comap", plus grep for integral local systems,
   lattice descent and MonModuleEquivalence. LeanFinder returned unrelated etale
   algebra results; Loogle returned zero hits; grep found the ordinary internal
   algebra equivalence, not the required sheaf-module compatibility theorem.
   Repository searches likewise found no proved duplicate of either split.
   Neither remaining proof is a few-minute completion: the first still needs
   the sheaf-module equivalence compatibilities; the second needs the actual sum
   submodule sheaf and its gluing. No additional hole was introduced in review.

4. **Top-down route and pruning: pass.** Read the proof from the assigned result
   through smallField_finiteFree_cover, continuousLisse_stratified_lattices,
   Scheme.exists_etale_stratified_finite and the separate integral gluing theorem.
   ULift is an explicit ring isomorphism, and preservation of finite presentations
   is proved by transporting their cokernel presentations. The stratification proof
   applies finite etale descent on the cartesian pullbacks and makes the resulting
   lisse models constructible by a zero-relation presentation and identity stratum.
   The three original removed imports and replaced separated-stratification node
   are accounted for above; the old lattice nodes remain below the new interfaces.
   The proper-base-change unit's realized statement and three steps are unchanged.
   Removed two redundant explicit Basic imports. Testing removal of
   ProfinitePointPullback exposed the required NatTrans.IsMonoidal instance, so
   that import was retained. No whole module is claimed as pruned.

5. **DAG correspondence: pass after repairs.** Compared proof/proof_deps and Lean
   records with the actual root reduction and each helper. New-node source,
   created, chapter/unit, blueprint, searches and verbatim Lean attachments are
   present. The existing finite-etale node keeps its mathematical statement and
   detailed proof, replacing its absent Lean attachment through the declared
   change record. Made the new stratified-lattice statement self-contained, without
   changing its mathematical content or Lean signature. Marked the substantial
   module/coefficient comparison in the etale-local node non-elementary, explicitly
   identified it as part of that remaining hole, and cited the existing tensor,
   module, norm-uniqueness and continuous-realization nodes. Added the existing
   etale-open and affine-union citations to the finite-refinement step, and the
   profinite-point-pullback citation to the stratified transport step. Recomputed
   proof_deps as the union of uses and checked that these additions create no cycle.

Changed during this second reading: two redundant imports and one extra blank line
removed; two new-node records clarified and their missing dependencies supplied;
this report corrected and extended. No theorem body, signature, coefficient-map body,
or count of remaining holes changed during review.


Additional validation in this reading: all sixteen modules containing direct uses of
condensedPullbackHom were checked individually. Thirteen compiled with the changed
definition. The three timeout cases and the mixed baseline result for the recollement
consumer are recorded in What changed above, rather than being reported as successful
consumer checks. The original Basic plus the complete delivered stratification proof
was also compiled in a separate sandbox: it timed out, while the changed-definition
version compiled. A local transparency alternative and a private map wrapper did not
remove that timeout; neither experiment is delivered. The definition's term and meaning
are unchanged, and its change record remains the declared performance repair.
The required deliver3.py --no-push run printed OK (review class CODEX). It checked
all delivered files, their axiom probes and the delivery records; it did not push.


## Second reading by C4

1. **Visible interfaces: pass after repair.** Compared each existing delivered module with
   the repository. The assigned theorem signature and surrounding variable context are
   byte-identical. Basic has exactly the declared abbrev-to-def keyword change, with
   identical body and type. All other modules are new. Reused the existing private
   restriction helpers with proof-only import all and withdrew the unnecessary source
   modification and helper-exposure record. The three new modules have the required
   module header and public section; proof imports are private, including import all.

2. **Proofs and axioms: pass, conditional on the listed lower obligations.** All five
   delivered files compile locally. There are exactly two direct sorries, the two named
   public split theorems listed above, each with its source, proof docstring and node.
   No forbidden declaration or sorry in a definition occurs. Scratch #print axioms
   checks give only standard axioms plus inherited sorryAx in the incomplete reduction;
   the reused private helpers and the explicit coefficient/pullback constructions use only
   standard axioms. Their data is constructed from actual functors. No arbitrary object
   is chosen from an unproved mere existence theorem.

3. **Split statements and search: pass.** Read Proposition 6.8.4(6) and the first paragraph
   of Lemma 6.8.13 in the local Bhatt--Scholze paper. Both lower statements are true strict
   substeps of the original reduction. Checked empty bases, rank zero, varying ranks,
   degree-one covers and degrees divisible by ell. The descent construction takes the
   finite sum of the sheet lattices inside the same rational module; continuous matrix
   neighborhoods make that sum locally a fixed full DVR lattice. Permutation invariance
   supplies gluing without a descent datum on the given lattice. Repeated LeanFinder,
   Loogle and grep searches with different wording and searched both Lean roots. The
   search found the generic internal sheaf-module equivalence and coefficient realization
   API, now cited and imported. It found no proved duplicate of either complete lower
   statement. The remaining specific compatibilities, affine assembly and sum/sheaf
   descent are not a few-minute completion; no additional hole was introduced in review.

4. **Top-down route and pruning: pass.** The root uses existing local triviality, the
   proved stratification combination and existing ordinary integral gluing. The latter
   two lower lattice obligations are combined through an actual cartesian pullback proof,
   not a renaming of the original goal. ULift and scalar transport are explicit. Every
   old proof dependency removed directly from the root is listed under No longer needed,
   with its retained lower use. Checked the unit record and searched its removed
   dependencies against all unit realized routes; no unit step is bypassed. Available
   stated dependencies of the two remaining holes are imported privately, with absent
   legacy attachments explicitly reported. No whole-module pruning is claimed.

5. **DAG correspondence: pass after repair.** All four delivered nodes match their Lean
   declarations; lean.statement is verbatim and proof_deps is exactly the union of uses.
   New-node source, creation, blueprint, chapter/unit and search fields are present.
   Updated the etale-local plan to reuse the proved generic equivalence, the stratified
   plan to cite the reused free restriction helper, and the finite-etale attachment's
   initial encoding step. Checked the added dependencies for cycles through the items.
   The existing finite-etale mathematical statement and detailed sum construction are
   retained. No unit realized field or target statement changes.

Changed in this reading: removed five duplicate helper bodies and reused the original
private lemmas through proof-only import all; withdrew the unnecessary helper exports,
source-module edit and associated change record; restored available proof-plan imports
of the remaining holes; added the missing encoding/helper citations and finite-etale
conversion step; regenerated the Basic change-record user table and corrected this report.
The mathematical signatures of the assigned theorem and the two lower obligations, and
the number of direct holes, are unchanged.

Final validation: deliver3.py --no-push printed OK for the final five-module delivery
(review class CODEX). The standalone library-wide normalized-statement comparison found
no new duplicate theorem statements. All delivered signatures and DAG statement records
were checked again after the helper pruning.

The final shortened stratification proof was also checked against the original Basic
abbreviation: it still times out after 60 seconds, confirming the declared definition
performance repair remains necessary after pruning the duplicate helpers.
