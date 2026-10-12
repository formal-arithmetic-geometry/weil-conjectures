## What changed

Return C1 repaired: added Mathlib leaf lem-sbc-finitely-generated-abelian-group-structure
for AddCommGroup.equiv_free_prod_directSum_zmod (Basic.lean:119-132), with actual
LeanSearch, LeanFinder, Loogle and grep records. Step 1 of the coefficient reduction
now cites this leaf in uses, and proof_deps includes the same id. No Lean theorem
was duplicated and no Lean file changed in this repair.

Closed the assigned module's sole sorry by combining two independent parts of its existing
proof in words: local vanishing of cyclic abelian higher direct images, and transfer of
that vanishing to constant module coefficients. Added two proof-only Sheaf imports and
two one-statement modules for those remaining parts.

Repaired the pre-existing full-module timeout. Etale.ModuleSheaf names the original module
sheaf category and caches its existing category instances. Inverse image, direct image and
the derived adjunction abbreviate the original operations with these instances fixed.
Public signatures use definitionally equal category/functor expressions. No target statement
or mathematical hypothesis/conclusion changes. The existing boundary homotopy is constructed
once in Etale.singleBoundaryHomotopy; Etale.homotopyOfSingle abbreviates its specialization.
A proved private cycle-boundary helper and explicit cancellation simplify the existing
local-injectivity proof. The long DerivabilityStructureInjectives import becomes proof-only:
its three declarations are used only in proofs here, and no downstream source uses them.
FullyFaithful is imported publicly for the cycle comparison appearing in a public signature.

Change record: coord/changes/cohomology-presheaf-instance-caching.md. It includes the old/new
signatures and definitions and the effects on the two downstream modules using this API.

## Proved and sorry left

AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists is reduced
by a complete Lean proof to the two intermediate statements. No sorry remains in the assigned
source module. All previously proved declarations remain proved.

The delivery leaves exactly these two named theorems with sorry:

- AlgebraicGeometry.Etale.isZero_cyclicHigherDirectImage_of_locally_zero,
  node lem-sbc-cyclic-higher-direct-image-local-vanishing.
- AlgebraicGeometry.Etale.isZero_constantModHigherDirectImage_of_cyclic,
  node lem-sbc-constant-module-higher-direct-image-cyclic-reduction.

The resumed worker reread the reduction, both intermediate statements, their nodes,
the unit record, and the definition-change diff. Fresh full-set compilation succeeds:
the intermediate modules take 3.7 and 2.2 seconds, and the assigned module 20.1 seconds,
with no warnings. The two remaining statements are separate mathematical parts of the
argument, rather than the original statement renamed or its hypotheses repackaged. Earlier complete files repeatedly
exceeded 60 seconds. The instance-sharing repair addresses the expensive definitions,
without splitting the assigned file or changing the compiler/time limit. All unsuccessful
performance experiments remain outside the delivered lean/ directory, in scratchpad.

The unchanged downstream FreeSheaf file exceeds 60 seconds both against the original cached
library and against this delivery; that full-file attempt cannot establish compatibility.
Direct API conversion checks against the new module compile in 4.3 seconds in the
resumed session, without warnings:
the original raw Sheaf-category types accept freeSheaf, freeSheafHomEquiv and its composition
lemma, upperStarFreeSheafIso, higherDirectImagePresheafFunctor, the canonical map,
its local-bijectivity theorem, sectionsMap, and the canonical map's naturality theorem.
The scratch check file imports the rebuilt sandbox module, not the cached original module.

The required deliver3.py Q1 dry run printed OK: the set compiles and passes the preflight
except for the second reading, which the independent second reader supplies. Nothing was
pushed. The resumed worker repeats the dry run after refreshing this report and adding the
explicit definition-node citations required in the three new node statements.

## No longer needed

No nodes or modules are pruned, and no unit statement or unit proof step is bypassed.
All existing imports remain used; DerivabilityStructureInjectives is needed only by proofs
and is no longer publicly exported. The complex and single-sheaf sheafification proofs
remain intact. The new coefficient reduction avoids importing FilteredColimit, which would
create an import cycle; it cites filtered cohomology and abelian sheafification instead.

## Where the brief, the DAG or earlier work was wrong

The second-reading dependency audit found pre-existing DAG cycles outside this delivery:
lem-weil-pbc-sheaf-algebraic-structures-objects points to each of its abelian-component
and ring-component nodes, which each point back. These cycles are present entirely in
the repository before this delivery; none of their files is changed here. Reported for
maintainer repair. The three new nodes do not introduce a back edge to themselves.

The exact-module DAG search returns no node. Its blueprint reference
sbc-lem-higher-direct-image-presheaf records the abelian sheafification statement in
Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf, rather than the extra module
coefficient vanishing theorem that is the only sorry here. This delivery adds a bridge node
for that existing vanishing declaration and two nodes for its independent argument parts.

HigherDirectImage.FilteredColimit cannot be imported here: it imports FreeSheaf, which
imports this item. The recorded injective-module acyclicity lemma uses the smaller-universe
SheafOfModules encoding, so its comparison cannot be applied directly to the ModuleCat
coefficients in Type (u + 1). The second reading found the proved Type (u + 1) cohomology comparison
lem-weil-pbc-etale-module-cohomology-forget and cites it in the coefficient proof plan.
LeanSearch returned HTTP 500; the search is recorded as unavailable, not as no match.

The earlier attempts correctly identified kernel checking as the timeout source but lacked
the shared category/functor instances needed by the entire file. Both the local-injectivity
proof and the derived-adjunction comparison need those instances; optimizing only the first
half of the file still exceeded the limit.

Edge cases checked: e = 0 supplies integral coefficients; d = 0 permits all positive cyclic
orders and also 0 dividing 0, covering free summands. For d = 1 the coefficient module is
zero. Degree zero, empty schemes and covers, and the zero ring require no extra assumptions.

## New nodes

lem-sbc-finitely-generated-abelian-group-structure is the Mathlib leaf for exactly
AddCommGroup.equiv_free_prod_directSum_zmod, Mathlib/GroupTheory/FiniteAbelian/Basic.lean:
119-132. Its finite-index prime-power decomposition is now cited in the coefficient
reduction. Actual searches and the exact Mathlib match are recorded; no new Lean module.

lem-sbc-cyclic-higher-direct-image-local-vanishing records the local sheafification/affine
basis argument for one cyclic abelian coefficient, for any morphism, independently of Λ,d.
Module: lean/Sheaf/AlgebraicGeometry/CyclicHigherDirectImageLocalVanishing.lean.

lem-sbc-constant-module-higher-direct-image-cyclic-reduction records transfer from already
vanishing cyclic higher direct images to constant module coefficients; it has no local
annihilation hypothesis.
Module: lean/Sheaf/AlgebraicGeometry/ConstantModuleHigherDirectImageCyclicReduction.lean.

lem-sbc-constant-module-higher-direct-image-local-vanishing records the existing assigned
module's extra vanishing declaration and its two-step Lean proof. It does not restate or
change the blueprint sheafification node. The technical instance-sharing and homotopy
refactoring introduces no new mathematical proof obligation.

Change record: coord/changes/cohomology-presheaf-instance-caching.md.

## Earlier second reading (a previous round; superseded)

1. Compared the entire assigned module with the repository using diff and the declaration
   parser. No declaration is removed. The vanishing theorem's signature is unchanged,
   including arbitrary Lambda, qcqs h, d and q, all e dividing d, affine etale U, arbitrary
   classes, jointly surjective etale families, and the original cohomologyMap conclusion.
   The 28 deliberately changed API signatures are all listed, old and new, in
   coord/changes/cohomology-presheaf-instance-caching.md. They replace only the raw sheaf
   category and image functors by their definitionally equal named specializations.
   The five cached instances use inferInstanceAs on the original categories, and the
   derived adjunction is the original adjunction. Read both downstream users and reran
   the raw-category API conversion examples against the sandbox build: clean in 4.8 s.
   No target statement or mathematical definition is weakened. Verdict: pass, with the
   declared interface repair requiring the normal CODEX delivery review.

2. Read all three Lean modules. Fresh full-set compilation succeeded in 4.3, 2.5 and
   24.8 s with no warnings. The assigned module has no sorry; each new module has exactly
   its reported named theorem with proof `by sorry`. There is no hollow definition,
   forbidden axiom, unsafe/opaque/extern declaration, or kernel-check bypass. The scratch
   SecondReadingAxioms file prints axioms for all 49 public declarations of the assigned
   file and both split lemmas: the existing proofs, definitions and new cached instances
   use only propext, Classical.choice and Quot.sound. Only the vanishing reduction and
   its two open parts additionally use sorryAx. In particular this is a completed
   reduction of the original obligation, not an axiom-free completed vanishing theorem.
   Verdict: pass for a partial stage-3 delivery.

3. Read the two split signatures, docstrings and nodes and checked their exact roles.
   Local cyclic vanishing is for one e and arbitrary h, and contains no module-coefficient
   assertion. Coefficient transfer starts from already vanishing cyclic direct images,
   not from the original local-annihilation hypothesis. Neither is a renaming of the item.
   Checked Stacks 03Q8, 03Q5 and 03FD and the cited node statements. The affine-basis
   reduction does not need h qcqs; the filtered-colimit argument uses qcqs precisely to
   make Y x_X U qcqs when U is affine. For d=0 the free summands are ZMod 0 and 0 divides
   0; for positive d the cyclic summand order divides d because its generator is killed
   by d. This includes e=1, d=1, q=0, Lambda=0, and the empty scheme. Also tested the
   model Lambda=Z, d=4 (only orders 1,2,4) and Lambda=Z, d=0 (free integral coefficient).
   The existing finite-abelian structure theorem is Mathlib
   AddCommGroup.equiv_free_prod_directSum_zmod, Basic.lean:119-132, with exactly the needed
   finite-index decomposition. Independent LeanFinder queries for local annihilation
   and filtered cyclic coefficient transfer, Loogle for IsZero/rightDerived, and grep in
   Mathlib Sites and both project Lean roots produced ingredients but no replacement
   theorem. The upstream vanishing declaration itself remains sorry. Neither remaining
   mathematical step has a few-minute direct proof from the currently exposed interfaces.
   Verdict: both statements true, strictly separate parts of the argument.

4. The final proof first obtains each cyclic vanishing by specializing H and then applies
   coefficient transfer. Read sk-lem-failure-field.realized and the original abelian
   sheafification node: the delivery changes neither and bypasses no unit step. There
   was no exact-module DAG node with an old proof_deps list to prune. Existing source
   imports are still used; the long injective-representative import is proof-only and
   FullyFaithful is public because singleCyclesHom occurs in a public signature. The
   two split imports are proof-only. Tried removing the new coefficient module's public
   UpperLowerStarCoherence import: rightDerivedLowerStarPlus becomes unavailable, so
   restored it. No import or node is newly pruned. Verdict: pass.

5. Checked each new node's lean.statement against its declaration, all required fields,
   blueprint ancestry and the union of proof-step uses. The bridge node records exactly
   the two calls of the Lean reduction and belongs to the original unit. Corrected the
   source references from 03Q6 (scheme continuity) to 03Q5 (filtered sheaf cohomology),
   and added 03FD for module/abelian comparison. The coefficient proof plan now cites
   the already proved lem-weil-pbc-etale-module-cohomology-forget at Lambda : Type (u+1)
   instead of the smaller-universe SheafOfModules acyclicity interface. Clarified that
   the cyclic plan uses only local representatives from the local-sheafification node,
   not its disputed unrestricted-universe local-injectivity clause; Mathlib's proved
   isLocallySurjective_toSheafify' gives the needed fact at this adequate value universe.
   Added the structure theorem's verified location and the generator divisibility check
   to the coefficient plan. Verdict: pass after these citation and proof-plan repairs.

Second reading changed only the new coefficient lemma's source/proof documentation,
source references and proof-plan annotations/dependencies in the new nodes, and this
report. No existing signature, definition, Lean proof or final import set was changed.
The normal deliver3 dry run and delivery below perform the final compile and axiom gates.

Return C1 citation repair: lem-sbc-finitely-generated-abelian-group-structure now records
the exact Mathlib structure theorem at Basic.lean:119-132. Checked its finite index type,
prime p i, arbitrary natural e i, and free factor (Fin n →₀ ℤ) against the source. The
coefficient reduction step 1 uses and proof_deps now cite that id. Loogle and grep found
the exact declaration; LeanFinder returned related ingredients; LeanSearch was unavailable.
The blueprint search found no matching imported node. This addendum records the requested
citation repair; it does not claim a new independent second reading or change the prior
second reader’s mathematical verdict. No Lean declaration was duplicated.

Preflight formatting repair for C1: the leaf has a direct-application proof step and
omits lean.file because lean.existing is true; mathlib_match retains the source file
and line. Fresh local compilation succeeded for all three modules (7.1, 3.8, 31.2 s).

## Second reading by Q1

Independent second reading of the C1 citation repair and the complete current delivery,
2026-10-12. This section supersedes the earlier round's review for this delivery.

1. Compared the assigned module with the read-only repository using diff and the project's
   declaration parser. No existing declaration is removed. The sole originally open
   vanishing theorem has exactly its original signature. The 28 changed API signatures
   are declared in coord/changes/cohomology-presheaf-instance-caching.md; reading the diff
   shows only the named category/functor specialization and the declared homotopy refactor.
   The category instances are inferred from the original sheaf category, and the derived
   adjunction abbreviates the original adjunction. No hypothesis, conclusion, coefficient
   universe or mathematical definition is weakened. Read the FreeSheaf and FilteredColimit
   users. Fresh scratch API checks against the sandbox's rebuilt module accept the raw
   sheaf-category freeSheaf, freeSheafHomEquiv, upperStarFreeSheafIso, presheaf functor and
   local-bijectivity types; rfl checks confirm the category and image-functor identities.
   They compile cleanly in 3.8 seconds. Verdict: pass with the declared interface change.

2. Read all three modules and the changed proofs. Fresh full-set local compilation is clean
   (4.0, 2.6 and 24.8 seconds). Exactly the two reported public named split theorems have
   sorry, each as its entire proof. No forbidden declaration or hollow definition appears.
   A fresh scratch #print axioms check covers all 49 public declarations of the assigned
   module and both split lemmas, against the sandbox overlay; it compiles cleanly in
   3.9 seconds. Only the vanishing reduction and its two open lemmas additionally use
   sorryAx; all other checked declarations use only propext, Classical.choice, Quot.sound.
   Verdict: pass as a partial reduction, not a completed axiom-free vanishing theorem.

3. Checked both split signatures and complete docstring arguments against their nodes and
   [Stacks 03Q8](https://stacks.math.columbia.edu/tag/03Q8),
   [03Q5](https://stacks.math.columbia.edu/tag/03Q5), and
   [03FD](https://stacks.math.columbia.edu/tag/03FD). Local cyclic vanishing treats one e
   and any h, and coefficient transfer assumes cyclic vanishing rather than local killing.
   They are distinct parts of the argument, not a renamed obligation. Checked e=0 and
   e=1, d=0 and d=1, q=0, the zero ring and the empty scheme. When d=0 the free summands
   are ZMod 0 and 0 divides 0; when d>0 a finite cyclic generator killed by d has order
   dividing d. Quasi-compactness and quasi-separatedness provide the qcqs pullbacks over
   affine objects needed for filtered cohomology. Read Mathlib Basic.lean:119-132: the C1
   leaf correctly cites AddCommGroup.equiv_free_prod_directSum_zmod with finite index,
   prime p, arbitrary exponents and the free factor. Fresh differently worded LeanFinder
   search for locally zero cohomology, Loogle for the structure theorem, Mathlib grep for
   constant colimits/sheafification, and rg in both project roots found ingredients and
   the exact structure theorem, but no replacement for either split lemma. Neither full
   remaining proof can be closed in a few minutes from the available interfaces.
   Verdict: pass; no duplicate theorem was introduced for the Mathlib leaf.

4. The final proof specializes H for each divisor e, obtains cyclic vanishing, and applies
   coefficient transfer. The imported abelian sheafification statement is itself open;
   applying it would still require the cohomology/restriction comparison and affine-cover
   argument, so does not immediately eliminate the local-vanishing split. The coefficient
   route cites the existing filtered-cohomology and module/abelian comparison nodes and
   avoids the FilteredColimit import cycle. The two split imports and injective-representative
   import are proof-only. FullyFaithful supplies singleCyclesHom in a public signature.
   No exact-module old DAG node has a proof_deps list to prune. Read the unit's realized
   record: no unit statement or step is replaced or removed. No further pruning found.
   Verdict: pass; the reported pruning list is none.

5. Checked the four delivered JSON records, Lean signatures, required fields, sources,
   blueprint ancestry and proof-step uses. In each node, proof_deps is exactly the union
   of uses. The bridge records the two calls in the new Lean proof. The C1 repair adds
   the structure-theorem leaf and cites it in coefficient decomposition, without adding
   a Lean declaration. The cyclic and coefficient plans retain their correct independent
   conclusions. Verdict: pass.

This second reading changed report.md and the change record Users table. Lean proofs,
signatures, definitions, imports and node records required no further repair. Scratch axiom/API checks are
outside the delivered lean directory. The required dry run and delivery provide the final
server compile and preflight gates.

Dry-run repair: the refreshed server preflight identified the newly landed downstream user
Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections, absent from the earlier Users table.
Read its whole module and compiled an unchanged scratch copy against the rebuilt sandbox
module: clean in 3.7 seconds. Its freeSheaf-derived-sections signature is definitionally
compatible, and its statement is unchanged. Added it to the change record's Users table;
no downstream adaptation is required. This is the sole substantive repair of this reading.
