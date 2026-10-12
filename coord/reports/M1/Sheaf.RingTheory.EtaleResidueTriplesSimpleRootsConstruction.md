## What changed

Proved `AlgebraicGeometry.Scheme.etaleResidueTriples_simple_root_stage` in
`Sheaf.RingTheory.EtaleResidueTriplesSimpleRootsConstruction`, preserving its statement.
Added five proved private helpers for growth of stage images, joint surjectivity,
monic coefficient descent, the kernel of a triple's field map, and construction of
an étale extension carrying the root. No definition or public statement changed.

Added proof-only imports of `Sheaf.RingTheory.EtaleResidueTriplesColimit`,
`Mathlib.Algebra.Polynomial.Lifts`, and `Mathlib.RingTheory.Etale.StandardEtale`.
The second reading removed the redundant explicit filtered-basic and ideal-residue-field
imports; the former is only needed for the proof and is available through the proof-only
colimit import, and the latter is already available through the statement imports. Updated the item's existing DAG
node to record the actual construction and its existing dependencies.

Read Stacks algebra.tex, lemma-henselization (04GN), final proof paragraph,
and lemma-strict-henselization (04GP). The former descends a monic polynomial and
adjoins a root on an étale neighborhood; the latter replaces pairs by residue
triples. The proof implements this route using the standard étale algebra localized
at the derivative, with the distinguished prime defined as the evaluation kernel.
The unit sk-thm-p1 is preserved; this item is not one of its realized statement/steps.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.etaleResidueTriples_simple_root_stage`, the module's
only original sorry, and all five private helpers. No sorry remains in this module,
and this delivery adds no sorry or new node.

The proof uses the filteredness clause of the existing sorry theorem
`AlgebraicGeometry.Scheme.etaleResidueTriples_filtered_colimit`
(node `lem-weil-pbc-etale-triples-filtered-colimit`). Thus this is a complete stage-3
proof from an existing open dependency, rather than an axiom-free closure of the
whole branch. All coefficient descent and root-extension calculations are proved here.

The zero ring cannot occur as c.pt because ψ is a unital map to a field. The descent
helper itself does not require nontriviality. A constant monic polynomial has no root
in K, so its root hypotheses are contradictory; no degree assumption is added.
The extension helper works for arbitrary primes, fields and compatible residue maps;
separability is used only through the existing filteredness theorem.

## No longer needed

Removed the original `public import Mathlib.CategoryTheory.Filtered.Basic`: it is needed
only for the proof and is already available through the proof-only colimit import.
Also removed the added `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` import as redundant.
No original node or module was pruned; the original construction node had no proof dependencies. No localization-property or surjectivity theorem for this
colimit is needed: coefficient descent and the prescribed-root construction are proved
locally. A trial import `Mathlib.Algebra.Ring.Subring.Basic` was removed because the
remaining imports already expose the Subring API.

## Where the brief, the DAG or earlier work was wrong

The original node had one non-elementary prose step and an empty proof_deps list.
The delivery supplies its complete Lean construction and records the existing
filteredness, standard-étale, and affine-residue-field dependencies.

The ready-made finite-stage coefficient lemma
`CommRingCat.exists_forall_mem_range_ι_app` requires preservation of this colimit by
the forgetful functor. The usual instance does not immediately apply to this category's
object universe. The proved subring/universal-property argument avoids that issue
without altering universes or adding a hypothesis. No statement dispute was found.

Searches were run through msearch.py using LeanFinder, Loogle, and grep; the results
included `Polynomial.lifts_and_natDegree_eq_and_monic` and the standard étale API.
The source library's finite-presentation and prescribed-residue-field proofs were
also read. Local lcompile validation succeeds without warnings; final delivery
validation is the required deliver3.py --no-push dry run.


## Second reading by M1

1. Compared the sole delivered module with the repository version and mechanically
   checked the full existing theorem signature through `:= by`: byte for byte unchanged.
   The existing docstring, definitions and public theorem statement are unchanged.
   The only existing-node changes are `proof`, `proof_deps`, and `proof_origin`.
   Verdict: pass; no statement change. The public-import removal has the change record
   `coord/changes/EtaleResidueTriplesSimpleRootsConstruction-imports.md`.
2. Independently compiled the module and a scratch copy printing axioms for all six
   declarations. All five private helpers use only `propext`, `Classical.choice`,
   and `Quot.sound`. The main theorem additionally uses `sorryAx` from the existing
   filtered-colimit dependency. No sorry is present in this delivery, no definition
   was added, and no forbidden axiom or implementation escape is present. Verdict: pass.
3. No statement is split off, and there are no new nodes. Read every helper proof:
   the finite union of images is a subring by common successors; its colimit retraction
   proves surjectivity; finite coefficient descent preserves monicity; field embeddings
   identify the kernel; evaluation at a simple root gives a nonzero standard étale
   algebra and a compatible residue triple. Checked constant monic polynomials (root
   premise impossible), zero colimit ring (unital field map impossible), and arbitrary
   primes rather than only maximal primes. Verdict: pass.
4. Searched the library by colimit surjectivity, coefficient lifting, and standard étale
   evaluation, and independently ran msearch grep for filtered colimit monic polynomial
   lifts. The ready-made underlying-type colimit routes have universe/preservation
   requirements that this direct subring proof avoids. The newer narrower
   `etaleResidueTriples_filtered_part` would suffice, but its compiled module is absent
   from the last green local library; retained the available filtered-colimit clause.
   Removed two redundant imports, including the proof-only filtered API that had been
   publicly imported. All remaining imports serve statements or the written proof.
   The old node had no proof dependencies to prune. Read sk-thm-p1's `realized` fields:
   this item is below its realized steps, and the standard étale route is preserved.
   Verdict: pass.
5. Read the original and delivered DAG node, the three dependency records, their Lean
   declarations or Mathlib matches, and the unit record. Each proof step matches the
   code, and the union of its uses is exactly `proof_deps`. No new-node obligations
   arise. Verdict: pass.

Changed only import cleanup, its required change record, and this report. No mathematical repair was necessary.
Local compilation and explicit axiom printing succeed without warnings. The remaining
`sorryAx` is reported above and is not an axiom-free closure of the branch.

Change record: `coord/changes/EtaleResidueTriplesSimpleRootsConstruction-imports.md`.
