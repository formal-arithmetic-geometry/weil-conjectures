## What changed

Repair of the duplicate-statement return: removed the private
AlgebraicGeometry.homObj_zero_target theorem entirely. Its two callers now apply
Mathlib's CategoryTheory.Functor.map_isZero to the internal-Hom functor in its target
variable. A proved private homFunctor_preservesZeroMorphisms helper supplies the local instance
by evaluating postcomposition with zero; there is no replacement zero-target theorem. The cited
AlgebraicGeometry.homObj_isZero_of_target in RHomSupportedQuasiCoherentPseudoPartBound
is private, so importing that module cannot expose it. Reusing the public, more general
Mathlib theorem avoids changing another module's visibility or importing its unrelated
lower-bound proof. All target signatures, imports and hole counts are preserved.
The earlier second reading is retained below as history; the fresh second reading
of this repair is recorded in the final section.


Replaced the only sorry in RHomSupportedQuasiCoherentPseudoPartQCCohomology by a complete
Lean reduction. The proof unpacks the pseudo-coherent local models, restricts the bounded-below
target, chooses a bounded-below K-injective representative, and transfers its quasi-coherent
cohomology through the exact restriction comparison. It explicitly constructs the source's
stupid truncation below m - n - 1. Product universal properties prove the comparison is
invertible in degrees n - 1, n, n + 1, giving the cohomology isomorphism. It applies the new
finite-source lemma, transports through the existing RHom representative and open-restriction
comparisons, and proves the covering condition to glue quasi-coherence.

Added proof-only imports of FiniteFreeHomComplexQCCohomology,
DerivedInternalHomRestrictOpen, BoundedBelowInjectiveResolution and the source library's
Embedding.StupidTrunc. Existing public imports and all existing signatures are unchanged.
The local definition presentation comparisons require the transparency setting used in the
existing PseudoCoherentQCohDegree proof and 800000 heartbeats; wall time stays below 60 seconds.

Read Stacks [0A6H](https://stacks.math.columbia.edu/tag/0A6H) and
[08I5](https://stacks.math.columbia.edu/tag/08I5). The new lemma's argument is the finite-column
Hom calculation. No unit realization is bypassed: sk-thm-picard-duality has empty realized
statement and step lists, and the route still proves the same supported-RHom prerequisite.

## Proved and sorry left

Closed: AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_qc_cohomology
(node new-lem-sc-rhom-supported-qcoherent-pseudo-part-qc-cohomology).
No sorry remains in the item's module or its private helpers.

Added and left: AlgebraicGeometry.finiteFree_homComplex_qc_cohomology
(node lem-sc-finite-free-hom-complex-qc-cohomology), in its own new module.
This is a decomposition, not an unconditional proof: one hole closed and one added.
The finite-source lemma has an actually bounded finite-free complex as source and an arbitrary
target complex with quasi-coherent cohomology. It neither selects pseudo-coherent neighbourhoods
nor proves the truncation comparison or RHom/restriction/gluing identifications.
Existing imported declarations with sorry remain separate existing items; none were duplicated.

## No longer needed

No existing import was removed. No existing proof-dependency node can be globally retired:
the original node had no proof_deps. The affine-module representation and affine equivalence
route described in its former proof is not used. In particular this proof does not need
lem-sc-affine-pseudo-coherent-rhom-qcoherent (module
Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent), its auxiliary affine projective
Hom model, or an affine derived quasi-coherent equivalence. These remain potentially needed
by other items. No claim of global pruning is made.

## Where the brief, the DAG or earlier work was wrong

The previous delivery duplicated the private zero-target helper from the lower-bound
module. The maintainer's import-pruning check correctly rejected the duplicate.
The repaired argument reuses Functor.map_isZero and proves only its zero-morphism
preservation prerequisite via a proved private helper. Five private helper theorems
remain, all proved. The new helper states preservation of arbitrary zero morphisms,
not the duplicated zero-target statement. The inline version compiled once in 56.1 s
but timed out during the dry run; sharing this prerequisite avoids its repeated
elaboration.


The original node packaged an entire local finite-free calculation into one non-elementary
step with no named proof dependencies. The delivered DAG now follows the written Lean proof.
The local models need not be affine: a bounded finite-free source is enough after the explicit
degreewise truncation comparison, so no affine refinement or module representation is required.
The source text is not present at literature/stacks-project/perfect.tex on this machine;
the primary Stacks pages above were read instead. Tag 0GM8, referenced by older finite-free
model lemmas, is a stalk comparison, whereas Tag 08I5 contains the Hom-complex computation.

The ancestor script returns None because prior stage-3 nodes record created.item as a module
name rather than a DAG node id. The new node records the mathematical ancestor
lem-sc-finite-duality by following the existing blueprint.from chain; no existing lineage
fields were changed.

## New nodes

lem-sc-finite-free-hom-complex-qc-cohomology states ordinary Hom-complex quasi-coherence for
an actually bounded finite-free source. Its proof is finite induction through the source's
stupid filtration: the single-term case is finite-free exact Hom and finite sums, and the
induction uses the cohomology exact sequence and quasi-coherent kernel/cokernel/extension
closure. Edge cases checked: empty U, rank zero, an empty source interval (a>b), and arbitrary
unbounded target. These give zero source/Hom or the same finite filtration. No uniform rank,
no noetherianity, no affine hypothesis, and no target boundedness are required. No data is
chosen from an unproved existence statement in a definition. The source truncation used by
the item is constructed directly with stupidTrunc; representative choices occur only in proofs.

Searches ran through msearch.py: LeanFinder returned sheaf cohomology and quasi-coherence
definitions, Loogle did not index the project's homObj, and grep found no matching signature.
LeanSearch returned HTTP 500 and is recorded as unavailable. Whole-blueprint searches for
"finite free Hom", "Hom complex", and "quasi-coherent cohomology" found no equivalent statement;
the one "Hom complex" hit defines a K-injective resolution and does not assert this result.
No change record is required: no existing statement, definition or public visibility changed.

## Earlier second reading (a previous round; superseded)

1. Compared both sandbox modules with the repository: the finite-source module is new;
   the existing module changes its proof, adds five proved private helpers and four plain
   proof imports, and updates its proof docstring and declaration-local options. Extracted
   the sole existing theorem's signature from `theorem` to `:=` and compared it byte for
   byte: identical. No existing definition, target statement, public import or visibility
   changes. No change record is required. Verdict: pass.
2. Compiled both modules in dependency order with lcompile.py: no errors or warnings
   (5.4 seconds and 47.4 seconds). A scratch copy with explicit `#print axioms` for all
   five helpers showed only propext, Classical.choice and Quot.sound; the item's theorem
   additionally uses sorryAx, as expected from its open dependencies. The finite-source
   theorem separately showed the permitted axioms plus sorryAx. Source scanning
   found exactly one sorry, the named public finiteFree_homComplex_qc_cohomology theorem,
   and no forbidden declaration or hollow definition. The retained source is constructed
   by stupidTrunc. Choices of local models and injective representatives occur inside
   proofs, not in data definitions. Verdict: pass as a decomposition, not a completed
   unconditional proof.
3. Read the new finite-source theorem, its node and its full proof docstring. Compared
   the sources at Stacks Tags [0A6H](https://stacks.math.columbia.edu/tag/0A6H) and
   [08I5](https://stacks.math.columbia.edu/tag/08I5): the finite filtration argument
   supplies the stated arbitrary-target finite-source specialization, rather than
   assuming the bounded-target hypothesis of 08I5. For each degree only finitely many
   nonzero source factors remain. Degreewise split source sequences give degreewise
   split Hom sequences, and finite-free Hom gives shifted finite sums of the target.
   The cohomology sequence and kernel/cokernel/extension closure prove the induction.
   Checked U empty, rank zero, a > b, a = b, arbitrary target bounds and varying ranks.
   They respectively give the zero sheaf, zero factors, zero source, the single-column
   case, or the same finite induction. The new lemma omits the original item's derived
   representatives, pseudo-coherent cover, truncation comparison and gluing, so it is
   strictly a part of the argument and does not restate the item. New searches used
   LeanFinder query "perfect source internal Hom arbitrary complex quasi-coherent
   cohomology finite filtration", Loogle query "HomologicalComplex.homology,
   IsQuasicoherent", and grep query "homObjFreeIso|homology.*IsQuasicoherent|
   IsQuasicoherent.*homology". LeanFinder returned eight generic cohomology/K-injective
   hits; Loogle could not index IsQuasicoherent; grep found no matching Mathlib theorem.
   Independently searched lean/Sheaf, the upstream internal-Hom files, and the installed
   Mathlib sheaf and algebraic-geometry sources. Read finiteFreeInternalHomExact,
   QuasicoherentSheafHom, DerivedHomFiniteFreeModel, StrictlyPerfectDerivedInternalHom
   and RHomSupportedQuasiCoherentPerfectPart. None directly proves this ordinary
   Hom-complex statement on the localized site without further comparison arguments.
   No few-minute closure was found. Verdict: true, needed, nonduplicated decomposition.
4. Read the argument from the target downward. The exact restriction comparison
   preserves the given lower bound; the proved bounded-below injective resolution
   produces I. For discarded p < c and q = n-1,n,n+1, c = m-n-1 gives p+q < m,
   so both internal-Hom factors are zero; retained source maps are isomorphisms.
   Product universal properties give the degreewise isomorphisms, and Mathlib's
   ShortComplex homology criterion gives H^n. The new lemma then applies to the
   explicitly bounded finite-free source, and the existing RHom/restriction comparisons
   and of_coversTop finish the proof. Each import supplies signatures or declarations
   used by this route; added proof imports are plain import. The old node had empty
   proof_deps, hence no omitted retired dependency. The report correctly claims no
   global pruning. Read dag/units/sk-thm-picard-duality.json: realized.statement is []
   and realized.steps is [[]]; no realized unit node is bypassed. Verdict: pass.
5. Compared existing node fields: only proof, proof_deps and proof_origin changed.
   Matched its three steps to the written Lean reduction and checked both nodes'
   proof_deps equal the union of their step uses, with every referenced node present.
   The new node includes its source, complete proof, searches, status, created,
   blueprint lineage, chapter/unit and verbatim Lean record. Its statement matches the
   theorem's boundedness, finite-free and quasi-coherent-cohomology hypotheses exactly.
   Verdict: pass after the proof-explanation correction below.

Second reading changed the finite-source docstring and its node's last proof step:
the previous phrase reversed the extension's subobject and quotient. Both now give
0 -> coker(delta^(n-1)) -> H^n(B) -> ker(delta^n) -> 0, with both connecting maps
specified. No theorem statement, Lean proof, import or hole count changed. One original
hole is closed and one simpler hole added, so this is a decomposition with net zero
holes closed and no modules pruned. Scratch axiom probes were removed before delivery.


## Second reading by D2

1. Compared every delivered module with the repository. The finite-source module is new.
   Extracted the existing theorem's entire signature, including binder whitespace, and
   verified byte-for-byte identity. Changes to the existing module are its proof, five
   proved private helpers, four plain proof imports, its proof explanation and local
   elaboration options. Existing public imports and visibility are identical; there are
   no delivered definitions or statement changes and no change record is needed.
   Checked coord/changes for records naming either module or the new declaration; none.
   Verdict: pass.
2. Compiled both modules in dependency order through lcompile.py, with no errors or
   warnings (5.7 and 48.5 seconds). Compiled a scratch copy with explicit #print axioms
   for all five private helpers and both public theorems (47.9 seconds). All helpers,
   including the repaired homFunctor_preservesZeroMorphisms, use only propext,
   Classical.choice and Quot.sound. Both public theorems additionally use sorryAx,
   as expected for their open dependencies. Source scanning found exactly one sorry:
   finiteFree_homComplex_qc_cohomology, the reported named theorem in its own module.
   No forbidden declaration, hollow definition or arbitrary-witness data definition
   was added. The source truncation is the explicit stupidTrunc construction; choices
   of representatives and local models are inside proofs. Removed the scratch copy.
   Verdict: pass as a decomposition, with one hole closed and one added, net zero.
3. Read the finite-source statement, complete proof docstring and new node independently.
   Checked Stacks Tags [0A6H](https://stacks.math.columbia.edu/tag/0A6H) and
   [08I5](https://stacks.math.columbia.edu/tag/08I5). Tag 08I5 has a bounded-below
   hypothesis on its target; the delivered ordinary-Hom statement instead follows
   from finite induction on the bounded source, so does not assume that stronger
   target hypothesis. Degreewise split source sequences give degreewise split Hom
   sequences, single finite-free columns give shifted finite sums of target cohomology,
   and the cohomology exact sequence with quasi-coherent kernel/cokernel/extension
   closure gives the induction. The stated cokernel subobject and kernel quotient
   in the induction step have the correct orientation. Checked empty U, rank zero,
   a > b, a = b, varying finite ranks and arbitrary target bounds: these respectively
   give zero objects, zero factors, zero source, a single column, or the same finite
   induction. This lemma omits the original item's pseudo-coherent cover, lower-bound
   resolution, truncation comparison and derived/restriction/gluing comparisons.
   It is a strictly smaller part of the proof, not a renamed original statement.
   Fresh msearch searches used LeanFinder 'bounded finite projective source sheaf
   internal Hom complex preserves quasicoherent cohomology', Loogle
   'Functor.PreservesZeroMorphisms', and grep
   'homology.*[Qq]uasicoherent|[Qq]uasicoherent.*homology|homComplex.*finite'.
   LeanFinder returned eight generic sheaf/K-projective results; Loogle could not
   index that identifier; grep found no match. Also searched lean/Sheaf and
   lean/WeilConjectures and read HomComplexSingle, FiniteFreeInternalHomExact,
   QuasicoherentSheafHom, DerivedHomFiniteFreeModel, StrictlyPerfectDerivedInternalHom
   and RHomSupportedQuasiCoherentPerfectPart. None directly supplies the localized
   finite-source ordinary Hom cohomology theorem. No few-minute closure was found.
   The existing additive instance in HomComplexSingle is scheme-site specific,
   whereas the repaired helper works on an arbitrary small ringed site; importing
   that module would not directly supply the localized-site instance needed here.
   Verdict: true, needed and not duplicated.
4. Read the proof from the target downward. The resolution is bounded below and
   K-injective; the exact restriction and representative comparisons transfer the
   supplied quasi-coherent cohomology to it. For c = m-n-1, discarded p < c satisfy
   p+q < m for q = n-1,n,n+1; retained truncation components are isomorphisms.
   The repaired helper proves zero-morphism preservation by evaluating postcomposition
   with zero. Mathlib Functor.map_isZero then makes both discarded factors zero.
   The product lifts and inverse identities prove the comparison is invertible;
   the ShortComplex homology criterion gives the required cohomology isomorphism.
   The explicit truncation is bounded and finite free, including rank-zero terms.
   The finite-source lemma and existing derived-Hom/restriction comparisons then
   give the local conclusion, and the point-indexed cover gives the global one.
   All four added imports supply used proof declarations and are plain imports.
   The three public imports of the new module supply its statement's scheme/QC,
   Hom-complex and free-sheaf vocabulary. The old node had empty proof_deps, so
   the report omits no retired dependency and correctly claims no global pruning.
   The unit sk-thm-picard-duality has realized.statement = [] and steps = [[]];
   no realized unit node is bypassed. Verdict: pass.
5. Compared both DAG nodes with the Lean. Only proof, proof_deps and proof_origin
   changed in the existing node. Its steps match the resolution, explicit truncation
   and finite-source/derived/gluing reduction, including the repaired zero-factor
   argument. Verified each node's proof_deps is exactly the union of step uses,
   and every dependency node exists. The new node contains the required source,
   proof, searches, status, created, blueprint lineage, chapter/unit and lean record.
   Its recorded Lean signature is byte-for-byte the new theorem's signature.
   Verdict: pass.

Second reading changed only this report: replaced the stale request for a fresh reading
and appended the independent checks of the repaired delivery. No Lean, node, import,
statement or hole count changed. The original hole is closed by a genuine reduction
with one simpler hole split off; this is a decomposition, not an unconditional proof.
