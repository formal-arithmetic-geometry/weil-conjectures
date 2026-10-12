## What changed

Completed the earlier sandbox proof of
`Sheaf.AlgebraicGeometry.SupportedQCohTriangulated`, preserving all existing signatures,
visibility, definitions and docstrings. Added the missing proof import
`Mathlib.Algebra.Category.Grp.Zero` for `AddCommGrpCat.subsingleton_of_isZero`.

The zero-object proof constructs the empty free module sheaf and uses additive homology
and stalk functors. The middle-term proof combines the existing quasi-coherent kernel,
cokernel and extension theorems with the five-term homology exact sequence. Exactness
of the additive stalk functor proves vanishing outside the arbitrary subset T.
The private additive instance and three private closure helpers are fully proved.
Proof imports also include `Mathlib.Topology.Sheaves.Abelian`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`, and
`Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension`.

Updated the contains-zero and closed-middle node proofs to reflect the Lean argument,
including the latter's three existing quasi-coherent closure dependencies.
The unit has no realized statement or step requiring a different route.

## Proved and sorry left

Closed both original holes:
- `AlgebraicGeometry.supported_qcoh_containsZero`
  (`lem-pc-supported-qcoh-contains-zero`).
- `AlgebraicGeometry.supported_qcoh_closedMiddle`
  (`lem-pc-supported-qcoh-closed-middle`).

No sorry remains in the delivered module; no hole or new module was added.
`AlgebraicGeometry.supported_qcoh_stableShift` and
`AlgebraicGeometry.supported_qcoh_isTriangulated` retain their existing complete proofs.
The axiom checks for all four public closure theorems show only `propext`,
`Classical.choice` and `Quot.sound`, with no `sorryAx`. This checks their proof dependency
closure; unrelated declarations in imported modules are outside this claim.

## No longer needed

None. Both existing public imports support the unchanged statements. Each added proof
import supplies a declaration or exactness instance used by the proof. No original
proof dependency is bypassed; the two original nodes had empty proof_deps.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt used `AddCommGrpCat.subsingleton_of_isZero` without importing
its defining Mathlib module, producing two unknown-constant errors. The import repairs
both. The earlier attempt left no report or node updates; these are now supplied.
The original middle-term node did not record its kernel, cokernel and extension
closure dependencies; its updated proof_deps now names the existing nodes.

The argument uses no closedness, compactness, affine or Noetherian assumption on T or X.
For T empty, stalk exactness still proves vanishing at every point; for T = X, the stalk
condition is vacuous. Zero and shift closure also work for every subset.

Change record: `coord/changes/moduleToSheaf_additive.md` documents the added private
additive instance and the file-local `open scoped ZeroObject` command, which the static
preflight conservatively classifies as interface changes. No existing signature changes.


## Second reading by J2

1. **Existing interface: PASS.** Read the complete diff against the repository module.
   Every existing declaration signature, visibility, definition body and docstring is
   byte-for-byte unchanged. The changes are six plain proof imports, a scoped notation
   command, four private proved helpers, and the two original theorem proofs. The change
   record documents the private instance and scoped command; no downstream signature
   or public definition uses a private helper.
2. **Proof and axioms: PASS.** Compiled the delivered file with `lcompile.py` without
   errors or warnings. Compiled a scratch copy with `#print axioms` for
   `supported_qcoh_containsZero`, `supported_qcoh_closedMiddle`,
   `supported_qcoh_stableShift` and `supported_qcoh_isTriangulated`: each uses exactly
   `propext`, `Classical.choice` and `Quot.sound`. There is no remaining `sorry`, new
   axiom, unsafe declaration, opaque declaration, foreign implementation, or hollow
   definition. The empty free sheaf is constructed directly, rather than chosen from
   an unproved existence statement.
3. **Split statements and small cases: PASS.** No new hole or split-off statement was
   added. Read the three private quasi-coherent closure adapters: they transport the
   existing kernel/cokernel theorems along the universal-property isomorphisms and use
   the existing short-exact extension theorem. Read that theorem and the source
   five-term exact-sequence lemma. Empty T requires all stalks to vanish and full T
   makes that condition vacuous; the same proofs work. Empty schemes and zero terms
   also require no extra hypothesis.
4. **Route and pruning: PASS.** Searched the library for quasi-coherent zero, kernel,
   cokernel, extension and supported triangulated closure results, and read
   `DerivedCategory.HomologyProperty`. Its generic theorem needs the same closure
   adapters and additional property packaging, so offers no shorter reduction here.
   Each proof import supplies a used theorem or instance: additive-group zero objects,
   exact stalks, module-forgetful colimits, five-term exactness, quasi-coherent cokernels,
   and quasi-coherent extensions, respectively. Both public imports support existing
   signatures. Both old proof-dependency lists were empty, so none is omitted from
   `No longer needed`. The unit `sk-thm-picard-duality` has empty realized lists for its
   statement and sole step; this delivery does not change or bypass that route.
5. **Nodes: PASS.** Compared both delivered node files with their repository versions
   and matched their proof steps to the Lean. The zero proof has no non-elementary
   node dependency. The middle proof lists the three existing nodes whose recorded
   declarations are precisely the kernel, cokernel and extension theorems it uses;
   the other steps use Mathlib or the proved generic source exact-sequence lemma.
   `proof_deps` equals the union of step dependencies; `proof_origin` describes the
   actual implementation. No new node needs a new-node record.

Second-reading changes: corrected the axiom-closure wording in this report and added
this review. No Lean repair was needed; both proofs and all imports were retained.
