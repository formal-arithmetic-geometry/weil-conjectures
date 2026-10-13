## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_pairing`, with its existing
signature and public imports preserved, to two separate parts of the original argument:

- `Sheaf.Paper.ModuleCupGodementCosimplicialInput` supplies flasque cosimplicial resolutions,
  quasi-isomorphic augmentations, and a **pointwise cosimplicial** multiplication compatible
  with the degree-zero augmentations. It supplies no tensor cochain map.
- `Sheaf.Paper.ModuleCupCosimplicialAW` supplies the Alexander–Whitney tensor cochain map
  from any pointwise cosimplicial multiplication, with its degree-zero component equality.
  It assumes neither flasqueness nor quasi-isomorphic augmentations.

The combining proof extends the alternating coface complexes by zero, proves their strict
lower bounds with Mathlib's extension instance, applies the Alexander–Whitney lemma, and
passes its equality of morphisms to their action on the tensor of augmented sections.
Transitivity with the cosimplicial input's degree-zero identity gives exactly the requested
section formula. The added imports in the original module are proof imports only.

The new definitions are actual alternating coface complexes, extension identifications,
pointwise tensor functors, and a composite degree-zero morphism. No definition chooses a
witness from a holed existence theorem. Existential witnesses are eliminated only inside the
proof of the existing existential theorem.

## Proved and sorry left

Closed one original hole, by decomposition:
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_pairing`
(node `lem-sc-module-cup-godement-aw`). No sorry remains in its module.

Added two holes, each the whole proof of a public named theorem:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_cosimplicial_input`
  (`lem-sc-module-cup-godement-cosimplicial-input`).
- `AlgebraicGeometry.Scheme.Modules.moduleCup_cosimplicial_aw`
  (`lem-sc-module-cup-cosimplicial-aw`).

This is a decomposition, not a proof without remaining dependencies: one hole closed and
two added, net minus one. In particular the Godement construction remains to be implemented;
the second obligation is the independent front/back coface combinatorics and tensor assembly.
Both docstrings give their construction and proof, including the empty-space and zero-sheaf
cases. No coefficient flatness is assumed or needed.

## No longer needed

No original public import was removed, and no module is claimed pruned. Second reading
removed redundant added imports of `Sheaf.Paper.ModuleCupGodementCosimplicialInput`
and `Mathlib.Algebra.Homology.Embedding.CochainComplex` from the original module.
In the new input module it replaced the homological monoidal import with the cochain
embedding and removed redundant imports of `Mathlib.Algebra.Homology.Embedding.IsSupported`
and `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`; the AW module now imports
the homological monoidal infrastructure directly for its tensor-complex statement. The original proof
edge to `def-sc-module-cup-resolution-data` is replaced by the two actual proof obligations;
that node and its module remain statement infrastructure. The unit's own statement and
steps are unchanged (`sk-prop-av-cube` has no realized step assigned to this node).

## Where the brief, the DAG or earlier work was wrong

The original DAG's one proof dependency is a definition of computing-resolution data;
it does not state either the construction of Godement resolutions or an Alexander–Whitney
map. The plan's mathematical steps therefore needed two new statements.

The original source description locates the Godement construction in the proof of Stacks
20.31.4 (0FKV). The construction is actually in
[Stacks Section 20.30](https://stacks.math.columbia.edu/tag/0FKR), Lemma 20.30.1 (0FKS).
Section 20.31.4 uses its bounded-complex extension to compare cup products.
For the pointwise Godement multiplication and front/back Alexander–Whitney formula, the
new nodes also cite [Banerjee, Tensor Structure on Smooth Motives](https://arxiv.org/abs/1004.1491),
§1.1.4, pp. 15–16. The paper was retrieved and read in the sandbox's `source/` directory.
The adaptation from abelian sheaves to module sheaves uses the additive sheaf tensor
structure; the morphism identity is checked by exactly the same simplex identities.

Importantly, existence of an Alexander–Whitney pairing is not asserted for arbitrary
flasque resolutions: the construction obligation supplies cosimplicial objects and a
natural multiplication, which are the hypotheses of the separate cochain-map lemma.

## New nodes

`lem-sc-module-cup-godement-cosimplicial-input`, in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-godement-cosimplicial-input.json`, records
`Sheaf.Paper.ModuleCupGodementCosimplicialInput`, its four explicit helper definitions, and
the existential cosimplicial resolution theorem. The theorem is strictly the construction
part of the original plan; it has no tensor-complex morphism or Leibniz assertion.

`lem-sc-module-cup-cosimplicial-aw`, in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-cosimplicial-aw.json`, records
`Sheaf.Paper.ModuleCupCosimplicialAW`. It isolates the Alexander–Whitney part of the plan
without resolving sheaves, proving quasi-isomorphisms, or proving flasqueness.

No existing statement or definition changed, so no change record or forced adaptation is
needed. The two elaboration options are scoped to the original theorem. The original node's proof, proof dependencies, and proof origin follow the Lean
combining proof.

Validation: the combining theorem compiled with no errors or warnings. The final dry run
rechecks all three modules and their axiom probes.

The required LeanSearch query was attempted through `msearch.py` and returned an internal
server error; this is recorded as unavailable, with no no-match verdict. LeanFinder, Loogle,
and Mathlib/repository grep searches completed and returned no exact construction or AW map.

## Second reading by M1

1. Compared the complete original module and existing node against the repository.
   PASS: the existing theorem signature is byte for byte unchanged, its public imports
   and docstring are preserved, and only its proof and scoped elaboration options change.
   Existing node changes are confined to `proof`, `proof_deps`, and `proof_origin`.
   There are no forced adaptations or changed existing definitions.
2. Read all three modules and the combining proof. PASS: the original hole is closed
   by constructing the three complexes, using Mathlib's strict support instance, and
   evaluating the AW degree-zero identity on augmented tensor sections. The only
   remaining holes are exactly the two reported public named theorems. The four
   definitions construct complexes, isomorphisms, a functor, and a composite morphism;
   none chooses data from an unproved existence theorem. No forbidden declaration occurs.
   All three cleaned modules compiled without errors or warnings. A scratch copy
   with `#print axioms` checked all seven declarations: the four definitions use
   only `propext`, `Classical.choice`, and `Quot.sound`; the combining theorem and
   two split theorems additionally use `sorryAx`, as reported. The scratch copy
   was removed. Delivery checks also run the declaration axiom probes.
3. Read the two new signatures, their docstrings and nodes, Stacks Section 20.30,
   and Banerjee §1.1.4 (the locally retrieved paper, printed pages 15–16).
   PASS: the Godement obligation is the resolution and natural pointwise multiplication;
   the AW obligation works for arbitrary cosimplicial inputs and has no resolution
   hypotheses. Each is a strict part of the original argument, rather than a renamed
   complete target. In degree (0,0) the two face inclusions are identities; in degree
   (0,1) the middle face terms cancel with the stated tensor differential sign.
   Negative degrees have zero factors; zero coefficients and the empty scheme cause
   no exception. Neither statement requires tensor to preserve quasi-isomorphisms.
   Independent LeanFinder, Loogle, and grep searches using lax monoidal complexes,
   Eilenberg–Zilber, and alternating coface terminology found only infrastructure;
   repository/upstream searches found no reusable complete theorem. Neither open
   construction can be closed in a few minutes using the available APIs.
4. PASS: the proof follows the two mathematical steps of the original plan and
   reports every removed old proof edge (`def-sc-module-cup-resolution-data`).
   That node remains statement infrastructure, so no module is claimed pruned.
   Checked `dag/units/sk-prop-av-cube.json`: its realized statement and step lists
   are empty, and this delivery changes no unit route. Removed the redundant direct
   proof imports of the cosimplicial input and cochain embedding from the original
   module: AW exposes the input, and the preserved monoidal import exposes the embedding.
   In the new input module, replaced the oversized homological monoidal import with
   the cochain embedding actually used by its definitions and removed the redundant
   support and tensor-closed imports. The homological monoidal import now belongs to
   the AW module, whose statement uses the tensor complex.
5. PASS: existing node proof steps match the combining proof; the new nodes have
   source, proof, search, creation, blueprint, chapter/unit, and Lean records.
   Corrected both new `lean.statement` fields to the verbatim multiline signatures.
   Their proof dependencies include the nodes supplying the definitions used in
   their statements and construction descriptions; AW uses the input module's
   concrete definitions, not its resolution existence theorem.

Second-reading changes: redundant import cleanup and verbatim Lean signature metadata;
no mathematical statement, definition body, or combining proof changed. This remains
one original hole closed by decomposition, two holes added, net minus one.
