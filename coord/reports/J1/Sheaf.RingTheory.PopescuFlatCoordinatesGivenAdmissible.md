## What changed

Reduced `Algebra.exists_popescu_flat_coordinates_given_admissible` without changing its
signature or docstring. The proof first applies the existing
`Algebra.exists_popescu_admissible_differential_basis`, retaining the actual enlarged
subalgebra, containment, maximal-ideal contraction equality, compatible residue-field map,
coordinate lifts, basis, and ideal generators. Admissibility supplies essential finite type;
`Algebra.EssFiniteType.comp` supplies it for the residue field.

The new module `Sheaf.RingTheory.PopescuAppendFlatParameters` states the remaining geometric
argument for a fixed field embedded in the residue field, fixed differential coordinates,
and fixed ideal generators. It selects only indices of the supplied generators and states
flatness and ideal equality for the explicit evaluation map on their concatenation. It has
no thickened quotient, admissible subalgebra, enlargement, containment, or spanning conclusion.
It is strictly the parameter-append part of the argument, not a renamed existential conclusion.

The assigned module constructs the polynomial map with `MvPolynomial.aeval` and constructs its
lifts with `Fin.addCases`. Its coordinate equations are proved by finite-index case analysis.
Its spanning assertion is proved using `Module.Basis.span_eq`, `Fin.castAdd`, and span
monotonicity: the first block contains the original differential basis. The main proof is
complete Lean, not an application of a restated whole theorem. No definition, signature,
visibility, or target changed; no adaptations or change records are required.

Both modules compile with the launcher compiler, without warnings. The new theorem has a
complete proof in words and a matching DAG node. The parent node now describes the actual
Lean reduction. The unit statement and its realized steps are unchanged.

## Proved and sorry left

Closed the one local hole:
`Algebra.exists_popescu_flat_coordinates_given_admissible`
(node `lem-weil-pbc-popescu-flat-coordinates-given-admissible`). There are no remaining
`sorry`s in the assigned module.

Added one strictly smaller conditional hole:
`Algebra.exists_popescu_append_flat_parameters`
(node `lem-weil-pbc-popescu-append-flat-parameters`), in its own new module. Its proof is
exactly `:= by sorry`. This is a decomposition: one hole closed and one added, net zero
before closure/import accounting. The existing enlargement theorem
`Algebra.exists_popescu_admissible_differential_basis` is used unchanged and still has its
pre-existing `sorry`; this delivery adds no hole to that module. Neither the new lemma nor
the main theorem is claimed axiom-free independently of those open dependencies.

## No longer needed

Removed the following direct proof imports from the assigned module:

- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`
- `Sheaf.RingTheory.FlatOverRegular`
- `Sheaf.RingTheory.GeometricallyRegularOverFieldFlat`
- `Sheaf.RingTheory.PolynomialOriginRegularLocal`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`

These are retained in the new append module as the dependencies of its documented proof plan.
They are relocated, not mathematical pruning. Their nodes remain needed by the new node.
Likewise the original Nakayama, finite-type Noetherianity, localization Noetherianity,
regular-sequence and regular-local nodes remain needed below the append argument; they are
not direct proof dependencies of the parent anymore. No node or module of the argument has
been established permanently unnecessary, so the delivery claims no pruning beyond removing
these direct imports from the parent. All public statement imports are unchanged.

The only direct Sheaf proof dependencies of the assigned module are the existing enlargement
and the new append theorem. `Mathlib.LinearAlgebra.Basis.Basic` is added as a proof-only import
for `Module.Basis.span_eq`.

The complete list of old `proof_deps` removed from the parent is:

- `def-weil-pbc-flat-ring-map`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-regular-sequence`
- `def-weil-regular-scheme`
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-flat-over-regular`
- `lem-weil-pbc-geometrically-regular-over-field-flat`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-nakayama-local-generators`
- `lem-weil-pbc-polynomial-ring-origin-regular-local`
- `lem-weil-pbc-regular-local-generators-regular-sequence`

Each remains in the new append node's proof dependencies; none is claimed pruned from the
import closure.

## Where the brief, the DAG or earlier work was wrong

The brief's minimum reduction is feasible; the existing enlargement lemma already includes
the maximal-ideal equality, so it need not be proved again in the parent. Its residue-field
essential-finiteness is obtained by explicit composition, rather than `inferInstance` alone
(which did not synthesize the composed instance for the residue-field type synonym).

No statement was found false. The new append statement was checked at `t = 0`, `r = 0`, and
zero-dimensional closed fibre: the empty differential basis is permitted; if `r = 0` then
the localized maximal ideal is zero and the fibre is a field, so `e = 0` works. For a
positive-dimensional fibre, a basis extracted from the images of the given generators has
exactly its regular-local dimension and gives the stated subset of parameters. The field
map is automatically injective; no omitted injectivity hypothesis is required.

The local literature files named by the original node were absent on this machine. Read
Stacks Tags 07FH and 07E6 on the official site and downloaded their actual source files to
this item's scratchpad. The relevant text is `smoothing.tex`, `lemma-solution-modulo`,
lines 2552–2605, and `more-algebra.tex`, `lemma-geometrically-regular-over-field`,
lines 8851–8890. The fibre-flatness detail implicit in the former is made explicit following
the existing parent plan and Tags 00OP, 00NQ, 07DY and 00MP. This elaboration is marked
agent-written in `proof_origin`.

LeanFinder finds standard-smooth statements requiring finite presentation, not this general
Noetherian algebra statement. LeanSearch returned Internal Server Error and is recorded as
unavailable, not as evidence of absence. The grep and blueprint searches found no existing
parameter-append statement. The original parent blueprint field is a legacy string, so
`blueprint_refs.py ancestor` reports None; the new node instead inherits the explicit
nearest-ancestor record from `lem-weil-pbc-popescu-flat-coordinates`, without changing the
parent's non-owned metadata.

## New nodes

`lem-weil-pbc-popescu-append-flat-parameters`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-append-flat-parameters.json`, records
`Algebra.exists_popescu_append_flat_parameters` in
`lean/Sheaf/RingTheory/PopescuAppendFlatParameters.lean`. It isolates the selection of
closed-fibre parameters and the flatness of the resulting explicit polynomial localization.
Its hypotheses are fixed differential data in a finitely generated residue subfield and
fixed generators of the localized prime, and it concludes only parameter selection,
localization compatibility, ideal equality and flatness. Its six proof steps expand the
original parent's steps 2–6 and cite their existing nodes. It adds no admissible-subalgebra
existence assertion and no hollow data construction. The three search kinds and their
actual results are recorded; the blueprint ancestor and unit are inherited as described
above. No change record is necessary because no existing interface changes.

## Second reading by J1

1. **Interfaces — pass.** Read both delivered modules and diffed the existing module
   against the repository. Its complete declaration signature and existing docstring are
   byte-for-byte unchanged; its public imports are unchanged. The only Lean differences
   are proof imports and the replacement proof. No existing definition, visibility,
   statement, or target is changed. No change record or adaptation is required.
2. **Kernel checks and holes — pass as a decomposition.** Independently compiled both
   modules in import order using `lcompile.py --all`. Both compile without warnings.
   Compiled scratch copies with explicit `#print axioms` for both declarations: each
   reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The parent has
   no local hole; the new append theorem is the sole added hole, exactly `:= by sorry`.
   There are no forbidden declarations or hollow definitions. Existential witnesses are
   eliminated inside a theorem proof; no definition chooses data from unproved existence.
   One original local hole is closed and one smaller hole added: net zero, not an
   independently axiom-free proof.
3. **Split statement — pass.** Read the new theorem, its complete docstring argument,
   its node, the existing 07E6, regular-parameter, polynomial-origin, and fibre-flatness
   declarations, and the actual Stacks source excerpts in the scratchpad. Its hypotheses
   give exactly the fixed residue-field differential basis and prime-ideal generators
   needed for the argument. A field algebra map is injective. Localizing geometric
   regularity permits 07E6; extraction of a cotangent basis from the supplied finite
   generating family and Nakayama provide selected parameters. The polynomial closed
   fibre is the origin localization, and 07DY followed by 00MP gives the asserted flatness.
   The extended ideal equality follows from generation modulo the first-coordinate ideal.
   For `t = 0`, the first source is the field k and the same argument applies. For `r = 0`,
   the maximal ideal of the localized target is zero, so the regular closed fibre is a
   field and `e = 0` works. The explicit example Λ=k[z], q=(z), F=k, t=0, ys=(z)
   yields e=1 and the identity local polynomial map. For a field closed fibre one takes
   no added parameters. The new statement omits the admissible enlargement, containment,
   thickened quotient, coordinate lifts into A, and spanning assertion; it is strictly
   the fixed-coordinate geometric part, not a restatement of the item.
   Independent LeanFinder and grep queries used “flat local homomorphism”, “regular
   system of parameters”, and `flat_of_regular|polynomialLocalization|basis_kaehlerDifferential`.
   Mathlib candidates require smoothness/finite presentation, which is not available here.
   Repository searches also found the parameter-quotient lemmas: they assume supplied
   regular parameters and separable residue extension and do not perform this selection
   from a differential basis. The upstream scheme polynomial-presentation theorem proves
   flatness in the other direction. None closes this split lemma in a short proof.
4. **Route and imports — pass, report completed.** Checked the proof from its conclusion
   backwards. It retains every enlargement assertion, constructs φ by explicit `aeval`,
   constructs the A-valued coordinate lifts by `Fin.addCases`, and proves spanning by
   containment of the original basis range. Proof-only imports are plain `import`.
   The five geometric imports in the append module support its remaining proof plan;
   the parent uses just enlargement, append, and the Mathlib basis-span result.
   Read `dag/units/sk-thm-p1.json`: no realized statement or step is bypassed or changed.
   Completed `## No longer needed` with every removed old direct dependency by node id.
   They are relocated below the append node, so actual closure pruning is none.
5. **DAG agreement — pass.** Diffed the parent node: only `proof`, `proof_deps`, and
   `proof_origin` change. Its steps describe precisely the implemented enlargement,
   essential-finiteness composition, parameter append, coordinate equations, and span
   argument. Both nodes' `proof_deps` equal the union of their steps' uses. The new node
   has its matching verbatim Lean signature, source, statement dependencies, complete
   proof plan, agent-written origin, three search records (including the unavailable
   LeanSearch result), split status, creation record, blueprint ancestry, chapter, unit,
   and Lean module/declaration/file record. No existing non-owned node field changes.

Second reading changed only this report: added the exhaustive removed-dependency list and
this review. The Lean proof and node records required no repair. Scratch axiom-check copies
were removed before delivery.
