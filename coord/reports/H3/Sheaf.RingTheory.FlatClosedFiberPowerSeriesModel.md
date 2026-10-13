## What changed

Proved `RingHom.exists_flat_closedFiber_powerSeries_model` with its exact original signature.
Its two new proof imports are `Sheaf.RingTheory.ClosedFiberEquationRemoval` and
`Sheaf.RingTheory.FlatClosedFiberKernelRigidity`; all original public imports remain.

Added three proved helper modules and their DAG nodes:

- `ClosedFiberKernelParameterSelection`: uses the existing regular-local quotient-kernel
  theorem to select a full parameter list in the closed fibre, lifts its kernel segment
  into `ker b` by subtracting elements of the base maximal ideal, and proves generation
  and the required parameter count by taking ideal preimages. No cotangent-space basis
  construction is needed in this glue.
- `ClosedFiberEquationRemoval`: forms the quotient by those actual equations, applies the
  existing field/Cohen power-series parameter-quotient theorem, transports the remaining
  parameters, proves the closed-fibre kernel identity, and transports formal smoothness
  using compatible residue-field and fibre equivalences. The universe-lifting theorem is
  used explicitly because the original target permits independent universes for B and
  the coefficient rings.
- `FlatClosedFiberKernelRigidity`: proves the final generic kernel equality using flatness
  of B over A, Mathlib's linear-kernel intersection theorem, and Nakayama over the
  Noetherian local quotient T/(ker q)T. It does not require flatness of j or completeness.

The original theorem combines the model construction and kernel rigidity. Updated its
DAG proof, proof dependencies and proof origin to match this Lean argument. No existing
statement, definition, visibility, target, or unit realization was changed.

The kernel-rigidity helper publicly imports `Mathlib.RingTheory.LocalRing.Basic`;
`Mathlib.RingTheory.LocalRing.Quotient` is a private proof import.

All four delivered files compile together through `lcompile.py --all`, without warnings.
There are no `sorry`s in any delivered file. The proof uses the project's existing
regular-local-of-formal-smoothness and power-series parameter-quotient results; this is
not a claim that every transitive dependency is already free of `sorry`.

## Proved and sorry left

Closed the original hole:
`RingHom.exists_flat_closedFiber_powerSeries_model`
(node `lem-weil-pbc-flat-closed-fibre-power-series-model`).

Also completely proved the three new declarations:
`RingHom.exists_closedFiber_kernel_parameters`
(node `lem-weil-pbc-closed-fibre-kernel-parameter-selection`),
`RingHom.exists_closedFiber_equation_removal`
(node `lem-weil-pbc-closed-fibre-equation-removal`), and
`RingHom.ker_eq_map_of_flat_of_ker_le_maximal`
(node `lem-weil-pbc-flat-closed-fibre-kernel-rigidity`).

Holes closed: 1 original. Holes added: 0. Holes left in the item's module and the
other delivered modules: none. No unfinished proof was split off.

## No longer needed

No original imports were removed: they are all public imports needed by the unchanged
statement. The unused copied `Mathlib.RingTheory.RingHom.Flat` import was removed from
the new construction helper.

The new route does not directly need these former planned dependencies:

- `lem-weil-pbc-flat-over-regular` / `Sheaf.RingTheory.FlatOverRegular`: flatness of
  R -> T is unnecessary for the final kernel argument, and is not constructed.
- `lem-weil-pbc-flat-module-base-change`: no base-change flatness proof for D is used.
- `lem-weil-pbc-tensor-quotient-base-change`: D is constructed directly as a quotient,
  rather than identified with a tensor product in this proof.
- `lem-weil-pbc-flat-quotient-tensor-injective`: the proof uses Mathlib's already proved
  `LinearMap.ker_inf_smul_top_eq_smul_of_flat` directly instead of writing a tensor
  kernel sequence and proving its injectivity.
- `lem-weil-pbc-regular-local-cotangent-dimension` and
  `lem-weil-pbc-nakayama-local-generators`: the parameter-selection glue uses generation
  by taking ideal preimages and length equality, rather than constructing a cotangent
  basis or applying Nakayama to that list.
- `lem-weil-pbc-fs-adic-field-geometrically-regular` /
  `Sheaf.RingTheory.FormallySmoothAdicGeometricallyRegular`: the weaker regular-local
  conclusion is supplied by `Sheaf.RingTheory.RegularLocalOfFormallySmoothAdic`.
- `lem-weil-pbc-power-series-field-cohen-regular-complete` is not a direct premise of
  this model construction: regularity is supplied by the given parameter system and
  transported from its quotient. Its module still occurs through existing dependencies,
  including the power-series parameter-quotient theorem; no global removal is claimed.

Disposition of the other old `proof_deps`, completing the list above:
`lem-weil-pbc-regular-local-generators-regular-sequence`,
`lem-weil-pbc-regular-local-quotient-kernel-parameters`, and
`lem-weil-pbc-power-series-parameter-quotient` remain used through the new helpers.
`lem-weil-pbc-quotient-local-structure` and `lem-weil-pbc-surjective-image-noetherian`
remain used as Mathlib facts in the helpers.
`def-weil-pbc-formally-smooth-adic` remains a statement dependency; its old proof edge
is replaced by the specific transport and universe-lifting results. No global pruning
of these retained modules is claimed.

The parameter-quotient and regular-local quotient-kernel nodes remain necessary through
the new helpers. The local quotient and Noetherian image facts remain used as Mathlib
applications. These are changes to this argument's dependency route, not claims that
all listed modules disappear from the complete targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The sandbox from the previous attempt contained only the original module with its hole.
The node's plan requested flatness of R -> T and of its base change. The final argument
only needs flatness of the target B over A: a surjection with flat target gives the kernel
intersection identity, and Nakayama over the quotient source kills its kernel. This
prunes that extra flatness construction without changing the conclusion.

The old cotangent-basis plan is also unnecessary for assembling parameters: a full
parameter list of S/m_R S can be lifted, with its kernel segment corrected into ker b;
their ideal together with i(t) has the same image and preimage as the maximal ideal,
and their count is the required dimension.

Checked the empty base parameter list, the empty kernel segment, and zero power-series
variables: the list, ideal-map, and dimension arguments cover them without nonempty
assumptions. In the Cohen case the given head is p, so an empty t is impossible;
p is permuted ahead of the eliminated equations and retained by the coefficient-algebra
parameter-quotient equivalence. No arbitrary data definition, axiom, or weakened target
was introduced. The original node is not a realized unit statement or proof step;
the unit's recorded route is unchanged.

The source checkout lacks the local Stacks TeX file, so the relevant text was read at
https://stacks.math.columbia.edu/tag/07NQ and https://stacks.math.columbia.edu/tag/07NM.
Mathlib search and the existing project declarations were checked before writing the
helpers. LeanSearch returned an Internal Server Error; Loogle, LeanFinder and source
search were available.

## New nodes

`lem-weil-pbc-closed-fibre-kernel-parameter-selection` records the proved selection
of actual kernel equations and their extension with the original base parameters.
Its only structural inputs are existing adic regular-local, parameter-quotient regularity,
and regular-local quotient-kernel theorems.

`lem-weil-pbc-closed-fibre-equation-removal` records the proved power-series construction,
with fibre-level kernel containment and transported smoothness. It uses no flatness
hypothesis and delegates the final kernel equality to the independent rigidity theorem.

`lem-weil-pbc-flat-closed-fibre-kernel-rigidity` records the proved generic Nakayama
argument for any local presentation with a flat target and no extra fibre kernel.
Its proof uses no new holed result. No change record or forced adaptation is required.

## Second reading by H3

1. Compared all delivered modules with the repository. Only the original item's module
already exists there. Its signature and existing docstrings are byte-for-byte unchanged;
the differences are two private proof imports and the replacement of `by sorry`.
No statement, definition, visibility, or target was altered. No change record is needed.

2. Independently compiled all four modules through `lcompile.py --all`, without errors
or warnings, and scanned all delivered sources for forbidden declarations and `sorry`.
None occur. Scratch-copy `#print axioms` checks give only `propext`, `Classical.choice`,
and `Quot.sound` for parameter selection and kernel rigidity. Equation removal and the
original theorem additionally have `sorryAx`, traced to the existing field and Cohen
power-series parameter-quotient theorems. No hole was added and no definition contains
holed data. The witnesses are assembled inside theorem proofs, not public data definitions.

3. No unfinished statement was split off. Read all three new proved helper statements
and proofs: parameter selection is independent of flatness and coefficients; equation
removal omits the final kernel equality and flatness; rigidity is a generic Noetherian
local Nakayama argument independent of regularity and completeness. They are genuine
parts of the argument. Checked empty kernel/base lists and zero variables: the ideal,
length, and quotient arguments impose no nonemptiness; the Cohen head condition excludes
an empty base list and retains p. Independently searched LeanFinder for a surjective
algebra map with flat target and kernel in the maximal ideal, Loogle for `RingHom.ker,
Ideal.map`, and project sources for flat-kernel and maximal-ideal arguments. No theorem
already supplies the combined results. `FiniteCoefficientTensorKernelReduction` is a
related tensor-specific calculation, not a replacement for the shorter direct Mathlib
kernel-intersection argument used here.

4. Read from the original theorem down through the three helpers. Existing regular-local
quotient-kernel and power-series parameter-quotient results supply the structural steps;
Mathlib supplies kernel intersection and Nakayama. No shorter exact result was found.
Reviewed each import against the statements and proofs. `RegularSequence` must remain
public because the new parameter-selection signature uses its `Ideal.ofList` definition.
Narrowed the rigidity helper's public local-ring import to `LocalRing.Basic` and made
`LocalRing.Quotient` private; recompilation verifies the change. Completed the report's
disposition of every old proof dependency. Read `dag/units/sk-thm-p1.json`: the original
node is not in its `realized` statement or steps, and the unit route is unchanged.

5. Read every delivered node against its Lean theorem and proof. The stored Lean
statements match verbatim; every `proof_deps` is exactly the union of step `uses`.
The original node changes only `proof`, `proof_deps`, and `proof_origin`. The three new
nodes have source, searches, provenance, chapter/unit, blueprint ancestry and Lean
records. Their arguments agree with the actual lifts, quotients, transport and Nakayama
steps. Verdict: passes, with the upstream parameter-quotient holes explicitly retained.

Second reading changed only the rigidity helper's import visibility and the report's
complete dependency disposition and independent verification record. Holes closed: one
original; holes added: zero; unfinished statements split off: zero.
