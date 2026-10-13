## What changed

Proved `WeilConjectures.DerivedTotalResolution.total_resolution_cycle_support_step`
in `lean/Sheaf/Paper/TotalResolutionCycleSupportStep.lean` without changing its
signature, visibility, or docstring. Added the proof-only import
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.

The proof follows the original node's complete argument. A concrete coproduct
projection is constructed with `HomologicalComplex₂.totalDesc`; private lemmas
compute its composites with summand inclusions and show that projected vertical
boundaries vanish in opcycles. The total differential formula follows from
Mathlib's `ι_D₁`, `ι_D₂`, `d₁_eq'`, and `d₂_eq'`. Projecting the finite cocycle sum
first makes its outer component a vertical cycle. Projecting onto the next
column and then opcycles shows its horizontal image has zero homology class.
Exactness of the horizontal homology pair supplies a preceding class;
surjectivity of `homologyπ` supplies a cycle representing it. The quotient
criterion `moduleCat_pOpcycles_eq_zero_iff` supplies the vertical primitive.
Both total boundary corrections are constructed explicitly, with the vertical
sign `p.negOnePow` applied twice and cancelled by `Int.units_mul_self`.
The new coordinate family is `Function.update x r (x r - w)`; finite-sum algebra
proves its support formula. Subtracting the boundary gives an actual cycle by
`iCycles_d` and `d_comp_d`.

Source checked: [Stacks Project, Tag 09IZ](https://stacks.math.columbia.edu/tag/09IZ),
proof, the outer component and the two boundary corrections. Local semantic
search, Loogle, and source grep found no existing support-reduction theorem.
The proof uses the Mathlib homology and total-complex APIs directly.

## Proved and sorry left

Closed the only original hole:
`WeilConjectures.DerivedTotalResolution.total_resolution_cycle_support_step`
(node `aux-total-resolution-cycle-support-step`). All private helpers are proved.
No holes remain in the delivered module and no holes were added elsewhere.
This is a proof, not a decomposition. Local single-file compilation succeeds
without warnings. The delivery dry run checks the axioms of every declaration.

The proof handles `r = 0` with the same formulas: the removed column is -1,
the preceding correction lies in column -2, and the neighboring update is in
column zero. No division, domain assumption, boundedness assumption, or
restriction on the integer degree is used. The sign is an integer unit, so its
cancellation also holds in characteristic two and for the zero ring.

## No longer needed

None. The node had no proof-dependency imports or nodes to prune. The original
public imports are retained. The final proof needs only the additional
proof-only Mathlib import named above. No new statement module is delivered.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The node's existing proof plan describes the route
now implemented, so its proof fields and empty `proof_deps` remain correct.
The unit has no realized node-level obligations bypassed by this proof.
The local repository has no `literature/stacks-project/homology.tex`; the cited
proof was read at the official Stacks Project URL above instead.

## Second reading by J3

1. PASS: Compared the delivered module with the repository using `diff` and
   separately compared the existing theorem's signature and docstring as exact
   strings. Both are byte-for-byte unchanged, including visibility. The only
   changes are a proof-only import, proved private helpers, and the theorem proof.
   There are no other delivered modules or interface change records.
2. PASS: Independently compiled the delivered module using `lcompile.py`, with
   no errors or warnings. Scanned for forbidden declarations, options, and holes:
   no `sorry`, axiom, unsafe, opaque, implemented_by, extern, or kernel-check bypass.
   A scratch copy with `#print axioms` checks the target; the delivery tool also
   probes every declaration. The coproduct projection is an actual `totalDesc`
   construction. Cycle representatives and primitives are obtained in proofs
   from proved Mathlib facts, without defining data from unproved existence.
3. PASS: No statements or holes are split off. All private helpers are proved.
   Checked the smallest support case `r = 0`: the removed, preceding, and updated
   columns are respectively -1, -2, and 0; the exactness hypothesis applies at
   -2. The two sign factors cancel as integer units in every ring, including
   characteristic two and the zero ring. Integer total degrees are unrestricted.
4. PASS: Read the argument from the target through `outer_boundary`,
   `lift_outer_class`, and `outer_cycle`, checking the differential formula and
   projection calculations. The two corrections agree with Stacks Tag 09IZ.
   Independent semantic search for elimination of an extreme totalization
   component and source searches in both library roots found no applicable
   shorter theorem; the semantic hits concern HomComplex coboundaries or support
   vanishing and do not replace this argument. The added ModuleCat import is
   needed for `moduleCat_pOpcycles_eq_zero_iff` and is correctly proof-only.
   Original public imports supply the signature's homology, total, module,
   exactness, and finite-sum vocabulary. The original node has no `proof_deps`
   to remove. Read `dag/units/sk-thm-picard-f-representable.json`: its `realized`
   statement and step lists are empty, and this local support reduction does
   not replace a unit step. No pruning is warranted.
5. PASS: Read `aux-total-resolution-cycle-support-step.json` in full. Its proof
   plan, empty node-level `proof_deps`, source, and `proof_origin` describe the
   implemented two-boundary argument; the tools used are Mathlib declarations.
   No new nodes or node edits are needed.

Second reading changed only this report, adding the independent checks above.
No mathematical or Lean repair was necessary. Holes closed: one, namely
`WeilConjectures.DerivedTotalResolution.total_resolution_cycle_support_step`;
holes added: zero; split off: zero; pruned: none.
