## What changed

Proved `AlgebraicGeometry.Scheme.principal_thickening_cokernel_sections` in
`Sheaf.AlgebraicGeometry.Morphisms.PrincipalThickeningCokernelSections` with its entire
signature and existing docstring unchanged. Added three proof-only imports:
`Sheaf.AlgebraicGeometry.PrincipalQuotientMultiplicationImage`,
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`, and
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`.

Four proved private helpers identify the principal-power multiplication image, normalize
the closed-immersion quotient comparison to the canonical structure-sheaf map, construct
structure-module pullback over the ambient scheme, and express degree-zero naturality.
The main proof builds the section equivalences, proves the quotient-projection equation,
and proves the full naturality clause by cancelling the cokernel projection as a sheaf
map. It never assumes that this projection is surjective on global sections.

Updated the item's node proof, proof dependencies and proof origin to this route.
No definitions, existing signatures, public imports or other modules changed.
The unit record `sk-prop-input-spreading` has no realized nodes at this level; its route
is preserved. The three imported results from other units are used as generic tools:
the principal-image theorem supplies the affine quotient calculation; the closed-immersion
quotient and pullback-structure theorems supply the quotient structure sheaf and its
normalization. No existing node of this unit supplies those comparisons.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.principal_thickening_cokernel_sections`
(node `new-principal-thickening-cokernel-sections`).
No sorry remains in the delivered module; no holes were added or split off.
The proof uses existing stated dependencies and makes no claim that every transitive
dependency is already free of sorry.

The four private helpers `closed_structure_quotient`, `thickening_multiplication_image`,
`structure_pushforward_map`, and `zero_sections_naturality` have complete proofs.
The module compiled cleanly through `lcompile.py`, including against the published build.

## No longer needed

None. Both original public imports are required by the unchanged statement. Each of
three added proof-only imports is used. The original node had no named proof dependencies,
so no previously planned node or module is pruned. No additional closed-immersion kernel,
flatness, invertibility, principal-quotient unit-kernel, cohomology pushforward, or separate
sections-naturality module is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original plan's affine calculation, quotient
comparison and naturality steps had empty `uses` lists. Existing library declarations
suffice for the first two, and explicit cokernel cancellation proves naturality even as
the closed immersion varies. The earlier search correctly found components rather than
an exact duplicate; those components now yield the complete proof without new nodes.
The proof includes arbitrary g, n and W, including g=0, units, the zero ring and the empty
open; it imposes no domain, flatness or Noetherian assumptions.

## Second reading by U3

1. Compared the sole delivered Lean module with the repository using `diff -u`.
   PASS: the existing theorem signature and docstring are byte-for-byte unchanged;
   the two public imports are unchanged. Only three plain proof imports, four proved
   private helpers, declaration-local elaboration options, and the theorem proof were added.
   No definition or other module is changed, and no change record is necessary.
2. Compiled the delivered module with `lcompile.py --all`, without errors or warnings.
   Also compiled a scratch copy with `#print axioms` for all four helpers and the target.
   PASS: every one uses exactly `propext`, `Classical.choice`, and `Quot.sound`;
   even the target's transitive proof has no `sorryAx`. Scanned the delivered source:
   no sorry, forbidden axiom, unsafe declaration, opaque declaration, external
   implementation, or kernel-check bypass. No data definition is added. The chosen
   comparison morphisms are characterized by their quotient-projection equations;
   cancellation of the epi projection determines the map used downstream.
3. PASS: no statement is split off and no hole is added. Read all four private helper
   proofs and the three existing imported comparison APIs. The principal ideal identity
   works for n=0, g=0, units, the zero ring, and empty W; it assumes no nonzerodivisor.
   The quotient comparison preserves the canonical structure-sheaf map, rather than
   merely giving an arbitrary isomorphism. The varying-immersion square is proved
   before applying global sections, so it needs no false global-surjectivity assertion.
4. PASS: checked the shorter-route question by searching the upstream modules and
   reading IdealSheafData.nonempty_cokernel_whiskerRight_iso in HilbertPolynomial,
   closedImmersion_ideal_tensor_sections, and H.zeroLinearEquiv. The first two do not
   provide the required normalized quotient isomorphism and varying-immersion
   naturality. The submitted proof directly uses the existing principal-image,
   closed-immersion quotient, tensor-unit, and degree-zero APIs. Each added import
   supplies a declaration explicitly used; both public imports supply statement
   vocabulary. The old proof_deps is empty, so `No longer needed` is complete.
   Read dag/units/sk-prop-input-spreading.json: all realized entries are empty;
   this below-unit quotient calculation preserves the unit's route.
5. Compared the delivered node against the repository node. PASS: only proof,
   proof_deps, and proof_origin change. The proof steps describe the actual Lean
   reductions and the dependency list is precisely the union of their uses:
   lem-sc-principal-quotient-multiplication-image,
   lem-weil-pbc-closed-immersion-unit-quotient, and
   lem-weil-pbc-module-pullback-structure-sheaf. No new node is needed.

Second reading changed only this report, recording the independent review and the
successful axiom checks. The Lean proof and DAG required no repair. Holes closed: one
(principal_thickening_cokernel_sections); holes added: zero; split off: zero; pruned: none.
