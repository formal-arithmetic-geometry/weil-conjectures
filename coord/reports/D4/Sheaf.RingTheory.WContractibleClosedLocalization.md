## What changed

Proved `IsLocalization.wcontractible_closed_localization` in
`lean/Sheaf/RingTheory/WContractibleClosedLocalization.lean`, preserving its complete
signature, universes and visibility and the construction `closedLocalizationFamily`.
Two private, fully proved helpers establish invariance of weak etaleness under a ring
isomorphism and weak etaleness of a finite product of weakly etale ring maps.

The spectrum embedding and image use Mathlib localization spectra and maximal ideals.
The canonical quotient equivalence uses the quotient-localization instance and
`IsLocalization.atUnits`. The finite-cover clause verifies both quasi-compactness over
every affine open and weak etaleness of all members.

For the retraction clause, follow the displayed finite product in Stacks Tag 0987 directly.
For a faithfully flat weakly etale `B → D`, the product of `D` and the principal
localizations is weakly etale (finite affine coproducts and source locality), and its
spectrum is surjective. Apply the given ring retraction hypothesis to this product.
The principal-factor idempotents have images in `I`, so the `D`-factor idempotent maps
to a unit idempotent, hence to `1`, in `B`. Extending elements of `D` by zero and
composing with the product retraction constructs the desired ring map `D → B`.
Localization uniqueness proves its retraction identity. Explicit universe lifts support
`D : Type (max u v)` without restricting the statement.

Updated the existing DAG node's proof, proof dependencies and proof origin to this
argument. No declaration signatures or definitions changed. The second reader removed
a redundant direct public import; its unchanged public reachability is documented in
`coord/changes/WContractibleClosedLocalizationImports.md`.
The source statements and proofs in Tags 096V, 0987 and 09AH were read; the source was
retrieved into the sandbox scratchpad because the repository's literature copy is absent
on this machine. LeanFinder, Loogle, launcher grep, and local source searches found the
localization APIs but no existing theorem proving the complete statement.

## Proved and sorry left

Closed the sole original hole, `IsLocalization.wcontractible_closed_localization`
(node `lem-weil-pbc-wcontractible-closed-localization`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the delivered module, and no split-off modules are added.

A clean single-file compile takes about 6 seconds. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for the theorem. The proof covers the
empty principal list, the unit ideal, the zero quotient and the zero ring uniformly;
it introduces no nontriviality assumption. In particular the quotient equivalence is
canonical on every element of `R`, and the retraction proof uses equality on all
localization fractions, not only equality on spectra.

## No longer needed

Removed the redundant public import `Mathlib.RingTheory.RingHom.FaithfullyFlat`
(second reading; still publicly reachable through `IndPrincipalZariski`).

Removed the proof imports:

- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`.
- `Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection`.

The following original proof-dependency nodes are not needed by this proof and were
removed from this node's `proof_deps`:

- `lem-weil-pbc-localization-prime-residue-field-iso`: use Mathlib's spectrum APIs directly.
- `lem-weil-pbc-localization-base-change`: the proved localization weak-etaleness API suffices.
- `lem-weil-pbc-flat-ring-map-iff-flat-affine`: no new flat-affine conversion is required.
- `lem-weil-pbc-fibre-product-affine-spectra`: no diagonal calculation is required here.
- `lem-weil-pbc-wcontractible-cover-section`: apply the ring hypothesis directly to the product.
- `lem-weil-pbc-scheme-coproduct-family`: use the more precise existing finite-affine
  coproduct spectrum node, which is a Mathlib leaf.
- `def-weil-open-immersion`: no open-subscheme factorization is constructed.

The finite-affine coproduct spectrum and weak-etale source-locality nodes are the
Mathlib tools used by the proved product helper. None of these changes bypasses a unit
statement or realized unit-proof step; this auxiliary node is not among the unit's
`realized` entries. The two retained public imports supply `RingHom.WeaklyEtale` and
`Scheme.proetalePrecoverage`, respectively; removing either makes the unchanged
statement fail to elaborate. The removed faithfully-flat module remains publicly
reachable, so no declarations or instances cease to be exported. Temporary
experimental imports were also removed; the final module adds no imports.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned cover-section and subsequent geometric
factorization are unnecessary: the ring hypothesis already splits the finite product
appearing in Tag 0987, and the component-idempotent calculation gives the restriction
algebraically. This is a shorter implementation of the source argument below the unit
level, with no weakening or additional hypotheses. The repository's cited literature
file was absent locally; the matching upstream Stacks source was read in the sandbox.


## Second reading by D4

1. **Visible interface: pass.** Compared the complete delivered file with the repository.
   The existing theorem signature (including universes and visibility) is byte-for-byte
   identical. The entire `closedLocalizationFamily` definition is byte-for-byte identical.
   The only added declarations are two private proved helpers. No target or definition
   changes. The redundant public import removal is recorded below and preserves the
   complete public import closure.
2. **Proof and axioms: pass.** Independently compiled the module with `lcompile.py`:
   no errors or warnings. Compiled a scratch copy with `#print axioms` for the family,
   both helpers and the theorem: each lists only `propext`, `Classical.choice`,
   `Quot.sound`. Scanned the delivered Lean for holes and prohibited declarations:
   none. Reviewed every construction and proof clause, including the finite affine
   quasi-compact covering condition, universe lifts, idempotent restriction and
   equality of ring maps on all fractions. No data is chosen from an unproved theorem.
3. **Split-off statements: pass, none.** No new holes, modules or public statements.
   Both private helpers are fully proved. Checked the empty finite product in the
   product helper and, in the main theorem, `r = 0`, `I = 0`, `I = R` and the zero
   ring. No nontriviality assumption or extra finiteness hypothesis is introduced.
4. **Route and pruning: pass after import repair.** Read the supplied Stacks source
   passages for Tags 096V, 0987 and 09AH. Searched the local Mathlib and library APIs
   and independently queried LeanFinder for finite products of weakly etale maps;
   the returned formal-etale product lemmas have stronger hypotheses and do not
   replace the proved helper. The geometric finite-coproduct proof is appropriate.
   Confirmed that all seven removed original proof dependencies are listed under
   `No longer needed`. Read `dag/units/sk-thm-properbasechange.json`: this auxiliary
   node is not a realized unit statement or step; none is bypassed. Removing either
   retained public import fails on the unchanged statement. Removing the redundant
   faithfully-flat import compiles cleanly and preserves its public import path.
5. **DAG: pass.** Compared parsed node JSON with the repository: only `proof`,
   `proof_deps` and `proof_origin` differ. Read the Lean/Mathlib records of every
   retained and added dependency. The union of step `uses` equals `proof_deps`;
   the spectrum, quotient, finite cover, product and idempotent steps describe the
   actual proof. No new nodes or statement changes.

**Changed in second reading:** removed the redundant direct public import
`Mathlib.RingTheory.RingHom.FaithfullyFlat`; corrected this report's claim that all
three public imports were necessary; added
`coord/changes/WContractibleClosedLocalizationImports.md` documenting the unchanged
public closure and all downstream users. The proof required no repair. Holes closed:
`IsLocalization.wcontractible_closed_localization` (1); holes added: none (0).
