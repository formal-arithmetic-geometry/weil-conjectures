## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data` from two
strictly smaller inputs, without changing any existing signature or definition.
Added proof-only imports of `StrictHenselRegularDivisorQuotient`,
`StrictHenselRootTameNormalization`, `StrictHenselizationStructuralFlat`, and the Mathlib
closed-immersion module.

The proof constructs the divisor as Spec(A/(t)). It constructs the ring equivalence
A/(t) with H/(g), proves t regular using flatness and t^|G|=g, transfers regularity
and integrality, identifies the quotient immersion kernel and proves it invertible,
checks the complement prime by prime, and proves the root spectrum locally Noetherian.
It then takes the divisor generic point and combines these results with the finite
tame normalization input. Every private helper is proved.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data`
(`lem-sbc-strict-hensel-root-purity-data`), the item's only hole.

Added and left:

- `AlgebraicGeometry.Scheme.strictHenselization_regular_divisor_quotient`
  (`lem-sbc-strict-hensel-regular-divisor-quotient`): the canonical ring and divisor
  quotient properties, with no cover, root extension or scheme divisor construction.
- `AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_tame_normalization`
  (`lem-sbc-strict-hensel-root-tame-normalization`): the finite normalization and
  etale neighbourhood, with the regular integral Cartier divisor and its generic
  point supplied as inputs, and with base Noetherianness supplied.

This is a decomposition: one original hole closed and two proper lower holes added,
net -1. The final theorem depends on sorry through those inputs. No sorry remains
inside its proof or in any definition. The target module compiled cleanly via lcompile.py.

## No longer needed

No existing import was removed and no module is claimed globally pruned. Two added
proof imports proved redundant and were removed: `Mathlib.RingTheory.Flat.Basic` and
`Mathlib.RingTheory.Spectrum.Prime.RingHom`. The remaining imports suffice in a clean
single-file compile.
`lem-sbc-root-algebra-regular-at-root` is no longer a direct dependency of the item's
divisor construction: the explicit quotient, Cartier and complement calculations
need no root-local regularity theorem. It remains a planned input of the normalization
subclaim, so is not globally pruned. Definitions in the old proof dependency list
remain available through the unchanged public imports. No finite-etale extension or
root-section theorem is imported, avoiding the cycle through this item. The unit
route (tameness, Abhyankar, normalization, then purity in the caller) is preserved;
the unit's realized lists are empty.

## Where the brief, the DAG or earlier work was wrong

The original first step's root-local regularity theorem supplies neither the canonical
strict-henselization quotient comparison nor a scheme Cartier centre. This delivery
isolates the missing quotient input and carries out the scheme construction explicitly.
The original remaining steps name definitions but give no theorem interface for the
ramification calculation and finite tame normalization; the new normalization node
states exactly that portion without moving the whole original statement.

Read Stacks Tags 0EYG, 0EYH, 0BRM, 05WS and 06LN. Quotient compatibility is 05WS
(`lemma-quotient-strict-henselization`); the normalization label is
`pione-lemma-extend-tame-covering-normal`. No excellence assumption was added.
The existing abstract strict-henselization Noetherian and regularity declarations
require an IsStrictHenselization witness and do not directly apply to the canonical
coordinate-ring colimit or its quotient. Blueprint searches for the two new concepts
found no duplicate. Mathlib searches used LeanFinder, Loogle and grep; LeanSearch
returned HTTP 500 and is recorded as unavailable.

Edge cases checked: nonunit g excludes the zero quotient; |G| is positive for every
group, including the trivial group; exponent one makes the quotient equivalence the
evident one; the zero base ring cannot have the given geometric point. Disconnected
torsors are handled by generic stabilizer components rather than a connectedness
assumption. In the new ring lemma, f need not be regular: quotient compatibility and
regularity only need regularity of R/(f) and the nonunit condition. The new ring input also permits f=0, in which case the quotient is H itself. The explicit
root construction uses the original regularity hypothesis hf separately.

## New nodes

`lem-sbc-strict-hensel-regular-divisor-quotient`, in
`StrictHenselRegularDivisorQuotient.lean`, isolates the canonical Noetherian and
regular domain quotient input from the first original proof step.

`lem-sbc-strict-hensel-root-tame-normalization`, in
`StrictHenselRootTameNormalization.lean`, isolates the ramification and normalization
steps with an already supplied Cartier divisor and generic point. Both nodes stay
in `sk-prop-input-spreading` and carry sources and complete proofs in words.
No interface change record or forced adaptation is needed.

## Second reading by F2

1. Compared the delivered item module with the repository version. All existing declaration
signatures and definitions are byte-for-byte unchanged; only proof-only imports, private
helpers, and the target proof body differ. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`. Compilation succeeds with
no errors; the only remaining `sorry`s are the two named split-off theorems listed above.
There are no axioms, unsafe declarations, opaque/extern implementations, or hollow
definitions. Verdict: pass.

3. Reviewed both split-off statements and their DAG nodes. Each is a strictly smaller input:
the quotient theorem isolates canonical strict-henselization regularity, and the normalization
theorem takes the divisor data as hypotheses. Their docstrings give source and complete proof
outlines, and searches found no duplicate declarations. Verdict: pass.

4. Checked the proof route from the target downward. The explicit root quotient and Cartier
construction uses Mathlib and the imported flatness and quotient inputs; the normalization
step is delegated to its strictly smaller node. No old proof dependency is bypassed, and the
reported redundant imports are removed from the effective proof. Verdict: pass.

5. Compared the DAG `proof`, `proof_deps`, and `proof_origin` with the Lean proof and checked
the unit record. The target node records the two split-off inputs and the unit route remains
tameness, Abhyankar, normalization, then purity. Verdict: pass.

Changed only this report section during second reading; no Lean declarations or DAG statements
were changed.
