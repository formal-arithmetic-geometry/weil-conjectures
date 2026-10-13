## What changed

Proved `Algebra.etale_retraction_finite_type_splitting` with its signature unchanged.
The proof applies the existing étale finite-factor decomposition, transports its
residue-field data through `ULift` to apply the given retraction hypothesis, tensors
the decomposition back to R, and uses surjective projections and `Shrink` to keep
both factors in the universe of S. Module finiteness survives tensor base change;
finite type of B follows from the surjective projection from S.

Added the fully proved module `Sheaf.RingTheory.RetractionBaseChangeNoQuasiFinite`,
with public theorem `Algebra.no_quasiFiniteAtPrime_of_retraction_baseChange` and a
proved private equivalence between the definition of quasi-finiteness and openness
of a singleton in the fibre subspace. The new theorem restricts the spectrum
embedding of the surjective tensor coprojection to a homeomorphism of closed fibres.
All added imports in the original module are proof-only. Its pre-existing unused
existential equivalence binder triggers the unusedVariables linter once its proof is
filled; a declaration-local linter setting preserves that original signature.

The existing node's proof and proof dependencies now record this route, and one new
node records the proved fibre transport theorem. No existing definitions, statements,
universes, public imports or other modules were changed. The unit's route is preserved.

## Proved and sorry left

Closed one original hole: `Algebra.etale_retraction_finite_type_splitting`
(node `lem-weil-pbc-etale-retraction-finite-type-splitting`). No sorry remains in the
item. Added no holes and split off no unproved statements: the new public theorem
`Algebra.no_quasiFiniteAtPrime_of_retraction_baseChange`
(node `lem-weil-pbc-retraction-base-change-no-quasi-finite`) and the private
`quasiFinite_iff_open_fibre_singleton` are fully proved from Mathlib and the existing
definition. The item continues to depend on the existing holed theorem
`Algebra.exists_etale_finiteFactor_decomposition`; this delivery does not claim
that imported dependency has been proved.

Both delivered modules compile together without warnings through lcompile.py.
The new fibre lemma permits zero C and B and arbitrary independent universes;
the proof works with empty fibres directly. With an identity retraction it reduces
to transporting the same fibre through an algebra equivalence. The main theorem
preserves the possibility of zero factors, and obtains smallness from actual
surjections before constructing the smaller-universe models.

## No longer needed

No existing imports or modules were pruned. The old direct proof dependency
`def-weil-pbc-ring-map-quasi-finite-at-prime` is now used through the new
fibre-transport lemma rather than directly in the item; it remains a statement
dependency and its public definition import remains required. The explicit residue-field inverse
and tensor equivalence construction planned for the last step is unnecessary: the
fully proved spectrum-embedding argument establishes the required fibre homeomorphism.
The residue-field definition remains needed for the universe adapter, so its node
and all original dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The decomposition theorem produces R' in Type u,
whereas hR tests Type (max u v); the ULift adapter is necessary. Its factors have
Type (max u v), whereas the conclusion demands Type v; the Small/Shrink construction
is necessary. The library's proved adapter in EtaleRetractionFiniteProductLocal was
reused in substance without importing that unrelated finite-product theorem.
The source's reversed retraction equality in 04GG is already corrected in the item's
statement and was verified against the online source. The local literature checkout
is absent; Tags 04GG and 00UK were read directly on the Stacks Project site.
LeanSearch was unavailable (Internal Server Error); its failed attempt is recorded
without a verdict, alongside successful LeanFinder, Loogle and source searches.

## New nodes

`lem-weil-pbc-retraction-base-change-no-quasi-finite` records the fully proved public
theorem in `lean/Sheaf/RingTheory/RetractionBaseChangeNoQuasiFinite.lean`. It formalizes
only the closed-fibre transport part of 04GG, assumes a specified retraction and a
specified tensor-base-change equivalence, and supplies no decomposition or retraction
existence. The proof has no new dependencies outside Mathlib and existing notion
nodes. No change records are required.

## Second reading by F4

1. Compared the delivered item with the repository using `diff -u`: the existing
   theorem signature, universes, docstring and public imports are byte for byte
   unchanged. Only its proof, proof imports and local linter setting changed.
   The other module is new; no existing definition or statement changed and no
   change record is required. Verdict: pass.
2. Compiled both modules in import order through lcompile.py without warnings.
   Scratch copies with `#print axioms` show only propext, Classical.choice and
   Quot.sound for the new public theorem and private helper; the item additionally
   has sorryAx from the existing imported decomposition theorem. No delivered
   declaration contains sorry or forbidden proof mechanisms. Existential witnesses
   are unpacked within a proposition proof; no public data definition chooses an
   arbitrary witness from an unproved existence theorem. Verdict: pass.
3. No unproved statements were split off. Read the fully proved new lemma from
   its hypotheses through the tensor quotient and fibre homeomorphism: it assumes
   only the specified base change, not decomposition existence, and is strictly
   the final transport step. Empty spectra of zero factors and identity
   retractions cause no exceptional case. Independent searches using Loogle
   `PrimeSpectrum.preimageHomeomorphFiber`, LeanFinder for split coefficient
   maps identifying tensor closed fibres, and rg of the library and Mathlib found
   ingredients but no duplicate transport theorem. Verdict: pass.
4. The item starts with the prescribed decomposition and applies Mathlib directly
   for tensor cancellation, products, finiteness and universe shrinking. Its
   shorter spectrum-embedding argument avoids a residue-field tensor equivalence.
   Read sk-thm-p1's realized statement and steps: none is bypassed or changed.
   Corrected No longer needed to account for the old direct quasi-finiteness
   definition dependency moving into the helper. Verdict: pass after repair.
5. Compared the existing node diff and read the new node completely. The recorded
   steps and proof dependencies match the Lean, including the Mathlib-matched
   tensor nodes. The new node has source, complete proof, search records,
   provenance, chapter/unit, blueprint origin and a verbatim Lean signature.
   Verdict: pass.

Second-reading repairs: made the new module's TensorProduct.Maps import proof-only
(the public QuasiFiniteAtPrime import already supplies the tensor types in its
signature); removed the redundant proof import Mathlib.Logic.Small.Basic from
the item, verified unnecessary by compilation; clarified the dependency accounting
in No longer needed. No proof or signature was rewritten. Closed one original
hole, added zero holes, and split off zero unproved statements.
