## What changed

Proved `AlgebraicGeometry.dimension_at_point_components`, with its signature and public imports
unchanged. Retained and verified four proved private helpers for quotient/component dimension, localization
lower bounds, localization dimension inside an open, and maximal ideals in an open; a fifth
proved private helper removes components missing the point and bounds chains in the resulting
neighbourhood. All proofs follow Stacks Algebra 00OT. Updated the existing DAG node's proof,
proof dependencies and proof origin to match the Lean implementation.

Added only proof imports `Mathlib.RingTheory.Ideal.Height`,
`Mathlib.RingTheory.Jacobson.Ring` and `Mathlib.RingTheory.KrullDimension.NonZeroDivisors`.
The existing `Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing` supplies the finite quotient
dimensions and their equality with maximal-localization dimensions.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.dimension_at_point_components`
(node `lem-weil-pbc-dimension-at-point-components`). Added zero holes. No `sorry` remains in
any delivered declaration. This is a proof from the existing stated dependency
`finiteTypeDomain_ringKrullDim_localizationAtMaximal`, whose proof is still a separate item;
it is not a claim that the target's transitive axiom closure is already sorry-free.

The resumed worker independently compiled the module successfully without warnings. The proof explicitly constructs the finite set of
minimal primes below p and takes a maximum of its quotient dimensions. The chosen natural
representation of each dimension is determined uniquely by the equality to ringKrullDim;
no algebraic object is chosen from an unproved mere-existence statement.

## No longer needed

No original Lean import was removed; the existing proof dependency
`Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing` is used. Redundant candidate proof imports
`Mathlib.RingTheory.Spectrum.Prime.RingHom`, `Mathlib.Data.Finset.Max` and
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian` were tested and removed: the required names
are already available through the remaining imports.

The direct DAG dependency `lem-weil-pbc-proper-ideal-contained-in-maximal` is no longer needed:
maximal ideals in neighbourhoods come directly from the Jacobson radical equality. The
standalone definition dependencies `def-weil-affine-spectrum`, `def-weil-pbc-noetherian-ring`
and `def-weil-pbc-finite-type-algebra` were removed from proof_deps (they remain statement
requirements or are embodied in the used theorem statements). No entire module is claimed to
leave the targets' import closure; the maximal-ideal existence result may still be needed by
other dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or unit route was changed. The planned neighbourhood and
localization chain arguments can be implemented using the existing Mathlib coheight and
order-isomorphism APIs; no new holed statements are necessary. During development two
intermediate interfaces were explored, but both were replaced by proved private helpers and
are absent from the delivery. Searches found the component/quotient and localization-height
APIs but no direct theorem for the entire result; LeanSearch was unavailable (HTTP 500),
recorded by msearch.py, and Loogle, LeanFinder and source grep were used instead.

The sandbox inherited an unfinished second-reading section and an obsolete decomposition
report (`coord-report.md`). Both were removed; the independent second reader still needs to
write their own review. The complete inherited proof was checked rather than replaced.

## Second reading by B3

1. **Visible declarations — PASS.** Read the complete repository/sandbox diff. The existing
   theorem's docstring and signature, including universes, instances, all conjunctions and
   existential witnesses, are byte-for-byte identical. All existing public imports and the
   module header are unchanged. The only Lean additions are three plain proof imports,
   five private proved helpers and the replacement proof. No definition or public interface
   was changed; no change record or forced adaptation is required.
2. **Proof and trust — PASS.** Independently compiled the delivered module using lcompile.py:
   exit 0, no warnings. Scanned the delivered source: no sorry or forbidden declaration or
   kernel-bypass construct. Compiled a scratch copy with #print axioms for the public theorem
   and all five helpers. Four helpers use only propext, Classical.choice and Quot.sound.
   quotient_dimension_le_localization and dimension_at_point_components additionally use
   sorryAx through the existing finiteTypeDomain_ringKrullDim_localizationAtMaximal theorem.
   The delivered module closes one original hole and adds zero; its transitive closure is
   not yet sorry-free. The finite minimal-prime set and neighbourhood are constructed
   explicitly. Choice from the open finite-dimension theorem selects only a natural number
   uniquely determined by equality with ringKrullDim, not an arbitrary algebraic object.
3. **Split statements and edge cases — PASS (none split off).** There are no new public
   statements, new nodes or deferred helper proofs. Read each private helper independently:
   quotient/comap height comparison, Jacobson basic-open selection, and open-embedding
   coheight comparison have precisely the hypotheses their applications supply. In the
   neighbourhood upper bound, the reversed chain's last prime is its smallest underlying
   ideal; a minimal prime below it lies below every prime of the chain. A point of the last
   irreducible closed subset rules out all removed components. The argument includes chains
   of length zero, dimension zero and the case with no components removed. Existence of p
   excludes the zero ring; existence of a minimal prime below p ensures qs is nonempty.
4. **Route, searches and pruning — PASS.** Read the finite-type-domain dependency and its
   complete signature; both its finite dimension and maximal-localization equality are used.
   Searched the local Mathlib dimension files, upstream topology dimension module and Sheaf
   ring-theory modules for component/minimal-prime and localization dimension alternatives;
   an independent msearch Loogle query for ringKrullDim and Localization.AtPrime returned no
   hits. Found no existing complete replacement. Checked the exact Mathlib quotient-dimension
   and open-embedding coheight lemmas used in the chain argument. Each added proof import
   supplies an explicitly used API; no original module import is unused. The report lists
   all four old DAG dependencies omitted by the new proof_deps. No whole-module pruning is
   claimed. Read sk-thm-p1's realized record: this item is below the unit's realizing nodes,
   and neither the unit's route nor any realizing node is bypassed or modified.
5. **DAG correspondence — PASS.** Compared parsed node records: only proof, proof_deps and
   proof_origin changed. Read every retained dependency's Lean record or mathlib_match and
   checked the seven proof steps against the actual Lean argument. The basic-open dependency
   is used through its basis clause (not its localization clause). The union of step uses
   equals proof_deps; source, statement, statement dependencies, unit and all other fields
   remain unchanged. There are no new node requirements to check.

Changes by the second reader: appended this independent review. No Lean or DAG repair was
needed. The delivered proof is sound relative to the explicitly identified open upstream
finite-type-domain theorem; no claim of a sorry-free transitive proof is made.
