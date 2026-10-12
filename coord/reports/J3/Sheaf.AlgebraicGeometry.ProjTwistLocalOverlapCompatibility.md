## What changed

Proved `AlgebraicGeometry.Proj.twist_localOverlap_pointwise` in
`Sheaf.AlgebraicGeometry.ProjTwistLocalOverlapCompatibility` without changing its
signature or visibility. Added the fully proved private helper
`principal_localization_zero`: evaluations on the locus where a degree-zero
fraction is invertible detect zero after further module localization. Its proof
applies the existing basic-open detection theorem to the homogeneous element
`f * g.num`, then cancels denominators in `A_f`.

The overlap proof clears the two module denominators, compares the cross numerator
using the given scalar-compatible evaluations, and cancels the invertible
endomorphisms on the product localization. Updated both existing nodes' proof
routes and dependencies. No new public statement or definition was introduced.
The second reading removed the redundant proof-only import
`Mathlib.Algebra.Module.Equiv.Basic`; its theorem is already available transitively.
The source is [Stacks Tag 01M7](https://stacks.math.columbia.edu/tag/01M7).

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Proj.twist_localOverlap_pointwise`
(node `lem-sc-proj-twist-local-overlap-pointwise`).
The already proved `AlgebraicGeometry.Proj.twist_localOverlap_compatibility` now
uses this completed proof. No holes remain in the item; no holes were added or
split off. Both private and public proofs compile locally without warnings.

The helper uses only the already proved `basicOpen_localization_detection` and
Mathlib localization algebra. Empty basic opens, zero/nilpotent chart elements,
the zero ring, and degree-zero chart numerators require no separate assumptions:
`f * g.num` still has positive degree, and the argument obtains an annihilating
power rather than assuming a prime exists. The Fin 0 case of compatibility is
vacuous, and all indices and denominators in nonempty cases are arbitrary.

## No longer needed

No imports, nodes, or modules of the existing planned route were removed.
The second reading removed the first worker's redundant added import
`Mathlib.Algebra.Module.Equiv.Basic`; this does not prune a module from the closure.
The existing detection module and the cover-module module are both used, the
latter for `localizationAway_map_units_of_dvd`, which appears in the unchanged
public statements as well as in the proof. No additional Sheaf dependencies
were imported, and no auxiliary iterated-localization isomorphism was needed.

## Where the brief, the DAG or earlier work was wrong

The pointwise node's prose describes equality of values at primes, but its actual
Lean conclusion is equality in the entire product localization. Equality of
values alone needs a detection argument. The earlier one-step proof description
omitted that argument and clearing the module denominators. This delivery proves
the existing stronger Lean statement unchanged and records all these steps.
The compatibility node's external dependencies record the dependencies of its
same-module pointwise proof; no edge back to that node is added, since the
pointwise node already has it as a statement dependency.


## Second reading by J3

1. PASS: compared the sole delivered Lean module with the repository by `diff` and
   compared the exact signature text of both existing theorems programmatically.
   Both signatures are byte for byte unchanged. No definitions, instances, public
   imports, visibility, target statements, or other modules changed.
2. PASS: the module compiled locally without warnings using `lcompile.py`.
   A scratch copy with `#print axioms` for `principal_localization_zero`,
   `twist_localOverlap_pointwise`, and `twist_localOverlap_compatibility` compiled
   and printed only `propext`, `Classical.choice`, and `Quot.sound` for each.
   No sorry, forbidden declaration, or arbitrary data construction was added.
3. PASS: there are no split-off statements or new nodes. Read the fully proved
   private helper and traced each denominator cancellation. The positive degree
   is b+g.deg, so detection applies even for a degree-zero numerator. Zero chart
   fractions, nilpotent f, the zero ring, and an empty basic open are covered by
   the power-annihilator argument; Fin 0 has no pair of indices. No nonemptiness,
   reducedness, or domain assumption is hidden in the proof.
4. PASS: searched the library by localization detection/injectivity and overlap,
   and independently queried Mathlib via msearch grep on localization equality
   and injectivity and Loogle on `IsLocalizedModule.lift_apply`. The lift lemma
   is already used; the general localization hits do not replace detection at
   homogeneous relevant primes. The proof uses the proved detection theorem and
   the divisor-unit helper, rather than a new unproved reduction. Both existing
   public imports are needed by the signatures, and the detection import is
   proof-only. The unit sk-thm-picard-duality has empty realized slots in this
   checkout; this delivery neither changes them nor bypasses a recorded unit
   node. Its finite-representative overlap step is retained. No old proof
   dependency was dropped, so the pruning list is complete.
5. PASS: diffed both delivered node JSON files against the repository: only
   `proof`, `proof_deps`, and `proof_origin` changed. Read their dependency
   declarations and checked that the recorded detection/cancellation steps match
   the Lean. The compatibility node records the same-module pointwise argument
   explicitly without introducing a cycle through its statement dependency.

Changed only the redundant added proof import and the report's wording about
new statements/imports. A scratch copy without that import compiled cleanly.
The mathematical proof and DAG edits passed unchanged. Closed one original hole,
added zero holes; this is a proof, not a decomposition.
