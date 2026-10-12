## What changed

Proved `AlgebraicGeometry.Scheme.exists_etale_stratified_finite` in
`Sheaf.AlgebraicGeometry.EtaleStratifiedFinite`, without changing its signature.
The proof obtains finite affine open covers, applies the existing affine-cover
stratification theorem, applies the existing separated theorem on each affine piece,
assembles those stratifications, then uses the existing affine-local gluing theorem.
Private proved helpers take a Mathlib finite subcover of the canonical affine cover, reindex it by Fin, transport finite-etale properties
through the pullback-pasting isomorphism, and carry out the affine-base argument.

Added `Sheaf.AlgebraicGeometry.ConstructibleStratificationAssembly` with a proved generic
assembly theorem. It builds the dependent sum of local strata, proves covering and
disjointness, and uses the existing constructible-in-constructible-subspace theorem to
prove constructibility of composite images. The predicate on composite immersion maps
is retained literally, so no set-theoretic containment is used to invent a factorization.
Updated the item's proof plan and dependencies to match these Lean proofs.

## Proved and sorry left

Proved the item's sole original sorry:
`AlgebraicGeometry.Scheme.exists_etale_stratified_finite`
(node `lem-weil-pbc-etale-stratified-finite`).
Also proved `AlgebraicGeometry.Scheme.exists_stratification_of_stratified_partition`
(node `lem-weil-pbc-constructible-stratification-assembly`).
No sorry remains in either delivered module, and no new sorry is introduced.
The proofs still depend on existing admitted declarations in the affine-cover,
separated-case, locality and constructible-subspace modules;
these remain the subsequent stage-3 items.
Both modules compile cleanly with the prescribed local compiler.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
  (`lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`): an ordinary finite affine open
  cover is enough; no refinement of a small-etale-site covering is needed.
- `WeilConjectures.ConstructibleSheaf.Refinement`
  (`lemma-constructible-common-refinement`): after the affine-cover theorem, the pieces
  are already disjoint; assemble their local stratifications by dependent sum.

- `Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`
  (`lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`): second reading replaced the
  admitted cover-refinement theorem by Mathlib's canonical affine cover and
  `Scheme.OpenCover.finiteSubcover`.

These three nodes are removed from the item's direct proof dependencies. The common
refinement module can still be needed inside the existing affine-cover and locality
lemmas; this is not a claim that it is globally unreachable. No other planned dependencies were pruned. Fibre products remain used via Mathlib's pasting API.

## Where the brief, the DAG or earlier work was wrong

The planned small-etale-site cofinality lemma is unnecessary for an ordinary affine
open cover. The existing common-refinement theorem takes the upstream scheme
Stratification type rather than the project's LocallyClosedStratification type, and
it does not directly assemble stratifications of different outer pieces. The generic
assembly theorem supplies exactly this missing operation and is fully proved.

The existing node's proof cited Tag 03S9, although its corrected statement and source
already identify Tag 03S0. The updated proof origin and docstring use 03S0.
The local literature files were absent on this machine; the source proofs were read at
https://stacks.math.columbia.edu/tag/03S0 and https://stacks.math.columbia.edu/tag/09YJ.

Checked the new assembly statement on empty outer and local index sets: the finite
sigma construction handles both, and the covering hypotheses preclude a missing
nonempty outer piece. No separatedness or reducedness of the immersion domains is
assumed. The unit record `sk-thm-p1` does not list this auxiliary node among its fixed
realized steps; its route is unchanged.

## New nodes

`lem-weil-pbc-constructible-stratification-assembly` is a generic, proved theorem
assembling stratifications of a finite constructible immersed partition. Its domain
schemes and immersion maps are the given local domains and composite maps, and it
preserves any predicate known for those composites. It is strictly a partition
construction and assumes no etale morphism or finite-etale conclusion. Its source is
the last refinement in Tag 03S0 with the constructibility argument of Tag 09YJ.
Searches were run through msearch.py: LeanSearch was unavailable (HTTP 500); Loogle and
Mathlib grep returned constructibility facts but no assembly theorem. Blueprint search
for stratification found no identical statement; the existing common-refinement node
is for a different operation. There are no definition or statement changes and no
change records.

## Second reading by U2

1. Compared the delivered module with the repository using diff and compared the sole
   existing public theorem's signature byte for byte: identical. No existing definition
   is changed; no hypothesis is added or conclusion weakened. The assembly theorem is
   new, generic, and not a restatement of the etale item. No change record is required.
2. Both delivered modules compile cleanly through lcompile.py. Text search found no
   sorry, axiom, unsafe, opaque, implemented_by or extern. Scratch copies with
   #print axioms show only propext, Classical.choice, Quot.sound and sorryAx for both
   public theorems; sorryAx comes from the already admitted dependency theorems, not
   a sorry in this delivery. The delivery probe also checks private declarations.
3. There are no split-off admitted statements. Read the fully proved new assembly
   theorem and its node together. Its finite sigma index, covering, disjointness,
   constructibility and literal composite-morphism predicate are correct. Empty X,
   empty outer indices, empty local pieces, and arbitrary predicates are handled by
   the same construction; a nonempty uncovered piece is excluded by the hypotheses.
   Independent LeanFinder and Loogle searches and rg over Mathlib, the upstream
   library and lean/Sheaf found no replacement assembly theorem. Verified the cited
   Tag 03S0 final refinement and Tag 09YJ constructibility argument against Stacks.
4. Read the proof from the target down through its affine reduction, separated case,
   assembly and pullback-pasting transport. Found and removed one unnecessary admitted
   dependency: finite affine covers now come directly from Mathlib. The No longer
   needed section includes all three removed old proof dependencies. The new module's
   QuasiSeparated import is needed only for its proof and is now a plain import.
   The unchanged unit sk-thm-p1 realized fields do not name any of these three removed
   auxiliary nodes; no fixed unit step is bypassed.
5. The existing node changes only proof, proof_deps and proof_origin. Updated the cover
   step and its dependencies for the Mathlib proof. For both nodes proof_deps is exactly
   the union of uses. The new node has its source, complete proof, recorded searches,
   provenance, chapter/unit and Lean signature, and matches the new assembly module.

Second-reading changes: replaced the finite-affine-cover helper's admitted cofinality
application with Scheme.OpenCover.finiteSubcover; removed the corresponding import and
DAG dependency; corrected the helper's description in the proof docstring and report;
made the new assembly module's proof-only QuasiSeparated import non-public. The other
proof steps required no repair. No new sorry or statement change was introduced.
