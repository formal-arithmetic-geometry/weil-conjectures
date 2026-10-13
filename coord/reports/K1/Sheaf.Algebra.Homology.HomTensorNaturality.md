## What changed

In `Sheaf.Algebra.Homology.HomTensorNaturality`, replace the original
`homTensorDegreewiseMap_natural` hole by product-limit extensionality and the
single-projection calculation. The original theorem signature, docstring,
visibility, and public import remain unchanged. Two proof-only imports are
added: `HomComplexProjections` and `HomTensorNaturalityComponent`.

The sole new module `Sheaf.Algebra.Homology.HomTensorNaturalityComponent` states
`CategoryTheory.homTensorDegreewiseMap_natural_component`. Its docstring gives
the complete localized argument, including restriction to total-tensor
summands, sheafification, pure tensors and componentwise functoriality.
No definitions, existing statements, or unit realizations change.

## Proved and sorry left

Original hole closed: `CategoryTheory.homTensorDegreewiseMap_natural`
(node `lem-sc-hom-tensor-naturality`). Its proof now formally carries out the
product-extensionality reduction.

Hole added and left: `CategoryTheory.homTensorDegreewiseMap_natural_component`
(node `lem-sc-hom-tensor-naturality-component`) in the new component module.
It is the equality after one fixed target product projection. Its proof must
establish the localized calculation, independently of the full naturality
statement. The declaration has exactly `:= by sorry`, with its source and
complete natural-language proof in the docstring.

This is a decomposition, not a complete proof: one original hole is replaced
by one strictly lower component obligation, so the delivery claims zero net
hole reduction. The first worker's additional
`CategoryTheory.homTensorDegreewiseMap_ext` hole has been eliminated: its
product-limit argument is now proved directly in the original theorem using
Mathlib `CategoryTheory.Limits.Fan.IsLimit.hom_ext` and the already proved
`CategoryTheory.homComplex_projections_exists`. That provisional helper and
its provisional node are not delivered.

## No longer needed

No original imports or library modules are pruned. The unchanged sandbox copy
of `HomTensorDegreewise.lean` is omitted from delivery.

All three original `proof_deps` (`def-pur-hom-complex`,
`def-pc-tensor-complex-sheaves`, and `lem-pc-sheaf-modules-tensor-closed`)
remain needed transitively for the component argument and the Hom product
specification. None is claimed pruned. The parent's direct proof dependencies
now name the proved projection-specification wrapper and the new component
node, matching the actual Lean proof. The proposed new node
`lem-sc-hom-tensor-naturality-ext` is unnecessary and removed before delivery;
it was never a node of the original library.

## Where the brief, the DAG or earlier work was wrong

The first worker's two new nodes both depended back on their parent naturality
node, producing a circular proof plan. They had no Mathlib searches, no
verbatim Lean statements, and only one-sentence proof descriptions. The
product-extensionality hole was unnecessary: the limit data are explicitly
part of `homComplex_exists`, and Mathlib already supplies fan extensionality.
The component declaration belonged in its own new module under the brief's
module rule. The first proof also emitted a `letI` style warning.

Stacks Tag 0A90 explicitly asserts functoriality and refers its omitted proof
to More on Algebra, Lemma 15.73.1. The localized component argument here
expands that construction; it does not assert that global pure tensors
generate sections of a sheaf tensor. Sources were checked at
https://stacks.math.columbia.edu/tag/0A90 and
https://stacks.math.columbia.edu/tag/0A8X because this machine does not contain
the repository's untracked Stacks source checkout.

## New nodes

`lem-sc-hom-tensor-naturality-component` is the fixed `(p,q)` projection
calculation. Its statement is self-contained, its Lean signature is verbatim,
and its dependencies are the degreewise currying characterization,
Hom-complex functoriality, total tensor construction and closed tensor
structure. The proof plan expands the localized pure-tensor calculation and
has no dependency on its parent naturality statement. LeanFinder, Loogle and
Mathlib/local grep searches found no exact existing component theorem.
LeanSearch was also attempted, but returned Internal Server Error; this is
recorded as unavailable without a mathematical verdict.
No change records are needed because no existing statement or definition
changes.

## Second reading by K1

1. Compared every delivered module against the repository. The only delivered
   pre-existing module is `HomTensorNaturality`; its existing theorem signature
   is byte-for-byte unchanged (also checked by a string equality assertion).
   Its existing public import and docstring are unchanged. The other delivered
   module is new. No existing definitions or statements were adapted. Verdict:
   unchanged mathematical interface.
2. Compiled both delivered modules locally, in import order, through
   `lcompile.py`, without errors or style warnings. The sole delivered `sorry`
   is the named component theorem listed above; no forbidden declarations or
   hollow definitions are introduced. Scratch copies with `#print axioms`
   check both declarations; they depend only on the standard axioms and
   `sorryAx`, as expected from the component obligation and the upstream
   degreewise existence theorem. Verdict: valid kernel-checked reduction,
   with the remaining hole explicitly identified.
3. Read the new component statement and its localized proof. It is the
   fixed-projection part of the argument, not another name for the full
   naturality equation: product extensionality is actually proved in the
   parent. Identity maps give identical composites; zero maps give zero by
   linearity; complexes concentrated in one degree give the ordinary
   tensor-Hom currying identity. Negative degrees and unbounded complexes
   require no change, since the fixed integer equation indexes the product
   and all comparisons precede any differential calculation. Searches found
   no exact library theorem. Verdict: true and appropriately scoped; the
   component proof remains open, with a complete proof description and node.
4. Reviewed from the top down. Replaced the unnecessary extensionality helper
   by Mathlib's general lemma and the existing proved projection wrapper.
   The two new imports of the parent are proof-only; the new component module
   publicly imports exactly the module used in its signature. No original
   dependencies cease to be needed transitively, and no modules are claimed
   pruned. Read `dag/units/sk-thm-picard-duality.json`: neither the parent nor
   its proposed helpers is a realized unit statement or step, and its
   `realized` record is unchanged. Verdict: unit route retained and the
   reduction shortened below the unit level.
5. Checked the parent and new component nodes against the Lean. Parent proof
   steps and dependency union now match its two explicit theorem applications;
   the component has independent lower dependencies, four search records (including the unavailable LeanSearch attempt),
   the required creation/source/blueprint/Lean fields, and its verbatim Lean
   statement. The cyclic and redundant provisional ext node is removed.
   Verdict: DAG matches the delivery and adds no backward proof edge.

Second reading changed: proved and inlined product extensionality; removed its
helper/node; moved the component obligation into its own module; completed its
docstring proof, node and searches; repaired DAG dependencies; removed the
unchanged degreewise file from delivery; fixed the `letI` warning; and rewrote
the report to distinguish decomposition from net progress.
