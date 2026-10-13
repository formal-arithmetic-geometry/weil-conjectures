## What changed

Proved `AlgebraicGeometry.principalOpenCech_subset_row_primitive` with its signature unchanged.
The proof fixes the coefficient degree, casts the cocycle, obtains a fixed-module primitive,
and casts it back while extending by zero away from cardinality k. Private proved helpers
verify identity, injectivity, inverse and restriction compatibility of the equality casts.

Added two fully proved modules:
- `Sheaf.AlgebraicGeometry.PrincipalOpenSubsetCechComparison`: constructs the ordered
  tuple complex and reindexes its cochains by finite subsets, including the erasure and
  sign-count identities. The existing no-cover restriction homotopy gives its homology
  comparison. All data and equality transports are explicit constructions.
- `Sheaf.AlgebraicGeometry.PrincipalOpenInjectiveSubsetExact`: combines the above comparison
  with existing injective module full-Cech acyclicity. Changing the cover target from its
  union to the top leaves the complex unchanged. The elementwise exactness criterion
  supplies the fixed-module primitive and its displayed equation.

Updated the original DAG proof and added matching nodes for the two proved statements.
No existing public signature or definition was changed. All new proof imports are private
imports. The unit record has no realized statement or steps naming this helper; its route
and all higher-level statements are preserved.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.principalOpenCech_subset_row_primitive`
(`lem-sc-principal-open-cech-subset-row-primitive`).

Also proved the newly added declarations without holes:
`AlgebraicGeometry.principalOpen_injective_subset_exact`
(`lem-sc-principal-open-injective-subset-exact`) and
`AlgebraicGeometry.principalOpen_subset_cech_comparison`
(`lem-sc-principal-open-subset-cech-comparison`).

No `sorry` remains in any delivered module; no holes were added. This is one original hole
closed, zero split off. Independent `#print axioms` checks of all three public theorems
show only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.AlternatingCechComputes` from the original module; the node
`lem-pc-alternating-cech-computes` is not needed by this proof. It is replaced by direct use
of `lem-pc-alternating-cech-restriction-homotopy`, whose statement works for every family of
opens without a cover hypothesis. The subset comparison constructs the ordered complex
and verifies its coordinate formulas directly.

The original direct import `Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic`
is moved to the fixed-coefficient exactness module; its node remains needed, so this is
not pruning of that module. No other planned node or module is discarded.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old proof plan routed the comparison through the open
subscheme given by the union because `alternatingCechComputes` has a cover hypothesis.
Its existing lower restriction homotopy theorem needs no cover hypothesis, so using that
interface directly avoids the restriction-to-union and section-comparison bridges.

The local Stacks source file is absent on this machine. The existing cited results were
checked against the public Stacks pages for Tags 01EP, 01FM and 08C1. Search found no direct
Mathlib subset-Cech primitive theorem; LeanSearch was unavailable, while LeanFinder,
Loogle and source searches were recorded. The main case analysis includes r=0, vanishing
high degrees and nonempty erasures at every positive-degree differential without adding
any hypothesis.

## New nodes

`lem-sc-principal-open-injective-subset-exact` is the fixed-coefficient exactness part of
the original proof. It is fully proved from injective module Cech acyclicity and the new
comparison; it has no complex-degree arithmetic or support assertion.

`lem-sc-principal-open-subset-cech-comparison` is the coordinate comparison part, for an
arbitrary module presheaf and any family of principal opens. It is fully proved, with no
injectivity or covering assumption, from the existing restriction homotopy. It explicitly
constructs the complex, coordinate isomorphisms and map. No change record is needed.


## Second reading by F4

1. Compared the delivered original module against the repository with `diff`, and
   extracted the existing theorem signature for an exact byte comparison. Verdict:
   unchanged statement, hypotheses, universes and visibility; no existing definition
   changed and no forced adaptation. The two other modules are new. Restored the original
   single space before `:=` so the signature text is byte-identical.
2. Compiled all three files in import order using `lcompile.py --all`: no errors or
   warnings. Scanned all delivered Lean for `sorry`, prohibited declarations and arbitrary
   witness constructions. Verdict: no holes, axioms or hollow definitions. A scratch module
   printed axioms of each of the three public theorems: exactly `propext`, `Classical.choice`
   and `Quot.sound`; no `sorryAx`. The complexes, coordinate isomorphisms, section casts and
   restrictions are explicit constructions. The homotopy witnesses occur only inside a
   proof, and their source has no remaining nonstandard axiom dependency.
3. No statement is split off with `sorry`. Read both new proved statements and their
   docstrings against their proofs. Checked r=0, r=1, k=1, k=r-1, k>=r, repeated opens,
   empty opens and arbitrary (not necessarily covering) principal-open families. Verdict:
   the exactness result is the fixed-coefficient part; the comparison independently
   handles reindexing, with no injectivity assumption. Neither merely renames the item.
   Independently searched LeanFinder for exactness of finite ordered Cech cochains,
   Loogle for `Finset.orderEmbOfFin, StrictMono`, Mathlib for erasure/enumeration and
   subset-Cech formulas, and project sources including PrincipalOpenCechSubsetInsertion.
   No direct primitive or subset-coordinate comparison exists. Existing enumeration and
   full-tuple exactness lemmas are used. The private elementary product-open identity
   avoids importing the unrelated total-complex construction solely for that identity.
4. Reviewed the reduction from the original row down to fixed coefficients, elementwise
   exactness, and the concrete ordered complex. Checked the two cast directions,
   restriction naturality, erasure cardinalities and sign counts. Verdict: correct and
   preserves the planned injective full-Cech acyclicity route. The removal list names
   AlternatingCechComputes and its node; ModuleInjectiveOpenCoverCechAcyclic stays needed
   through the new exactness module. The unit sk-thm-picard-duality has no realized entry
   naming this helper; its record and route are unchanged. Narrowed the comparison's
   public import from Modules.Tilde to Scheme and ModuleCat.Basic, which supply its
   signature; all proof-only imports remain plain imports.
5. Read all three DAG records alongside Lean. Verified each stored Lean statement
   against its declaration and each proof_deps list against the union of step uses.
   Verdict: proof steps and proof_origin match the implementation; new nodes have the
   required source, searches, creation, blueprint, chapter, unit and Lean records.
   Corrected the comparison node's source place to Tags 01FJ, 01FK and 01FM, matching
   its docstring. Checked the cited public Stacks pages 01EP, 01FM and 08C1.

Changes by this reader: signature spacing and one long proof line; narrower comparison
imports; corrected its docstring to describe subset coordinates on the ordered complex
rather than transporting the complex; aligned its node source; recorded axiom checks.
No mathematical proof or statement required repair. One original hole closed, no holes added.
