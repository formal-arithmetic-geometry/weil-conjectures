## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.finiteEtale_powerSeries_punctured_cover_sections_comparison`
without changing its signature or its existing docstring. The proof now follows
three concrete comparisons: sections on each scalar thickening, adic completeness
of the power-series ring, and transfer from the structure sheaf to finite étale
covers. The existing
`AlgebraicGeometry.Scheme.bijective_powerSeries_punctured_globalSections` supplies
the comparison with sections on V.

Added three modules, each with one public theorem:

- `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedThickeningRestriction`:
  the finite-index geometric restriction calculation, left for another worker.
- `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedThickeningSections`:
  a complete Lean proof recovering a unique power series from compatible scalar
  sections, using the finite-index calculation and Mathlib completeness.
- `Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer`:
  the general Noetherian quasi-affine finite étale transfer, left for another worker.
  This module also constructs the scalar thickenings, their projections, and their
  transitions by actual pullbacks; their data contain no holes.

The scalar proof explicitly constructs the inverse quotient classes, checks their
compatibility using the pullback square and Gamma-Spec naturality, takes quotient
representatives, proves the Cauchy condition, applies Mathlib precompleteness, and
uses Hausdorffness for uniqueness. Quotient classes are chosen only through
bijections which uniquely determine them; representatives use Mathlib's actual
`Quotient.out` construction. No arbitrary object is chosen from an unproved mere
existence statement.

The complete delivered set compiled without errors or warnings through
`lcompile.py --all`. Public imports and existing declarations in the original
module remain identical. No other existing module was adapted.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finiteEtale_powerSeries_punctured_cover_sections_comparison`
(node `lem-sbc-power-series-punctured-cover-sections-comparison`): 1 of 1 original
holes is replaced by a complete proof from named lower statements.

Also proved the newly added theorem
`AlgebraicGeometry.Scheme.existsUnique_powerSeries_punctured_thickening_sections`
(node `lem-sbc-power-series-punctured-thickening-sections`), with no hole in its body.

Exactly two new holes remain, each the entire proof of a public named theorem:

- `AlgebraicGeometry.Scheme.bijective_powerSeries_punctured_thickening_restriction`
  (node `lem-sbc-power-series-punctured-thickening-restriction`). This states only
  the canonical quotient-ring restriction at a single finite index, with no cover
  P and no compatible-family assertion.
- `AlgebraicGeometry.Scheme.finiteEtale_adic_sections_comparison_of_structureSheaf`
  (node `lem-sbc-finite-etale-adic-sections-transfer`). This is the general transfer
  for arbitrary Noetherian R and arbitrary ring map f, conditional on a scalar
  comparison. It has no power-series, depth, local-ring, punctured-section, or
  positive-dimensional assumption.

This delivery is a decomposition: one original hole closed and two lower holes
added, rather than an unconditional proof or a net reduction of holes. The
combination is substantial Lean code, including the fully proved adic convergence
argument; neither lower statement is the original theorem under another name.

Edge cases checked mathematically: n=0 in the finite-index statement is exactly
Hartogs on the punctured spectrum. Nilpotents in A are allowed, since the truncated
ring is a free A-module and its variable ideal is nilpotent. The scalar argument
uses all positive exponents and projects to exponent zero, so there is no indexing
gap. The transfer permits empty V, the empty cover, rank zero, and variable rank;
local freeness, not a single positive rank, is used. No surjectivity of f is needed
for the transfer: its closed subschemes are defined by the ideal ker(f) itself.

## No longer needed

Removed the original direct proof imports:

- `Sheaf.RingTheory.FlatLocalDepthFormula`, node
  `lem-weil-pbc-flat-local-depth-formula`. This module's proof no longer uses the
  flat local depth formula directly; the global scalar injectivity calculation is
  supplied by the existing global-sections theorem instead.
- `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction`, node
  `lem-sbc-depth-two-hartogs-restriction`, from the item's own imports. Hartogs is
  still needed by the finite-index restriction statement and remains imported
  there. This is removal of a redundant direct import, not global pruning of
  Hartogs or of its dependency closure.

The old direct proof-dependency edges to these two nodes are replaced by the
actual new route in the item's node. No unit statement or realized unit step was
bypassed. No claim is made that either node becomes unreachable from every other
project target. All remaining imports supply statement data, a used proof, a
Noetherian/completeness instance, or a documented dependency of one of the two
remaining named holes.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface correction. The original node's first two
steps can use the existing global-sections theorem rather than repeating its
Hartogs/associated-point proof. The direct Hartogs and flat-depth signatures
alone do not supply the finite-index scalar comparison or the finite locally free
transfer: these are the missing geometric parts, now separate explicit items.
The previously available finite-order/formal approximation statements start with
an actual section on V; they do not recover arbitrary compatible sections on the
thickenings, so they are not substitutes for the finite-index restriction lemma.

Mathlib does provide completeness of multivariate power series for the variable
ideal. The delivered scalar argument uses it and the already proved combined-ideal
coefficient theorem, avoiding a new holed completeness or coefficient-convergence
lemma. LeanSearch returned Internal Server Error; LeanFinder, Loogle, source grep,
and blueprint searches were performed and recorded. The unit record has empty
realized lists, and the route remains its power-series full-faithfulness calculation
through Stacks Tags 0EY9 and 0EKP.

## New nodes

`lem-sbc-power-series-punctured-thickening-restriction` is the scalar finite-index
calculation in the first display of Tag 0EY9, with depth-two Hartogs as its recorded
dependency. Its canonical restriction map is specified, rather than a mere
abstract ring isomorphism.

`lem-sbc-power-series-punctured-thickening-sections` records the proved compatibility,
Cauchy convergence and uniqueness calculation. Its proof dependencies are the
finite-index restriction, the existing combined-ideal coefficient theorem, and
Mathlib's power-series completeness leaf.

`lem-sbc-finite-etale-adic-sections-transfer` records Tag 0EKP's universally exact
finite-free presentation argument for the direct image of a finite étale cover,
including affine base change and the canonical transition maps. Its recorded
local-freeness dependency is the source-library finite flat pushforward theorem.

All three nodes inherit chapter `sec-smooth-base-change` and unit
`sk-prop-input-spreading`. The original node's proof, proof dependencies and proof
origin now match the delivered assembly. There are no change records because no
existing statement, definition, or interface changed.

## Second reading by S1

1. **Existing interface: pass.** Read the repository and sandbox versions with
   `diff -u`. The original module differs only in its two removed private imports,
   three added private imports, and theorem proof. Its complete theorem signature,
   existing docstrings, universe, public section and three public imports are byte
   for byte unchanged. The only other Lean modules are new. Compared the original
   node JSON as well: only `proof`, `proof_deps`, and `proof_origin` changed; there
   is no statement or definition correction requiring a change record.

2. **Proof and data: pass as a decomposition.** Recompiled all four delivered
   files in import order through `lcompile.py --all`: no errors or warnings.
   Inspected every proof and definition. Exactly the two named lower theorems
   reported above contain `sorry`, each as the entire theorem body. There are no
   prohibited declarations or attributes. A scratch module printed axioms for
   all four public theorems and the three new thickening definitions. Theorems
   use only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the three
   definitions use only the permitted three axioms, with no `sorryAx`.
   `openThickeningTransition` is an actual pullback lift whose square follows
   from `baseTransition_comp_baseMap`. In the scalar proof, `Equiv.ofBijective`
   determines each quotient class uniquely; `Quotient.out` then selects a
   representative of that actual quotient. No data are selected from a holed
   mere-existence theorem. Read `hnatural`, `hq`, `hcauchy`, `hbq` and
   `hrestriction`: they identify the correct quotient and pullback transitions,
   use precompleteness at exponent n+1 to recover exponent n+1, and use
   Hausdorffness after projecting positive exponents down to n. The original
   proof lifts a scalar family, uses global-section surjectivity to represent
   a competing section by c, and applies scalar uniqueness before the transfer.

3. **Lower statements and sources: pass.** Read Stacks
   [0EY9](https://stacks.math.columbia.edu/tag/0EY9) and
   [0EKP](https://stacks.math.columbia.edu/tag/0EKP), including their proofs.
   The restriction theorem is exactly the finite-index term of 0EY9's first
   display: B/I^(n+1) is finite free over A, its nilpotent variable ideal leaves
   Spec(A) as its underlying space, and pushing to the punctured spectrum gives
   a finite sum of copies of O_U. Hartogs identifies its canonical restriction,
   not an arbitrary isomorphism. At n=0 this is Hartogs itself; nilpotents in A
   do not affect freeness or the nilpotent thickening argument.
   The transfer theorem applies (1) => (2) => (3) of 0EKP to the closed subscheme
   defined by ker(f) on V. Noetherianity makes V quasi-compact, and O_V is ample
   because V is quasi-affine. Finite generators of E dual yield an embedding
   with locally free cokernel; repeating it yields the universally exact
   two-free-term sequence. Scalar comparison identifies the kernels, and affine
   finite base change identifies them with the specified cover sections. This
   also covers empty V, an empty or variable-rank cover, f an isomorphism
   (constant thickenings), and ker(f)=top (the scalar hypothesis then forces
   the zero section ring). No surjectivity assumption is needed on f.
   Neither remaining hole restates the original: one fixes a single scalar
   index without a cover; the other assumes the scalar comparison and contains
   none of the power-series/depth argument. The new scalar-family theorem is
   proved, rather than a third added hole.
   Repeated searches with different wording: LeanFinder on finite free
   embeddings of vector bundles on Noetherian quasi-affine schemes found local
   generators of sheaves, not the required global comparison; LeanFinder on
   functions on punctured truncated-polynomial spectra found affine spectrum
   results, not this restriction; Loogle for constantCoeff and RingHom.ker
   found no match. Grepped Mathlib MvPowerSeries and algebraic-geometric module
   files, source FinitePushforward, and the project's power-series modules.
   FinitePushforward supplies local freeness only. Formal approximation starts
   with a section on V and cannot recover arbitrary thickening sections.
   No existing declaration closes either geometric hole in a few minutes.

4. **Route and pruning: pass.** The assembly uses existing global sections,
   Mathlib power-series completeness and Noetherianity, and the two explicitly
   missing geometric ingredients. Imports needed only for proofs are private.
   The public imports of each new module supply its signature or public
   pullback constructions; private imports supply the proof or the documented
   proof plan of the remaining holes. The original two proof-dependency edges
   removed are both listed in `No longer needed`. Hartogs stays below the
   finite-index restriction, so neither it nor flat local depth is claimed to
   be globally pruned. Read `dag/units/sk-prop-input-spreading.json`: its
   realized statement and step lists are empty, and the depth-two formal
   full-faithfulness step still follows 0EY9 and 0EKP. No unit step is bypassed.

5. **DAG and report: pass.** Read all four delivered nodes and their Lean files.
   Checked each stored Lean statement is verbatim in its module and each
   `proof_deps` equals the union of the step `uses`. The original node's three
   steps match scalar lifting, global-section comparison and finite-etale
   transfer. The proved scalar node matches the variable-ideal identification,
   quotient compatibility, Cauchy construction and Hausdorff uniqueness. Each
   new node has its source, searches, creation provenance, blueprint ancestry,
   chapter/unit and Lean record. Checked the cited completeness and
   Noetherian Mathlib leaves and the finite-flat pushforward declaration.
   The report names the original hole closed, the two new holes added and
   the proved new scalar theorem: this is a net +1 hole decomposition, not
   an unconditional proof or a net closure gain.

Second-reading changes: added this independent review and the new search
records produced by msearch. No Lean proof, statement, definition, import or
node needed repair. Removed the temporary axiom-check scratch module before
running delivery checks. No additional hole was closed or introduced.
