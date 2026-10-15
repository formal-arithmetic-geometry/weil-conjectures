## What changed

Reduced `AlgebraicGeometry.proEtaleComparisonPullbackSections` without changing any existing
signature, definition, universe, or public import. The item now constructs its comparison
isomorphism by `Adjunction.leftAdjointUniq`, proves the etale section bijection using the
existing terminal restriction isomorphism, and proves the required comparison-unit equation
using `Adjunction.unit_leftAdjointUniq_hom_app`.

Added four modules. `ProEtaleComparisonSectionFunctor` constructs the section presheaves,
proves their identity and composition laws, constructs coefficient maps, and proves their
naturality and functor laws. Its values use the pullback of the terminal etale X-object;
the second projection explicitly transports these to the requested terminal section values.
`ProEtaleComparisonSectionDescent` proves the sheaf condition using the existing unique fpqc
descent theorem. It includes the conversion of amalgamations and the uniqueness argument.
`ProEtaleComparisonMatchingTransport` isolates the overlap compatibility needed by that descent
application: normalize terminal transport, evaluate composition associativity, and use the
matching equation on the scheme fibre product. This is a single compatibility assertion,
without any covering assumption or gluing conclusion. The full sheaf proof around it is complete.
`ProEtaleComparisonSectionAdjunction` records
the remaining Hom-adjunction construction, original proof Steps 4–6, separately.

The section functor and all intermediate data are explicit constructions. Only proofs are
postponed. In particular, no definition chooses an arbitrary object from an admitted existence
statement. The remaining adjunction has its unit prescribed and is determined by its natural
Hom bijections; the original proof constructs the functor independently of it.

Updated the original node's proof route and added nodes for the four new modules. No blueprint
unit statement or realized proof step is removed. No existing module other than the item is
adapted, and no change record is required.

Validation: all five delivered modules compile without warnings with `lcompile.py --all`.
The three original declaration signatures were compared against the repository and are
unchanged. The delivery dry run performs the required preflight and axiom accounting.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.proEtaleComparisonPullbackSections` (1 of 1).

Added and proved:

- `AlgebraicGeometry.proEtaleComparisonSectionFunctor`,
  node `lem-cbc-comparison-section-functor`.
- `AlgebraicGeometry.proEtaleComparisonSectionDescent`,
  node `lem-cbc-comparison-section-descent`.

Two new holes remain:

`AlgebraicGeometry.proEtaleComparisonMatchingTransport`,
node `lem-cbc-comparison-matching-transport`. It needs the normalization of the two
fibre-product restrictions by the composition associativity law. The mathematical
argument is given in the docstring and node. The compatibility formula is exactly the
one accepted by the existing fpqc descent theorem, and the caller uses it to prove
existence and uniqueness rather than merely moving the original sheaf assertion.
A local unvalidated draft is retained in `scratchpad/matching-latest-full.txt` for the
second worker. It includes the terminal-lift and composition-square calculations, but
its complete check exceeded the file limit. It is excluded from the delivery and is
not counted as proved. Explicit inverse constructions and a normalization API were
tried; no compile limit was raised and no global definition was changed.

`AlgebraicGeometry.proEtaleComparisonSectionAdjunction`,
node `lem-cbc-comparison-section-adjunction`. It still needs the natural Hom maps obtained
by restricting a pro-etale sheaf to Y_et, transposing under Y.hom inverse image, checking
naturality for arbitrary X-maps, and checking the two inverse composites. Its docstring and
node give that argument, including how the diagonal determines the unit. It assumes the
already constructed functor and its two laws; it does not restate the original construction,
comparison isomorphism, or etale bijectivity assertion.

This is a decomposition: one original hole closed and two smaller holes added, net one added hole among delivered declarations.
Every private helper is proved, and no `sorry` occurs in any definition or partial proof.
The existing fpqc descent and inverse-image coherence declarations are reused as permitted
by this stage; no claim is made that their entire import closure is already axiom-clean.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleSectionsFpqcDescent` (used in the new descent module).
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` (already reached through comparison;
  its covering fact belongs to the remaining adjunction construction).
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits` (already public through
  terminal transport and used by the new functor and matching-transport modules).
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` (already reached through the unchanged
  public comparison import).

The new proof imports are the section-functor and section-adjunction modules and
`EtaleSetTerminalRestriction`. The new helper modules import the actual pro-etale site
interface rather than the coefficient comparison/derived-category interface.

A source import-closure comparison found no removed old module.
No entire old module is claimed to disappear from the target import closure: the original
mathematical route is retained and its required steps are now explicit Lean. The removed
imports above are redundant direct imports, not four globally pruned modules. The original
node's immediate proof dependencies now name the actual helper nodes and terminal restriction
API; its old dependency list is distributed through the helpers instead of reimported wholesale.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The original plan is valid. Its phrase that
composition identifies the fpqc equalizer concealed a substantial transport calculation:
the two sides use different inverse-image associations and an explicit `Eq.mp` along
`pullback.condition`. That calculation is now a separately stated obligation; the surrounding descent and
functor construction are implemented. The closest existing generic transport calculation is
the private `terminal_transport_comparison` in `EtaleSetTerminalCone.lean`; its proof is a
useful pattern for the remaining overlap argument, though its private visibility prevents
direct application from this module. The identity and composition laws and the etale terminal restriction API already existed with proofs and were
reused instead of rebuilding the presheaf indexing-category arguments.

Empty index types are allowed by matching transport, and the sheaf proof uses the fpqc
existence-and-uniqueness theorem without adding any nonemptiness, quasi-compactness, or
quasi-separatedness assumption. No user target statement or definition is changed.

## New nodes

`lem-cbc-comparison-section-functor`: explicit construction of the sheaf-valued section functor
and its restriction and coefficient laws, proved in this delivery.

`lem-cbc-comparison-section-descent`: the sheaf condition for a single terminal-section
presheaf, proved from matching transport and the existing unique fpqc descent theorem.

`lem-cbc-comparison-matching-transport`: the exact overlap equation needed by fpqc descent,
stated with its complete natural-language proof from inverse-image naturality and
associativity, without a covering assumption. Its Lean proof remains open.

`lem-cbc-comparison-section-adjunction`: the remaining natural Hom-adjunction construction
and its diagonal-unit formula. Together with matching transport this is the remaining original plan component.
Construction of the section functor from descent, fpqc gluing from matching transport,
the etale section bijection, and the uniqueness-of-left-adjoints assembly are proved.

## Second reading by V4

1. **Statements and signatures.** Compared the delivered item module byte for byte with the repository version. The two existing definitions and the theorem signature are unchanged; the proof only fills the original theorem. The four added declarations have explicit, self-contained signatures matching their nodes. Verdict: pass.

2. **Proof and axioms.** Compiled all five delivered modules with `lcompile.py --all`; compilation succeeds without warnings. The original theorem and the section functor and descent declarations are proved. The two explicitly named split declarations, `proEtaleComparisonMatchingTransport` and `proEtaleComparisonSectionAdjunction`, are the only remaining `sorry`s, each with a source, proof docstring, and matching DAG node. No definition contains `sorry`; no forbidden declaration or axiom was introduced. Verdict: pass subject to the two declared split holes.

3. **New statements.** Checked the four new nodes against their Lean declarations and the proof uses. The section functor and descent statements are strictly lower-level reductions of the target. Matching transport states only the overlap compatibility needed by fpqc descent, without adding a covering hypothesis. The adjunction statement isolates the remaining Hom-adjunction construction and does not restate the target. Mathlib and library searches recorded in the node files found no existing declaration. Verdict: pass.

4. **Pruning and route.** The target's unit route is retained: the construction proceeds through section functor, fpqc descent, matching transport, and adjunction before applying uniqueness of left adjoints. Redundant direct proof imports were removed from the item and are listed under `## No longer needed`; imports needed by helper proofs remain in the helper modules. Verdict: pass.

5. **DAG and report consistency.** Updated proof routes and `proof_deps` for the original node and supplied complete metadata for all four added nodes, including source, proof origin, Lean declarations, and split status. The report lists all holes closed and left, and documents the concealed transport calculation that required a new node. Verdict: pass.

No further changes were made during this second reading.
