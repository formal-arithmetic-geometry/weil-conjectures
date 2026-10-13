## What changed

Completed and checked the earlier sandbox attempt. The statement and visibility of
`AlgebraicGeometry.Etale.exists_constructible_module_mono_closed_cohomology_eq_zero`
are unchanged. Its proof embeds the constructible module sheaf into a finite biproduct,
kills each projected class by a finite-cover unit, composes the monomorphisms, and uses
`Abelian.Ext.addEquivBiproduct` on the preserved bilimit to detect zero.

Added the proved module `Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement`
and its node. The component proof uses finite exchange, the finite edge bijection,
Tag 09ZD (2), and unit/edge compatibility. It transfers killing from the abelian unit
to the forgotten module unit by the abelian adjunction bijection. This factorization
requires no pullback/forgetful natural isomorphism. Its auxiliary injectivity lemma is
private and proved by applying cohomology of the inverse isomorphism.

Replaced local `letI` proofs with `have`, added explanatory proof comments, and removed
two unnecessary local elaboration options in the component theorem. Both modules
compile with `lcompile.py --all`, with no compiler warnings. Updated the parent node's
proof, proof dependencies and proof origin to match the implemented argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_constructible_module_mono_closed_cohomology_eq_zero`
(node `lem-weil-pbc-constructible-module-closed-effacement`).

Also proved the new component theorem
`AlgebraicGeometry.Etale.exists_finite_cover_pushforward_unit_closed_cohomology_eq_zero`
(node `lem-weil-pbc-finite-pushforward-constant-closed-unit-killing`).

No `sorry` remains in either delivered module. No holes were added or split off.
These are complete Lean proofs from the existing declarations; this does not claim
that all transitive dependencies of those declarations are already proved.

## No longer needed

Removed these direct proof imports from the parent module:

- `WeilConjectures.SixFunctors.Finite.BaseChange`
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`
- `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology`
- `Sheaf.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility`
- `Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`

The first four are used by the new component module and remain dependencies of this
proof. Only `Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`, with node
`lem-weil-pbc-etale-module-pullback-forget-naturality`, is genuinely unnecessary for
this route. No claim is made that other targets no longer reach it. All other original
proof dependency nodes are retained directly or through the component lemma.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had compiling proofs but no node records or report. These are now
provided. The original DAG called for pullback/forgetful naturality; the argument only
needs a factorization of the forgotten module unit through the abelian unit. This is
obtained directly from the abelian adjunction, without constructing an isomorphism.

Checked the constructible finite-pushforward paragraph of Stacks Tag 09ZE
(https://stacks.math.columbia.edu/tag/09ZE). The argument follows that paragraph and
keeps the unit route: constructible embedding, finite constant killing, monic unit,
finite biproduct assembly. No target, definition or existing signature was changed.

For the component statement, checked finite source affineness, the closed base-change
immersion, finiteness of the underlying abelian group, and q > 0. Its proof uses no
constructibility or comparison hypothesis. Zero coefficients and empty schemes do
not require extra hypotheses. The parent permits n = 0: the empty preserved biproduct
and its Ext equivalence detect zero without a nonempty assumption.

Searches of the library, DAG and blueprint found no existing declaration of the exact
component-unit killing statement. Logged LeanFinder results are general sheaf/module
facts, not an effacement theorem. The source grep found no match. LeanSearch returned
an internal server error and is recorded as unavailable, not as evidence of absence.

## New nodes

`lem-weil-pbc-finite-pushforward-constant-closed-unit-killing` records the proved component
lemma in `lean/Sheaf/AlgebraicGeometry/FinitePushforwardConstantClosedEffacement.lean`.
It is strictly part of the argument: it assumes constant coefficients pushed forward
along one finite morphism, produces a geometric cover and proves killing by its specific
pushed-forward unit. The parent still supplies the constructible embedding, the monicity
argument, and the finite-biproduct assembly. The node contains the five-step proof,
source, actual search records, and exact Lean statement. No change record is needed:
no existing interface changed and no other existing module was adapted.

## Second reading by H2

1. **Interfaces: pass.** Compared both delivered modules with the repository. The
   component module is new. In the existing module, only plain proof imports and
   the proof body differ; the theorem signature, visibility, docstring, universes,
   and namespace are byte-for-byte unchanged. There are no changed definitions,
   target statements, or adapted modules, so no change record is needed.
2. **Proof checking: pass relative to existing open dependencies.** Both modules
   compile in import order through `lcompile.py --all`, without errors or warnings.
   Source inspection finds no `sorry`, forbidden axiom or implementation mechanism,
   or definition containing postponed data. Scratch copies with `#print axioms`
   for both public theorems report exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The last comes from existing imported open proofs:
   neither delivered module introduces a hole. Witness extraction occurs inside
   theorem proofs, not in a public data definition chosen from mere existence.
3. **Component and edge cases: pass.** No statements are split off with `sorry`.
   The new proved component theorem handles one finite constant pushforward and
   its specified unit; it is strictly a part of the parent argument. Read the
   constant-killing and unit/edge-compatibility declarations and checked the
   argument against [Tag 09ZE](https://stacks.math.columbia.edu/tag/09ZE) and
   [Tag 09ZD (2)](https://stacks.math.columbia.edu/tag/09ZD). A finite source over
   affine X is affine, and its closed base change satisfies the killing theorem.
   Degree zero is excluded; q = 1 is included. Zero modules, the zero ring,
   empty schemes, and the parent's empty biproduct impose no missing nonempty
   assumptions. The adjunction factorization uses a genuine inverse hom-set
   equivalence, not an assumed pullback/forgetful comparison. Independent
   LeanFinder, Loogle, and grep searches with different wording, and rg of the
   library and Mathlib Ext implementation, found no shorter existing effacement
   theorem. Generic adjunction and Ext biproduct results are already used.
4. **Route and pruning: pass.** The proof first uses the existing constructible
   embedding, then the proved finite component reduction, monicity of surjective
   units, and Mathlib's Ext biproduct equivalence. Every retained import supplies
   signature data, a used declaration, or a required instance. Public imports
   supply statement notions; proof imports are plain. The removed original
   dependency `lem-weil-pbc-etale-module-pullback-forget-naturality` is explicitly
   recorded above. All other old proof dependencies remain directly or through
   the component. Read `dag/units/sk-thm-p1.json` and its realized steps: this
   reduction is below the unit level and preserves the Gabber affine-comparison
   route and all realized unit steps. No whole-library pruning claim is made.
5. **Nodes: pass after metadata repair.** The parent's changed fields are exactly
   `proof`, `proof_deps`, and `proof_origin`. Both dependency lists equal the
   unions of the steps' uses. Checked the listed declarations and Mathlib matches
   against the actual proof. The new node has its source, complete proof, origin,
   searches, creation, blueprint, chapter, unit, and Lean records. Replaced its
   whitespace-normalized `lean.statement` with the verbatim multiline Lean
   signature required by the brief, and added the independent second-reader
   search records, including Loogle.

Second reading changed only the new node's signature transcription and search
records and this report. The compiling Lean proof required no repair. One original
hole is closed, zero holes are added, and zero statements are split off; the new
component theorem is proved from existing dependencies. This is a proof-body
closure, with existing transitive `sorryAx` dependencies still open.
