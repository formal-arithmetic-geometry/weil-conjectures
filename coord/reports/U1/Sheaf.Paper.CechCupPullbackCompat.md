## What changed

Completed the proof body of
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality` in
`Sheaf.Paper.CechCupPullbackCompat`, preserving its full signature and visibility.
The proof lifts both classes through the surjective computing-resolution class maps,
uses the resolution Leibniz identity to form their paired cycle, transports the three
cycles along additive cochain maps between different scalar rings, and combines the
three class equations with the source and target `IsModuleCupProduct` characterizations.
The new private `map_cycle_additive` is proved from the cochain commutation equation;
its underlying cycle value is the degree component map. A scoped heartbeat setting
supports the three scalar-changing cycle elaborations and does not change a definition.

Added the proof-only import `Sheaf.Paper.ModuleCupPullbackResolutionMaps`. That new
module isolates the computing-resolution construction: it provides two pairings and
three additive cochain maps, their class-map identifications and their strict section
pairing equation. It has no input cohomological cup product and no assumption of
cohomological cup naturality. The proof in the assigned module genuinely combines its
resolution data with surjectivity, Leibniz, cycle transport and both characterizations.
This is a decomposition, not a claim that the lower construction is already proved.

Updated the assigned DAG node's proof, proof dependencies and proof origin to describe
the implemented argument and the pruned comparison import. No definition, existing
public signature, target, universe or visibility was changed. No forced adaptations.

The delivery base fetched by the second reader has two holes, including
`moduleCup_coefficient_naturality`. The first worker had copied an X2 proof that
was present during its session; that proof is absent from the current delivery
base. This delivery therefore restores that coefficient proof as well as reducing
pullback naturality. The coefficient proof uses the already existing
`moduleCup_coefficient_resolution_maps` and adds no hole. It and the shortened
composition comparison proof were reviewed along with the pullback proof.

## Proved and sorry left

Closed both holes present in the freshly fetched delivery base, by declaration:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`: restores
  the earlier X2 resolution argument using the existing
  `lem-sc-module-cup-coefficient-resolution-maps`, with no new lower hole.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`: reduces the
  statement to the new resolution construction below.

Both belong to `lem-sc-picard-cech-cup-pullback-compat`. No `sorry` remains in
`Sheaf.Paper.CechCupPullbackCompat`; the other five existing public proofs are
retained, with the composition comparison route shortened as described below.

Added exactly one lower hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_resolution_maps`, belonging to
`lem-sc-module-cup-pullback-resolution-maps`, in the new module
`Sheaf.Paper.ModuleCupPullbackResolutionMaps`. Its entire proof is `by sorry`, with a
source and full construction argument in the docstring and DAG node. The pullback
change closes one upper hole and adds one lower hole: a decomposition, net zero.
Relative to the fetched base, the delivery closes two holes and adds one, net one
textual hole closed. This does not assert a whole-library or target-closure ledger
figure; those are measured by the maintainer against the pinned baselines.

## No longer needed

Removed the proof-only import `Sheaf.Paper.CechComparisonMapNaturality` and the assigned
node's proof dependency `lem-sc-cech-comparison-map-naturality`. The current composition
proof applies `cechRefinement_comparison_square` directly to supplied comparisons;
it does not construct auxiliary comparison maps or cup products. The tuplewise
coefficient, refinement and composition arguments use their explicit formulas.
The canonical-comparison definitions remain available through the existing public
imports. This removes a direct proof dependency; it does not assert that the module
is unreachable from every other target path.

Every retained direct import is used by an existing signature or proof, or by the
new pullback proof. No other node or module is claimed pruned. The blueprint unit's
statement, steps and realized fields remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The snapshot changed during the first worker session: coefficient naturality was
landed by X2 while that worker explored the route. The second reader fetched a base
where that hole was open again, so the copied proof is now explicitly counted as
a restored proof. The remaining pullback case cannot use the coefficient-resolution theorem:
its source and target lie on different schemes and have different global rings.
The scalar pullback theorem additionally assumes a field and does not apply to the
unrestricted scheme statement. The additive cochain interface in the new node
handles these different scalar rings without adding any flatness or field hypothesis.

The old composition-step text still mentioned auxiliary comparisons and cups although
the refreshed Lean proof had replaced that route by a direct refinement comparison
square. The updated proof step now records that actual proof and removes its unused
comparison-existence dependency.

## New nodes

`lem-sc-module-cup-pullback-resolution-maps` states existence of computing pairings on
X and X-prime, with three additive global cochain maps preserving the section pairing
and inducing the three canonical pullback class maps. Source constructions read:
Stacks Tags 0FKS, 0FKU (Lemma 20.31.3) and 01FD. The node records the coordinatewise
extension to a scheme morphism as an agent-written argument based on those sources.
Searches ran through the prescribed msearch script: LeanSearch was unavailable
(Internal Server Error); LeanFinder returned unrelated sheaf/gluing declarations;
Loogle supplied the cochain `comm` equation; Mathlib grep found no Godement/cup-pullback
match. Searches of the repository and the entire imported blueprint found no matching
cross-scheme resolution-map statement. The new lemma is lower resolution data, rather
than the original cup-product equality under another name.

Edge cases checked: no quasi-coherence or flatness is needed for these Godement maps;
zero coefficients give zero pairing values; degree zero is the pullback-unit tensor
identity; empty schemes have zero global-section groups. Rings may differ and all
three maps are merely additive. No witness from this existence theorem is used to
construct definition data. The assigned theorem combines the witnesses only in a
proof. No change record is needed: this delivery changes proofs, adds a new node and
module, and removes a plain proof import without changing an existing interface.

## Second reading by U1

1. Compared both delivered modules against the read-only repository. The new module
   is absent there. All existing declaration statements, visibility and docstrings in
   CechCupPullbackCompat are byte-for-byte unchanged (checked with the delivery
   declaration parser); no existing definition body changed. Only proof bodies,
   private helpers, plain imports and a scoped heartbeat setting differ. Verdict: pass.
2. Both files compile locally through lcompile.py (5.9 and 57.1 seconds). Read every
   declaration and checked for forbidden constructs and hollow definitions. The only
   delivered hole is the named moduleCup_pullback_resolution_maps theorem, whose
   entire proof is `by sorry`. The new cycle-transport definition constructs its
   value directly and proves the kernel condition from cochain commutation. The
   resolution witnesses are eliminated within theorem proofs, never used to choose
   new definition data. Scratch #print axioms checks passed for all seven public
   theorems and the new theorem: only propext, Classical.choice, Quot.sound and
   sorryAx. The three tuplewise coefficient/refinement theorems have no sorryAx;
   the other four still depend on upstream holes. The main axiom scratch compiled
   in 40.8 seconds. Verdict: pass, with the explicitly recorded lower hole.
3. Checked the new theorem against CupResolutionPairing, its computing class map,
   moduleCohomologyPullback and the section-normalized tensor comparison. The
   coordinatewise Godement map is compatible with the germ unit and evaluation;
   iteration therefore commutes with cosimplicial faces. Alexander--Whitney is
   preserved strictly, and injective comparison homotopies identify the class maps.
   Checked identity morphisms, degree zero, zero coefficients, empty schemes and
   scalar-changing morphisms; neither flatness nor quasi-coherence is needed by
   the intermediate construction. Read Stacks 0FKS, 0FKU and 01FD directly. The
   cross-scheme extension is correctly identified as an agent argument. Repeated
   LeanFinder, Loogle and Mathlib grep searches with alternate resolution/pairing
   terminology, and searched lean/ for pullback resolution and cup statements.
   No replacement was found: scalarCup_pullback_naturality requires a common field.
   The lower statement supplies resolution data and three class-map equations,
   rather than assuming the desired equality between cohomological cup products.
   Its source, full docstring proof and matching node are present. Verdict: pass
   as a decomposition; the construction is not a few-minute proof.
4. Read the main proof from the cup characterizations down: computing class maps
   are surjective; Leibniz makes the paired cycle; cochain commutation transports
   cycles; the pairing identity and three class equations give naturality. No
   shorter applicable library result was found. All public imports support
   signatures, and all plain imports support proofs. The sole removed old
   proof dependency is lem-sc-cech-comparison-map-naturality, fully listed under
   No longer needed. The direct composite refinement square replaces unnecessary
   auxiliary comparisons and cups. Read sk-prop-av-cube's realized record: no unit
   statement or realized step is bypassed or changed. Verdict: pass.
5. Checked both nodes: proof_deps is exactly the union of step uses, the new node's
   Lean statement matches its declaration, every referenced dependency exists,
   and source, searches, created, blueprint, chapter, unit and Lean fields are
   present. The new proof origin correctly distinguishes the cross-scheme agent
   construction from the source results. Repaired two stale sentences in the
   parent proof plan that still said pullback naturality remained untouched.
   Verdict: pass after that repair.

Second reading retained the Lean proofs and split-off statement. It repaired stale
DAG proof-plan wording, recorded its three independent searches on the new node,
and corrected the reporting baseline and counts against the freshly fetched
delivery base (two original holes, not one). This remains a decomposition with one new lower construction hole,
not an unconditional proof with only the three standard axioms.
