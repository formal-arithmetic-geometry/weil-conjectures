## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_morphism_cohomology_edge` with its
signature, universes, visibility and docstring unchanged. Added the proved private
helper `beta_quasiIso` in the same module. No definitions or interfaces changed.

The upstream affine higher-direct-image vanishing makes F pushforward-acyclic.
Leray acyclicity applied to the injective augmentation makes its pushforward a
quasi-isomorphism. The defining augmentation equation and two-out-of-three show
that the actual horizontal comparison β is a quasi-isomorphism. Applying global
sections to β between complexes of injectives gives the remaining invertible
factor in the definition of the edge map. The existing basic-properties theorem
supplies the exact scalar identity through h.appTop.

Replaced the proof import of ModuleCohomologyFMapFunctorial with
ModuleCohomologyFMapBasicProperties, removed ModulePushforwardInjectiveAcyclic,
and removed the redundant direct LongExactSequence import. The affine
higher-direct-image module already publicly imports Acyclic.
All existing public imports are retained. Updated the existing node's proof,
proof_deps and proof_origin to this route; the unit route is unchanged.

Validated the module with lcompile.py; it compiles without warnings. The argument
also covers degree zero, zero modules and empty schemes: no positivity assumption
is used for invertibility, and all steps are categorical.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.affine_morphism_cohomology_edge`
(node `lem-weil-pbc-affine-morphism-cohomology-edge`).

The private helper `beta_quasiIso` is proved. There are no sorries left in the
item and none added elsewhere: one hole closed, zero holes split off.

This is a proof from existing declarations, not a claim that its entire import
closure is sorry-free. In particular it uses the existing
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMapData_nonempty`
(node `def-weil-pbc-module-cohomology-fmap`) to access the data already used by
the edge-map definition, and the linearity clause of the existing
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_properties`
(node `lem-weil-pbc-module-cohomology-fmap-basic-properties`). Their existing
holes are unchanged. No data construction or new witness-selection definition
is introduced; D is the same resolution system used by the existing edge map.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`:
  node `lem-weil-pbc-module-cohomology-fmap-functorial` is unnecessary for this
  proof because it works with the actual choices, without comparing choices.
- `Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic`:
  node `lem-weil-pbc-module-pushforward-injective-acyclic` is unnecessary as a
  separate edge-theorem proof dependency. The proof applies sections to β
  between complexes of injectives, rather than to h_*I. This node can still be
  reached through the construction of the existing cohomology-map data.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`:
  its direct import is redundant with Acyclic; the module remains transitive
  and is not claimed globally pruned.

Also removed `lem-weil-pbc-lift-along-injective-quasi-iso` from the node's
proof dependencies. No new lift γ is necessary: β and lambda are fields of
existing resolution data. This lemma remains relevant to constructing that data.

Retained `lem-pc-affine-morphism-hi` and `lemma-weil-pbc-leray-acyclicity`,
including the blueprint's designated tools. No unit statement or realized step
is bypassed. These are removals from this item's direct route, not claims that
the modules are unreachable from every project target.

## Where the brief, the DAG or earlier work was wrong

The planned choice of γ and the proof of independence of choices are unnecessary
for this theorem. The existing β already becomes a quasi-isomorphism by the
augmentation equation once F is pushforward-acyclic. The original geometric
statement is unchanged and no statement was disputed.

The proof follows the supplied Stacks sources, read in the available local copy:
coherent.tex (relative affine vanishing and cohomology), cohomology.tex
(Equation 01FA and Remark 01FB), and derived.tex (Leray acyclicity).

## Second reading by W2

1. Interface: PASS. Compared the sole delivered Lean module and node with the
   repository using diff. The existing theorem signature, universes, visibility,
   docstring, and all public imports are byte-for-byte unchanged. There are no
   definition changes, new public declarations, or change records. Only a proved
   private helper, the proof, and private imports change.
2. Proof: PASS. Independently compiled the module without errors or warnings.
   A scratch copy with `#print axioms` shows only `propext`, `Classical.choice`,
   and `Quot.sound` for `beta_quasiIso`; the main theorem additionally uses
   `sorryAx` from existing open dependencies. No sorry or forbidden declaration
   occurs in the delivered module. Checked the augmentation equality through
   `fromSingle₀Equiv`, both Leray applications, two-out-of-three, the invertible
   factors of `D.map`, and the exact restricted scalar action. The chosen D is
   definitionally the same choice already used by the edge map. It is a local
   proof variable, not new data in a definition. The upstream construction and
   independence of resolution choices remain existing obligations; this
   delivery does not claim to close them.
3. Split statements: PASS, vacuous. Zero new holes, nodes, or split statements.
   The private proved helper works for every pushforward-acyclic F. Its proof
   handles the single complex in degree zero and zero objects in positive
   degrees; no positivity of the requested cohomology degree, nonempty scheme,
   or nonzero module is assumed.
4. Route and pruning: PASS. Searched the library and Mathlib for affine
   cohomology comparisons, edge maps, and quasi-isomorphism cancellation.
   The upstream `nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom`
   requires schemes over a field and gives an isomorphism for a different
   cohomology construction, not the stated edge map; it cannot replace this
   argument. The present proof already uses upstream affine vanishing and Leray
   acyclicity. Checked `dag/units/sk-thm-p1.json`: this node is below its realized
   statements and steps, which remain unchanged. The two recorded tool uses
   remain. All three removed old proof dependencies are listed under
   `No longer needed`; no global module pruning is claimed. Proof-only imports
   are private. Removed the redundant direct Acyclic import, since the retained
   AffineMorphism module publicly imports it.
5. DAG: PASS. The existing node changes only proof, proof_deps, and proof_origin.
   The union of step uses equals proof_deps. Its four steps match affine
   vanishing, the actual beta comparison, global-sections cohomology, and
   linearity. Statement, source, unit, tool uses, and Lean record are unchanged.

Second-reading changes: removed the redundant private Acyclic import and
corrected the report's import description; appended this independent review.
No proof repair was necessary. One original hole closed, zero holes added.
