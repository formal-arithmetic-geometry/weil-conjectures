## What changed

Replaced the single `sorry` in `AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit`
with a complete Lean reduction along the original eight-step argument. Its signature,
universes, original public imports, and docstring are unchanged. The proof constructs the
witness package from three strict parts, proves the two morphism clauses itself, and
reassembles all twenty conjuncts.

The morphism-descent clause is proved directly from the closed
`Scheme.exists_pullback_hom_of_isLimit`: identify the chosen limit objects with ordinary
pullbacks, descend the composite with the target's first projection, lift the result into
the chosen stage pullback, and verify the delta conjugation formula by pullback uniqueness.
Eventual equality is proved directly from the closed
`Scheme.exists_pullback_fst_comp_eq_of_isLimit`, using naturality of q and p and the chosen
pullback isomorphisms. Affine domains supply compactness and quasi-separatedness; the
quasi-separated stage supplies quasi-compactness of their structure morphisms.

Added three proof-only imports of new modules, each with one public named theorem,
a complete proof in words, and a node. Updated the parent node's proof and dependencies.
All four modules compile together through the prescribed wrapper without warnings.

## Proved and sorry left

Proved, in the stage-3 sense of reduction to named statements:
`AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit`
(node `lem-weil-pbc-affine-etale-site-colimit`). No `sorry` remains in the item's module.
The morphism-descent and eventual-equality conjuncts are complete proofs from existing
spreading-out declarations, rather than new postponed statements.

Every postponed declaration in the delivery is exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_affineEtale_baseChange_system`, node
  `lem-weil-pbc-affine-etale-base-change-system`: only the coherent base-change system,
  its pullback squares, covering and pullback preservation, and site morphisms.
- `AlgebraicGeometry.Scheme.affineEtale_descent_data`, node
  `lem-weil-pbc-affine-etale-descent-data`: only descent of affine objects and finite
  standard coverings for a supplied cartesian base-change system.
- `AlgebraicGeometry.Scheme.exists_affineEtale_colimit_presentation`, node
  `lem-weil-pbc-affine-etale-colimit-presentation`: strictification and colimit comparison
  for a supplied coherent system already satisfying object, map, equality, and cover descent.

These are three proper parts of the argument. None has the original existential
conclusion or obtains that conclusion by repackaging its hypotheses.

## No longer needed

Removed proof-only imports from the item:
`Sheaf.AlgebraicGeometry.DescendSurjective`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`,
`Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`,
`Sheaf.CategoryTheory.ColimitSites`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
Their statements belong below the remaining helpers where applicable; this is removal of
unused direct imports, not a claim that these modules leave the targets' transitive closure.
The spreading-out import is retained and actually used.

All old direct proof dependencies except `thm-pd-spreading-out`,
`lem-weil-pbc-qcqs-morphism-permanence`, and `def-pc-fibre-product` are replaced at the parent
by the three new helper nodes. Their needed descendants are recorded on those helpers.
No mathematical node in the original route is claimed globally unnecessary. In particular,
strictification and the colimit-of-sites argument are retained, and no blueprint unit step
is bypassed. The item is not itself one of the unit's `realized` declarations.

## Where the brief, the DAG or earlier work was wrong

The plan's existing strictification and colimit-site signatures use `Cat.{u, u}` with
index `I : Type u`, whereas the full affine étale categories have object universe `u + 1`
and morphism universe `u`, and this item's strict diagram is `Cat.{u, u + 1}`. Raising
that theorem's single universe also raises its index and coefficient universes, so it
cannot be applied verbatim. The new colimit-presentation helper retains the original
construction and states precisely the part needed at the correct universes.

The existing `affineEtaleSiteBaseChange` uses coefficients `Type (u + 1)`, whereas this
item asks for adjunctions on `Type u`. Its pullback preservation is also only stated for
covering arrows, whereas this item asks for every cospan. The system helper states the
missing combined construction at the original universes, using the same affine restriction
and topos-equivalence route. No existing statement was changed.

`EtaleFiniteDataDescent` descends finitely presented étale objects and finite diagrams,
but does not keep affine domains at the stage; the 01Z6 refinement is still necessary.
It is not a direct substitute for the new affine object-and-cover helper. Both map clauses
were nevertheless proved directly from the existing closed 01ZM declarations.

The cited local Stacks .tex files are absent on this machine. Read the primary source
online: https://stacks.math.columbia.edu/tag/0EYL,
https://stacks.math.columbia.edu/tag/09YL, and
https://stacks.math.columbia.edu/tag/004A. The proof route and source tags are recorded in
the nodes. The LeanSearch service returned Internal Server Error for all three helper
queries; this is recorded as unavailable, with no false absence verdict. LeanFinder,
Loogle, source grep, and blueprint searches were performed.

Edge cases checked in the helper statements: a singleton index gives identity transitions
and a constant colimit; a preorder need not be antisymmetric and proof irrelevance handles
multiple proofs of comparisons; n = 0 keeps the empty covering of the empty object,
with an empty coproduct in the descent argument; the empty base scheme and empty affine
objects cause no nonemptiness assumptions on domains. The nonempty directed index is
retained exactly. Object universe `u + 1`, arrow universe `u`, and coefficient universe
`u` are all kept separately.

## New nodes

`lem-weil-pbc-affine-etale-base-change-system` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-etale-base-change-system.json`, with
module `Sheaf.AlgebraicGeometry.AffineEtaleBaseChangeSystem`. It isolates original steps
1--4 before strictification and before any descent. Its remaining proof follows affine
base change, pullback pasting and uniqueness, and affine-site sheaf equivalence.

`lem-weil-pbc-affine-etale-descent-data` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-etale-descent-data.json`, with module
`Sheaf.AlgebraicGeometry.AffineEtaleDescentData`. It isolates original steps 5 and 7.
The internal map-descent argument is needed only to descend a finite cover; the item proves
its separately asserted morphism-descent clause directly.

`lem-weil-pbc-affine-etale-colimit-presentation` is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-etale-colimit-presentation.json`, with
module `Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentation`. It isolates the
strictification part of step 4 and assembly in step 8, with all four descent properties
as explicit hypotheses. Its construction retains the original strictification and
colimit-site arguments, at the correct universe levels.

No change record is required: no existing definition, statement, or public import changed.

## Second reading by E1

1. **Visible changes:** Compared the delivered item with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and proof-only imports changed. The three added helper modules and their nodes are new declarations, with no accidental edits to existing modules.

2. **Compilation and proof hygiene:** Compiled all four sandbox modules with the prescribed `lcompile.py --all` wrapper successfully. The item theorem has no `sorry`; the only remaining `sorry`s are the three explicitly named split-off helper theorems, each public, documented with a source and proof plan, and matched by a DAG node. No forbidden `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition occurs.

3. **Statements and nodes:** Read each helper statement and tested its intended edge cases (singleton directed index, proof-irrelevant preorder comparisons, empty finite covers, and empty schemes). Each helper is a proper intermediate result: base-change coherence/site structure, affine object and cover descent, or strict colimit presentation. None restates the parent target, and the node Lean records, declarations, proof dependencies, sources, and split status agree with the files.

4. **Pruning and route:** The proof follows the unit route: coherent base-change system, descent data, direct map and eventual-equality arguments, then strict colimit presentation. Removed direct proof-only imports are listed above and are not used by the compiled proof. The parent node records the six dependencies actually used; no unit step or realized route was bypassed.

5. **Axioms and source review:** The proof uses existing pullback-limit and spreading-out declarations plus the three named split results. The source and Stacks tags in the item and helper docstrings were checked against the recorded route; no stronger hypothesis or weakened conclusion was introduced.

I found no proof or statement defect and made no code changes during this second reading.
