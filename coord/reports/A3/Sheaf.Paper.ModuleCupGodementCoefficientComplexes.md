## What changed

Repaired return X-e7670: deleted the duplicate private declaration
`AlgebraicGeometry.Scheme.Modules.tensor_summand_d` from
`ModuleCupCosimplicialAWNaturality`. The existing declaration in
`ModuleCupCosimplicialAW` is private, so an ordinary import does not expose it.
The second reader verified that `import all` can expose private helpers; the direct
Mathlib differential proof is retained because it already avoids this helper.
The cochain-map proof now applies the existing Mathlib declarations
`HomologicalComplex.mapBifunctor.d_eq`, `ι_D₁`, `ι_D₂`, `d₁_eq` and `d₂_eq`
directly, then simplifies the signs and applies the existing signed Leibniz theorem.
No replacement helper or duplicate statement is introduced; no library module is adapted.


Proved `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_coefficient_complexes`
without changing its statement. Added two proved modules:
`Sheaf.Paper.ModuleCupGodementCoefficientModels` constructs compatible augmented
cosimplicial models and coefficient morphisms; `Sheaf.Paper.ModuleCupCosimplicialAWNaturality`
constructs the explicit Alexander--Whitney maps and proves their coefficient square.
The main proof applies the existing Godement quasi-isomorphism and flasqueness results,
checks strict nonnegativity and the two section equations, and packages the witnesses.

The coefficient construction uses one shared natural Godement tensor transformation
for both triples. Its recursive pairings are natural by induction. The coefficient
maps commute with both cofaces and codegeneracies, so they are actual cosimplicial
transformations. Their augmentation squares are checked in degree zero using
`HomologicalComplex.from_single_hom_ext`. No arbitrary witness is put into a definition:
the two new definitions are explicit functorial maps (the private iterate map and
`moduleCup_cosimplicialMap`). All remaining private helpers are proved; the second reader removes repeated foundational
helpers using proof-only `import all` imports of their existing modules.

Compiled all three delivered modules in import order, below the 60-second per-file
limit, without warnings. The delivery tool's axiom probes found no forbidden axioms. Edge cases need no additional assumptions: zero sheaves and
zero maps satisfy the same naturality identities; the empty scheme uses empty product
universality; negative tensor summands have a zero factor. No existing declaration signature,
universe or declaration visibility was changed. The pruned public import is recorded below. No other held module was adapted.

## Proved and sorry left

Closed the original single hole in
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_coefficient_complexes`
(node `lem-sc-module-cup-godement-coefficient-complexes`).

Also proved, with no holes added:
- `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_coefficient_models`
  (`lem-sc-module-cup-godement-coefficient-models`).
- `AlgebraicGeometry.Scheme.Modules.moduleCup_cosimplicial_aw_natural`
  (`lem-sc-module-cup-cosimplicial-aw-natural`).

There are no `sorry`s in any delivered module. This closes one original hole and adds
zero holes; it is not a decomposition into new admitted statements.

## No longer needed

The duplicate private `tensor_summand_d` declaration is removed. Second reading also
removes duplicated flasqueness and Godement naturality helpers, reusing their existing
private declarations via proof-only `import all` instead. Its role is supplied
by the existing Mathlib differential API already imported; no new import is required.


Removed the original import `Sheaf.Paper.ModuleCupGodementPairing`, replacing it with
the four required statement-level public dependencies:
`Sheaf.Paper.ModuleCupResolutionData`, `Mathlib.Topology.Sheaves.Flasque`,
`WeilConjectures.Mathlib.Algebra.Homology.Monoidal`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`, plus the actual proof imports (including proof-only `import all` of
`ModuleCupGodementCosimplicialInput` after second reading).
Return H9 also removes the unused public import
`Mathlib.Algebra.Homology.Embedding.IsSupported`; it is not a replacement dependency. Neither its
`moduleCup_godement_pairing` theorem (`lem-sc-module-cup-godement-aw`) nor the standalone
existential `moduleCup_cosimplicial_aw` (`lem-sc-module-cup-cosimplicial-aw`, module
`Sheaf.Paper.ModuleCupCosimplicialAW`) is needed by this proof. The latter is replaced
by the explicit natural construction, not an arbitrary choice of an existential map.
These two modules are absent from the delivered modules' direct imports.

The previous proof dependency `lem-sc-module-cup-godement-model-pairing` is also not
used as a theorem: two independently existential pairings do not supply their common
coefficient naturality square. Instead the new construction uses one beta and both
recursive pairings. Its module still occurs indirectly through the existing
`ModuleCupGodementCosimplicialInput` module, whose definitions we use; no claim is made
that it leaves the entire target import closure. The single-model existence,
quasi-isomorphism and product-flasqueness nodes remain needed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

Return X-e7670 correctly found a repeated private theorem statement. Its suggested
import is unavailable because the existing theorem is private. The repair uses Mathlib's
existing public differential formulas directly instead. All three repaired modules
compile without warnings (5.3, 13.1 and 10.5 seconds). The delivery dry run rebuilds
the delivery on the fetched `sheaf-dag` base; server compilation is enabled for this repair.
The previous second-reading records were removed because they precede this repair;
the next independent reader must read the changed proof.


Repaired return H9: removed the unused public `Embedding.IsSupported` import
and corrected the replacement-import list in this report and the change record.
Recompiled all three delivered modules without warnings (6.2, 13.2 and 10.3 seconds).
The unchanged direct importer `Sheaf.Paper.ModuleCupCoefficientResolutionMaps`
also compiles against the repaired sandbox outputs without warnings (22.0 seconds);
its temporary verification copy is excluded from the delivery.
No mathematical statement error was found. The original plan correctly warned that
one-pair existential model statements do not themselves supply functoriality across
coefficient morphisms. That construction and Alexander--Whitney naturality are now
explicit Lean proofs. The new proofs reuse the existing stalk-product and signed
Leibniz results rather than adding replacements for them. The source front/back
formula was checked in Banerjee §1.1.4 and the functorial Godement construction in
Stacks Tag 0FKR.

## New nodes

`lem-sc-module-cup-godement-coefficient-models`, in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-godement-coefficient-models.json`,
records the proved cosimplicial coefficient construction. Its proof dependencies are
the existing concrete model existence, canonical beta/recursive pairing construction
and collapse compatibility. No flasqueness or exactness assertion is hidden in it.

`lem-sc-module-cup-cosimplicial-aw-natural`, in
`dag/nodes/sec-abelian-varieties/lem-sc-module-cup-cosimplicial-aw-natural.json`,
records the proved naturality of the explicit front/back tensor cochain maps. It uses
the existing component and signed Leibniz nodes and has no Godement or exactness
hypothesis. All search records are real queries recorded in `searches.jsonl`;
LeanSearch returned an internal server error, while LeanFinder, Loogle and source grep
were available. Blueprint searches for Godement and Alexander returned no matching
blueprint node. The import-pruning record is `coord/changes/module-cup-coefficient-imports.md`; it records
the narrower public re-export and unchanged theorem signature. No dependent adaptation
is required.


## Second reading by A3

1. **Interfaces: pass.** Diffed the existing coefficient-complex module against the
   repository: the entire theorem signature, universe, binders, visibility and original
   docstring are byte-identical. The only interface change is the declared narrower public
   re-export, recorded in `coord/changes/module-cup-coefficient-imports.md`. Both additional
   modules are new; no other existing module is modified.
2. **Proof and data: pass.** Read all three modules and compiled them in import order.
   No delivered source contains `sorry`, an axiom, unsafe/opaque declarations, extern,
   implemented_by or skipped kernel checks. The three public theorem axiom checks show
   only propext, Classical.choice and Quot.sound. The iterate map and extended alternating
   map are explicit constructions. Existential models and recursive pairings are unpacked
   inside theorem proofs; no arbitrary existential witness enters a definition.
3. **New statements: pass.** The compatible-model theorem gives cosimplicial maps commuting
   with both generators, their augmentation squares, and the degreewise tensor square.
   The shared beta is essential: independently chosen one-triple pairings cannot establish
   the square. The AW theorem assumes that square and proves total-complex naturality;
   it asserts no exactness or flasqueness, so neither new theorem restates the whole item.
   Checked degree zero (identity front/back inclusions), negative bidegrees (zero source),
   zero coefficient maps and empty products. Searches using "alternating coface complex
   tensor product natural transformation cochain pairing" (LeanFinder), "Flasque"
   (Loogle), and source searches for Godement naturality and flasqueness found no public
   replacement of either new theorem. No holes are split off.
4. **Route and pruning: pass after repair.** The signed Leibniz theorem and Mathlib tensor
   differential formulas give the AW cochain-map condition with the correct two signs.
   Coproduct inclusions detect the coefficient square. The final proof applies the six
   existing quasi-isomorphism results and evaluates the two augmentation identities on
   tensor sections. The old model-existence dependency remains used by the new model
   theorem; the old standalone model-pairing and AW-existence dependencies are unused as
   theorems and are listed under No longer needed. The unit sk-prop-av-cube realized
   record has empty statement/step lists; this changes no unit route or realization.
   Found duplicated private foundational helpers. A scratch compile verified that Lean
   `import all` exposes them: removed all three flasqueness helpers from the main module
   and the stalk/projection/evaluation/functoriality/unit/multiplication helper block from
   the model module. Reuse existing helpers from ModuleCupGodementCosimplicialInput and
   ModuleCupGodementRelations with proof-only imports. Public imports remain confined
   to statement/definition dependencies.
5. **Nodes: pass.** Matched each new lean.statement with its declaration and checked all
   proof dependency declarations. The two new nodes have source, searches, creation,
   blueprint, chapter/unit and Lean records. The old node changes only proof, proof_deps
   and proof_origin. Updated the proof prose to identify reused private helpers. The
   mathematical dependencies are unchanged: these helpers implement the recorded
   reduction from the model definitions and product-flasqueness result.

Second-reading changes: removed duplicate private foundational proofs, replaced them
with proof-only `import all`, updated the affected DAG proof prose and import change
record, and recorded this independent review. One original hole closed; zero holes added.
