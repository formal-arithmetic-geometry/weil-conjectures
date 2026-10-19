## Worker report

The node is an exact existing declaration:
`CategoryTheory.Adjunction.projectionFormula` in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`, lines 180–190.
No Lean module is delivered and no definition or theorem is restated. Only the
item's `lean` field is changed. There is no statement correction, new node,
dependency delivery, or mathematical dispute.

Read the complete stage-2 brief, stage document, delivery-errors H, worker role,
setup, goal, state, tools README, CompactObject example and record, the item's
statement and seven proof steps, both statement-dependency records, the current
main-20261015 blueprint statement/proof and transport unit clause 4. There is no
repair note for this item. Read the full upstream signatures/docstrings and
construction through `Adjunction.projectionFormula`, and confirmed the source
against the current server with `scompile.py --source`.

### Hypotheses and clauses

- Arbitrary monoidal categories C and D: inherited variables
  `{C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]` and
  `{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]`; all four universes
  are explicit and independent.
- P:C→D and S:D→C: `{P : C ⥤ D} {S : D ⥤ C}`.
- P left adjoint to S: `(adj : P ⊣ S)`; no monoidal structure on P and no
  monoidal-adjunction hypothesis is imposed.
- S strong monoidal: `[S.Monoidal]`, providing the forward tensorator μ and
  inverse tensorator δ and inverse unit η of Mathlib's monoidal API.
- The adjunction satisfies the projection formula:
  `[adj.HasProjectionFormula]`. Its `isIso (L : D) (M : C)` field states
  invertibility of exactly `adj.projectionFormulaMap L M`.
- The prescribed maps, not an arbitrary coherent family: the construction sets
  `iso L M := asIso (adj.projectionFormulaMap L M)`. The map definition is
  `(adj.homEquiv _ _).symm
  (S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M))`.
  This is precisely the inverse hom-bijection image of the node's two-arrow
  composite SL⊗M → SL⊗SPM → S(L⊗PM).
- Result: `S.ProjectionFormula P`, namely the existing
  `CategoryTheory.Functor.ProjectionFormula` structure. Its `iso` has type
  `P.obj (S.obj L ⊗ M) ≅ L ⊗ P.obj M` for every L and M.
- Naturality in L is the `natural_left` field, filled by
  `adj.projectionFormulaMap_natural_left`:
  `P.map (S.map f ▷ M) ≫ π' = π ≫ f ▷ P.obj M`.
- Naturality in M is `natural_right`, filled by
  `adj.projectionFormulaMap_natural_right`:
  `P.map (S.obj L ◁ g) ≫ π' = π ≫ L ◁ P.map g`.
- The unit clause is `unit := adj.projectionFormulaMap_unit`. The field reads
  `π ≫ (λ_ (P.obj M)).hom =
  P.map (Functor.OplaxMonoidal.η S ▷ M ≫ (λ_ M).hom)`.
  Mathlib's oplax η is the blueprint's inverse unit ε; composition is written
  left-to-right in Lean.
- The associativity clause is `assoc := adj.projectionFormulaMap_assoc`:
  `π ≫ (α_ L L' (P.obj M)).hom =
  P.map (δ S L L' ▷ M ≫ (α_ (S.obj L) (S.obj L') M).hom) ≫
  π' ≫ L ◁ π''`. This is exactly the source's associativity equation with
  its stated domains and orientation.

### Dependencies and source provenance

Both statement-dependency JSONs currently have neither `lean` nor
`mathlib_match`. Nevertheless their exact notions are already available in the
same published framework module: `Adjunction.projectionFormulaMap` and
`Adjunction.HasProjectionFormula` (lines 107–177) render
`def-sfb-adjunction-has-projection-formula`, and
`Functor.ProjectionFormula` (lines 78–101) renders
`def-sfb-projection-formula`. Their full signatures, fields and docstrings were
read. This delivery attaches the item's existing construction; it does not
state or change either dependency node. There is no missing Lean object to
construct. The prerequisite records can separately be attached to these names.

The module is among the 51 side-published framework files documented in
`coord/pefw-upstream-framework.md`. It is absent from the older local
slopmaster2 tree but present in `lean/WeilConjectures` and the current server
source returned by the prescribed wrapper. `branch: slopmaster2` follows the
existing-record validator's required convention for `WeilConjectures.*` modules;
`lean.note` makes this source distinction explicit.

### Edge cases

No symmetry, braidedness, Cartesian product, rigidity, additivity, nonemptiness,
or zero object is assumed. Both categories retain independent object and Hom
universes. Monoidal units and all L,M are covered without exclusions. Taking
L to be the tensor unit gives exactly the unit field; taking L or L' to be the
unit in the associativity field introduces no new hypotheses. Zero objects,
when present, are included by the unrestricted object quantifiers. An identity
adjunction and terminal monoidal category are included. The isomorphism data
uses the prescribed maps and their inverses, with no arbitrary family choice.

### Searches

Search output is recorded in sandbox `searches.jsonl`.

- `msearch.py ... leanfinder`, query “An adjunction with a strong monoidal right
  adjoint defines a coherent projection formula”: eight hits, including
  monoidal-adjunction constructions and `frobeniusMorphism`, none matching the
  unrestricted coherent structure.
- `msearch.py ... loogle`, query `"frobeniusMorphism"`: eight hits; inspected
  Mathlib `CategoryTheory/Monoidal/Closed/Functor.lean:35–70`. Its construction
  assumes Cartesian monoidal categories and is not this general construction.
- `msearch.py ... leansearch`, query “A strong monoidal right adjoint with
  invertible projection maps defines a coherent projection formula”: eight
  hits concerning monoidal adjunctions and strong monoidal functors, no exact
  Mathlib match.
- `msearch.py ... grep`, query
  `projectionFormula|ProjectionFormula|projection_formula`, subdirectory
  `CategoryTheory`: zero Mathlib hits.
- `rg` of `projectionFormula|ProjectionFormula|projection_formula` in the
  slopmaster2 source, `lean/Sheaf`, and side `lean/WeilConjectures` located
  specialized geometric statements and the exact general upstream module.
  Focused declaration search in the category-theory directories identified
  `Functor.ProjectionFormula`, `Adjunction.projectionFormulaMap`,
  `Adjunction.HasProjectionFormula`, and `Adjunction.projectionFormula` there.
- Node-id search in the old slopmaster2 source returned no hit; its
  category-theory `projectionFormula` search also returned no hit. Search of
  `dag/lean_names_upstream.json` yielded no recorded attachment for the item.
- Inspected all DAG records whose existing module is the exact upstream module:
  none were recorded at inspection time. Thus no second definition is needed.

### Validation

The sandbox-only `scratchpad/ExistingChecks.lean` imports the published module,
checks all four declarations with `#check @...`, and prints the axioms of the
item declaration. It is compiled only by `scompile.py` and is not delivered.
The probe compiled cleanly with no warnings. Its axiom output was exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` was reported.
The required `deliver2.py Q14 def-sfb-adjunction-projection-formula --no-push`
additionally checks the existing declaration in its own compiler probe and runs
the server preflight. The independent second reader will record its own reading
and deliver; this worker does not write that section or push.

## Second reading by Q14

I reread the item node, its blueprint source place (`sk-def-sfb-transport`, clause 4
and node order 1605), both statement dependencies, and the complete declaration in
`WeilConjectures/CategoryTheory/ModuleObjects/ProjectionFormula.lean`.

The node's objects and hypotheses match the Lean declaration item by item:

* The two arbitrary monoidal categories are the independent universes and instances
  `{C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]` and
  `{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]` (source lines 72--76).
* The functors are `P : C ⥤ D` and `S : D ⥤ C`, and the adjunction is the explicit
  `adj : P ⊣ S` (lines 105--109). No monoidality of `P` is assumed.
* The strong monoidal hypothesis is `[S.Monoidal]`, exactly the strong structure used
  by the dependency definition (line 109); no symmetry, braiding, closedness, or
  finiteness assumptions are added.
* `[adj.HasProjectionFormula]` is the node's assertion that every canonical map is an
  isomorphism. Its field is `isIso (L : D) (M : C) :
  IsIso (adj.projectionFormulaMap L M)` (lines 176--179).
* The conclusion is `S.ProjectionFormula P`, whose `iso L M` has exactly the required
  type `P.obj (S.obj L ⊗ M) ≅ L ⊗ P.obj M` (lines 82--99). The construction uses
  `asIso (adj.projectionFormulaMap L M)`, so it is the prescribed mate and not an
  arbitrary family.
* The four remaining clauses are supplied verbatim by the existing fields:
  `natural_left := adj.projectionFormulaMap_natural_left`,
  `natural_right := adj.projectionFormulaMap_natural_right`,
  `unit := adj.projectionFormulaMap_unit`, and
  `assoc := adj.projectionFormulaMap_assoc` (lines 184--189). In particular, the
  unit equation uses `Functor.OplaxMonoidal.η S`, and the associativity equation uses
  `δ S L L'` and the intermediate object `S.obj L' ⊗ M`, with the same composition
  orientation and quantifier order as the node.

The dependency declarations were also checked. `Functor.ProjectionFormula` is the
full structure named by `def-sfb-projection-formula` (lines 82--101), while
`Adjunction.projectionFormulaMap` and `Adjunction.HasProjectionFormula` are exactly
the canonical map and invertibility predicate named by
`def-sfb-adjunction-has-projection-formula` (lines 112--118 and 176--179). No
private replacement or specialization is being used. These dependency records are
not changed here because this delivery attaches the item's already published
construction; their separate stage-2 attachments remain independent items.

Edge cases are covered by the unrestricted binders: empty or terminal categories,
identity adjunctions, zero objects, unit objects, and all choices of `L`, `L'`, and
`M` (including `L = 𝟙_ D` and `L' = 𝟙_ D`) are allowed. The independent object and
morphism universes do not exclude any case. No nonemptiness, characteristic,
additivity, rigidity, or Cartesian assumption appears.

For the duplicate search I reran the prescribed LeanFinder search for a canonical
coherent projection formula and inspected its monoidal-adjunction hits; none has the
general statement. I also searched Mathlib and both project source trees with
`rg` for `ProjectionFormula`, `projectionFormulaMap`, and `HasProjectionFormula`.
The only exact declaration is the side-published framework module above; Mathlib's
`frobeniusMorphism` is Cartesian-only and is not a match. The search log records the
LeanFinder query and the earlier LeanSearch, Loogle, and grep results.

No mismatch was found, so no source-based correction or Lean change was necessary.
The only delivery change remains the existing declaration record for
`CategoryTheory.Adjunction.projectionFormula`; the existing-check probe compiled
cleanly with axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
