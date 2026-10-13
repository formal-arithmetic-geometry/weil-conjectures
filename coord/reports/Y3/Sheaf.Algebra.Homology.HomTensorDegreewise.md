## What changed

Replaced the sorry of `CategoryTheory.homTensorDegreewise_exists` with a Lean proof
combining two strictly separate parts of the degreewise argument: the
forward currying construction and a reverse map with both inverse identities.
The proof explicitly packages the inverse as `IsIso` and proves uniqueness by
composition with the same reverse map: c = c ≫ (b ≫ a) = (c ≫ b) ≫ a = a.
No original signature or visibility was changed. The three existing names are now abbreviations
of their identical constructions in a shared equation module,
which is publicly imported to expose those bodies.
Added proof-only imports of `Sheaf.Algebra.Homology.HomTensorDegreewiseConstruction`
and `Sheaf.Algebra.Homology.HomTensorDegreewiseIso`. Updated the original node's
proof, proof_deps and proof_origin to this reduction.

Read Stacks Tags [0A90](https://stacks.math.columbia.edu/tag/0A90) and
[03EO](https://stacks.math.columbia.edu/tag/03EO) online because the cited local
sites-cohomology.tex is absent on this machine. Inspected the existing Hom-complex
product specification, tensor-Hom adjunction, tensor sheafification comparison,
total-tensor coproduct constructor, and internal-Hom coproduct-fan statement.
The new statements use a shared equation interface extracted verbatim from the
original definitions. The original `homTensorProjection`, `homTensorSectionMap`
and `HomTensorCurryCondition` names are abbreviations of the corresponding constructions
in `HomTensorDegreewiseEquation`. These are definitionally equal to their old
bodies. This refactor avoids an import cycle and prevents repeated expansion of
large category constructions when applying the two intermediate theorems.
The shared module has no sorry and chooses only the specified Hom projections.


## Proved and sorry left

Closed upper hole: `CategoryTheory.homTensorDegreewise_exists`
(node `lem-sc-hom-tensor-degreewise`). This is a decomposition, not a completed
sorry-free proof of the mathematical comparison. There are no sorries remaining
in the item's module.

Added lower holes, both public theorems with proof exactly `by sorry`:

- `CategoryTheory.homTensorDegreewise_construct`, node
  `lem-sc-hom-tensor-degreewise-construction`, in
  `Sheaf.Algebra.Homology.HomTensorDegreewiseConstruction`: existence
  of the forward map, with no uniqueness, inverse or invertibility conclusion.
- `CategoryTheory.homTensorDegreewise_inverse`, node
  `lem-sc-hom-tensor-degreewise-iso`, in
  `Sheaf.Algebra.Homology.HomTensorDegreewiseIso`: constructs a reverse morphism
  with both identity equations, simultaneously for every forward map satisfying its equation;
  does not assert existence of a forward map.

The delivery closes one hole and adds two (net minus one before further pruning).
The original chosen-map definition continues to depend on a uniquely specified
object; it does not choose an arbitrary witness of mere existence. No data
construction contains a sorry.

Edge cases checked mathematically: zero complexes and the zero coefficient ring
have zero comparison objects and their unique identity/inverse morphisms;
complexes concentrated in single, possibly negative, degrees reduce to ordinary
localized tensor-Hom currying. The general statement uses direct sums in the
total tensor and products in Hom, so no boundedness or finite-support assumption
on Hom families is added. Sections of sheaf tensors need not be global pure-tensor
sums; every equality is tested before sheafification and on every localized site.

## No longer needed

Removed the redundant direct public imports `Sheaf.Algebra.Homology.HomComplex`
and `Sheaf.Algebra.Homology.KFlat` from the item. The publicly imported equation
module supplies both transitively, preserving the public interface. No module
is made unreachable by this removal.
The three original proof dependencies `def-pur-hom-complex`,
`def-pc-tensor-complex-sheaves` and `lem-pc-sheaf-modules-tensor-closed` remain needed
inside the new construction and inverse plans; none is claimed pruned.
No blueprint unit statement or realized step is bypassed. The unit record
`sk-thm-picard-duality` has no realized node for this degreewise support lemma.

## Where the brief, the DAG or earlier work was wrong

The original node's one-step proof plan does not supply a declaration for the
forward currying construction or its reverse. The available tensor-Hom equivalence
is a module-level adjunction; connecting it to the selected Hom product projections
and localized pure-tensor equation is substantial glue. The existing
`homTensorLocalized_ext` theorem cannot be imported into this item: its module
publicly imports this item, and doing so would create a cycle. Its general
extensionality statement was therefore not duplicated as a new holed lemma.

The ancestor lookup for `lem-sc-hom-tensor-degreewise` reports a broken created.item
chain (its item is a module name); the next node `lem-sc-derived-hom-tensor-total`
records `lem-sc-finite-duality` as the blueprint ancestor. The new nodes preserve
that ancestry, with the intervening degreewise, total-Hom and derived-adjunction
nodes named in via. No existing blueprint field was changed.

LeanSearch returned HTTP 500, recorded as unavailable. LeanFinder returned generic
homological tensor declarations; Loogle returned the monoidal closed API; grep
found tensor-Hom equivalences but no exact theorem for these chosen Hom complexes.
All searches are recorded in searches.jsonl and copied accurately to the new nodes.

## New nodes

`lem-sc-hom-tensor-degreewise-construction` isolates existence of the forward map. Its
proof plan constructs restriction-compatible bilinear evaluations, descends
through tensor sheafification, and combines coproduct/product components. Its Lean equation is the
existing curry predicate expanded definitionally.

`lem-sc-hom-tensor-degreewise-iso` isolates the reverse construction and the two
inverse calculations. It constructs one reverse map independently of a forward map,
and proves both identity equations for every map with the evaluation equation. The upper proof
uses these identities to construct `IsIso` directly. Both nodes cite the original
source, have their complete proof in words, and belong to the original chapter
and unit. The shared equation refactor is recorded in the change record below; no forced
adaptation is needed.

`def-sc-hom-tensor-degreewise-equation` records the shared, unchanged equation and
its two auxiliary constructions, extracted solely for import direction and compile
performance. The old names are abbreviations of the corresponding new definitions;
there is one actual construction of each. Change record:
`coord/changes/hom-tensor-degreewise-equation.md`.

The shared equation extraction changes no downstream statements. The change
record lists the transitive importers and their claim holders; no adapted
module is delivered.


## Earlier second reading (a previous round; superseded)

1. Compared the item with the repository by diff and the declaration scanner:
   all six existing declaration signatures and their visibility are unchanged.
   The three abbreviations and their bodies are covered by the change record. Compared
   the extracted bodies byte for byte after renaming: all three match. Thus the
   original abbreviations unfold to the same data and predicate; no target meaning
   changes. Repaired the change record's Old/New blocks to contain the exact
   declarations, including noncomputable modifiers and original whitespace.
2. Compiled all four delivered modules in import order with lcompile.py: no
   errors or unlisted holes. A scratch #print axioms probe against the sandbox
   overlay reports only propext, Classical.choice and Quot.sound for the
   equation and auxiliary definitions; the upper theorem, chosen map and its
   specification additionally have sorryAx from the reported lower holes.
   The only added holes are the two public named
   theorems reported above. No forbidden declarations or data holes occur.
   The chosen upper map comes from unique existence; the new projections use
   the already proved homComplex_exists, not an unproved arbitrary existence
   assertion. The upper proof's IsIso witness and uniqueness calculation have
   the correct directions. Separate scratch attempts to elaborate duplicate
   original constructions and rfl checks exceeded the 60-second limit; those
   are not delivered. Exact body comparison supplies the refactor check.
3. Read both split statements and their full docstring arguments. The forward
   statement asserts only existence and the equation. The reverse statement
   constructs b independently and proves inverse laws conditional on a;
   it asserts no existence of a. They are true proper parts of the construction,
   and neither restates the upper theorem. Zero objects, the zero ring, and
   single-degree complexes (including negative degrees) cause no exceptions;
   infinite complexes use coproducts for tensor and products for Hom, with
   equality tested locally before sheafification. Repeated searches using
   LeanFinder, Loogle and grep with different terms; inspected tensorHomEquiv,
   internalHomCoproductFanIsLimit, homTensorSummandRestriction_ext and
   homTensorLocalized_ext. No direct replacement closes these construction
   holes in a few minutes; the last theorem imports this item and would cycle.
   Checked the cited Stacks sources: [0A90](https://stacks.math.columbia.edu/tag/0A90)
   and [03EO](https://stacks.math.columbia.edu/tag/03EO).
4. Reviewed the shortest route and imports. Removed the item's redundant direct
   public HomComplex and KFlat imports: the public equation module reexports
   both. Construction and inverse imports remain proof-only. No old proof
   dependency module becomes unreachable: all three old dependencies are used
   in the lower plans. No unit realization is bypassed; the unit has no realized
   node for this support lemma. The result remains a decomposition: one closed
   upper hole, two added lower holes, net minus one before any ledger pruning.
5. Checked every delivered node's statement, declaration, source, proof steps,
   proof_deps union and proof_origin against the Lean and intended remaining
   argument. Added def-sc-hom-tensor-degreewise-equation to the statement
   dependencies of both new theorem nodes, since their signatures use it.
   The upper node records precisely the two lemmas used by its proof. The shared
   definition node has no proof holes. Existing immutable node fields and unit
   records are unchanged.

Second reading changed redundant imports, exact change-record quotations,
new theorem nodes' statement dependencies, and this report; it did not change
any theorem statement, definition construction, or proof argument.

Repair of reviewer X-28c27's return (head 28c2781c8):

- H4: changed `homTensorProjection`, `homTensorSectionMap`, and
  `HomTensorCurryCondition` to abbreviations, preserving every binder, type,
  body and visibility. Updated the change record's New blocks accordingly.
- C1: the forward construction's descent step and the inverse's second-composite
  step now explicitly cite `def-pur-sheaf-tensor-product` and
  `def-weil-presheaf-modules-sheafification`; both lower nodes' `proof_deps`
  include these citations. These supply the tensor sheafification comparison
  and sheafification adjunction used by the lower proof plans, beyond the
  three previously cited Hom, total-tensor and closedness nodes.


## Second reading by Y3

1. **Interface and definitions: pass.** Independently diffed the item against
   the read-only repository version and compared declaration records. The three
   theorem/map signatures are byte-for-byte unchanged. The other three declared
   types and visibility are unchanged; their change from `def` to `abbrev` is
   explicitly covered by `coord/changes/hom-tensor-degreewise-equation.md`.
   Compared all three extracted bodies programmatically, replacing only the
   two auxiliary identifier names: each is byte-for-byte identical to its
   original body. The change record contains the actual Old/New declarations.
   Thus the equation, projection choices, section map, and target meanings
   are preserved. No forced adaptation is delivered.
2. **Proof and axioms: pass with the two declared lower holes.** Independently
   compiled all four modules with `lcompile.py --all`: equation 41.9 s,
   construction 3.2 s, inverse 3.5 s, item 7.1 s; no errors or warnings.
   Compiled a scratch copy with explicit `#print axioms` for all eleven
   delivered declarations, against the sandbox overlay. Every declaration
   uses only propext, Classical.choice and Quot.sound, with sorryAx additionally
   in the two lower theorems and the upper existence/map/specification that
   depend on them. Both holes are public named theorems, exactly `by sorry`;
   no forbidden declarations or data holes occur. The upper uniqueness proof
   uses c ≫ b = identity and b ≫ a = identity in the correct directions.
   Its chosen map uses unique existence; the shared projection uses the
   already proved Hom construction, not arbitrary unproved existence.
3. **Split statements: pass.** Read both full statements and docstring proofs.
   Forward existence omits uniqueness and invertibility; the reverse lemma
   asserts no forward existence and constructs one reverse map independently.
   They are proper parts of the argument, not renamed copies of the item.
   Checked zero complexes, the zero ring, negative degrees and complexes
   concentrated in single degrees. Arbitrary degree families use products
   in Hom and coproducts in tensor; no boundedness is required. The quantifier
   over localized objects permits evaluation at the local identity object,
   and equality descends from pure tensors before sheafification, so it does
   not assume that sheaf tensor sections are global pure-tensor sums.
   Repeated LeanFinder, Loogle and grep searches with different terms, and
   searched repository Lean sources. Inspected internalHomCoproductFanIsLimit,
   tensorHomEquiv, homComplex_exists and the downstream localized extensionality
   API. None directly proves either remaining construction in a few minutes;
   importing the downstream API would cycle. Checked the source statements
   at https://stacks.math.columbia.edu/tag/0A90 and
   https://stacks.math.columbia.edu/tag/03EO.
4. **Route and pruning: pass.** The upper proof combines precisely the forward
   and inverse parts. Its two construction imports are proof-only; the shared
   equation import and its HomComplex/KFlat imports supply public signatures
   and definition bodies. The two removed direct imports remain publicly
   available transitively. All three old proof dependencies remain necessary
   in the lower plans; no module is claimed pruned or made unreachable.
   Read the unit record: no realized step for this support lemma is bypassed.
   This remains a decomposition: homTensorDegreewise_exists closed, the two
   lower holes added, net minus one before any ledger pruning.
5. **DAG consistency: pass.** Checked every node against its Lean declaration,
   source, statement dependencies, proof steps and proof_origin. For each node
   proof_deps equals the union of the steps' uses. The upper node changes only
   proof, proof_deps and proof_origin. Both lower nodes now explicitly include
   tensor sheafification and its adjunction among their dependencies, as
   required by the earlier return. New nodes contain the requested source,
   search, creation, blueprint, chapter, unit and Lean records.

This second reading added this independent review and repaired the change-record
Users table after preflight found a newly landed user,
Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents. Read that module:
its component formula uses homTensorProjection at the unchanged declared type,
so the definitionally equal alias needs no adaptation. No Lean or node repair
was needed. The scratch axiom probe is outside the
set of delivered Lean modules. No additional hole was closed or added.
