## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.etale_injective_of_small_extensions` by a complete Lean
combination proof. The statement and its existing public imports are unchanged.
The proof applies the assumed extension property to subobjects of a concrete
small-valued generator, builds the corresponding lifting squares into `T → 0`,
and uses Mathlib's `IsGrothendieckAbelian.generatingMonomorphisms_rlp` and
`injective_iff_rlp_monomorphisms_zero`.

Added three modules:

- `Sheaf.AlgebraicGeometry.EtaleSmallGenerator`: the real construction
  `AlgebraicGeometry.Scheme.etaleSmallGenerator`, a coproduct of sheafified free
  Yoneda objects on a `u`-small model of the affine etale site, transported through
  the two comparison equivalences. No data is chosen from an unproved theorem.
- `Sheaf.AlgebraicGeometry.EtaleSmallGeneratorSeparating`: the proved theorem
  `AlgebraicGeometry.Scheme.etaleSmallGenerator_isSeparator`. Its proof detects
  group maps using the integer group, applies Mathlib's free-Yoneda generator
  theorem, and transports separation through both equivalences.
- `Sheaf.AlgebraicGeometry.EtaleSmallGeneratorSections`: the remaining section-size
  bound, with a complete proof plan identifying the large construction with its
  coefficient-lifted small version and using affine covers to bound all sections.

The item's new imports are proof-only. The proved upstream Grothendieck-abelian
instance in `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` is used at
universe `u + 1`; the smaller-coefficient instance of `AffineEtale` does not suffice.
Updated the item's DAG proof and added nodes for the construction, separation
property, and section-size bound. The unit `sk-prop-h2` and its route stay intact.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.etale_injective_of_small_extensions`
(node `lem-sc-etale-small-injective-criterion`). The proof has no local sorry.

Also proved `AlgebraicGeometry.Scheme.etaleSmallGenerator_isSeparator`
(node `lem-sc-etale-small-generator-separating`) and its private
`integer_isSeparator` helper. The definition `etaleSmallGenerator` contains no
sorry.

One new hole remains, and it is the only textual sorry in the delivery:
`AlgebraicGeometry.Scheme.etaleSmallGenerator_sections_small`
(node `lem-sc-etale-small-generator-sections`). Its entire proof is `by sorry`.
This is a strict part of the geometric argument: it bounds the values of a fixed
constructed generator; it does not mention T, the extension hypothesis, or
injectivity. One original hole closed and one hole added is a decomposition,
with net zero holes, not a completely sorry-free proof of the original theorem.

All four modules compile locally in dependency order without warnings. The
empty scheme, empty etale objects, non-quasi-compact etale objects, and the zero
sheaf require no additional hypotheses. In particular, the section-size proof
plan uses all affine opens rather than a finite affine cover.

## No longer needed

No existing import or module was removed from the original item. The old direct
proof-dependency edge to `def-weil-pbc-etale-site` is replaced by the dependencies
on the generator construction and its properties; that definition remains a
statement dependency and a dependency of the new generator nodes. Thus no node
or module is pruned from the import closure. An added redundant proof import of
`Mathlib.Algebra.Category.Grp.AB` was removed after checking compilation: the
construction module supplies it already. The second reader also removed the added
proof import `Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties`,
already publicly imported by `EnoughInjectives`. Neither was an original import.

No separate Zorn argument or additional holed generator-extension criterion is
needed. `Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator` was searched
and read but is not imported: the corresponding categorical reduction is already
proved in Mathlib. This is avoidance of an unused possible dependency, not a
claim that this delivery prunes that module from other targets.

## Where the brief, the DAG or earlier work was wrong

The item's original DAG step bundled the geometric universe bound with the
categorical injectivity criterion, while its recorded proof dependencies named
only the site and injectivity definitions. Those definitions do not supply the
geometric bound. This delivery makes the generator construction explicit, proves
its separator property, and isolates only the section-size argument.

Mathlib already supplies the categorical reduction, so a new holed theorem for
that part is unnecessary. Large-valued sheaves require the upstream
Grothendieck-abelian instance at `u + 1`, rather than the Mathlib affine-site
instance specialized to coefficients with homs in `u`.

LeanSearch was attempted and returned Internal Server Error. LeanFinder, Loogle,
local source searches, and direct inspection of the generic Mathlib declarations
were used; the unavailable searches are recorded without an absence verdict.

## New nodes

`def-sc-etale-small-generator` records the concrete definition in
`lean/Sheaf/AlgebraicGeometry/EtaleSmallGenerator.lean`. It uses actual small-model,
sheafification, coproduct and site-comparison operations, with no new hypothesis
and no postponed data.

`lem-sc-etale-small-generator-separating` records the proved separator theorem in
`lean/Sheaf/AlgebraicGeometry/EtaleSmallGeneratorSeparating.lean`. It specializes
Mathlib's free-Yoneda generator result and preserves separation under equivalence.

`lem-sc-etale-small-generator-sections` records the single remaining theorem in
`lean/Sheaf/AlgebraicGeometry/EtaleSmallGeneratorSections.lean`. Its docstring and
DAG give the coefficient-lift/sheafification argument on the small model and the
separatedness embedding into a small product over an affine open covering.

No existing definition or statement was changed, and no forced adaptation or
change record is needed.

## Second reading by U1

1. **Interfaces — pass.** Read all four delivered modules and diffed
   `EtaleSmallInjectiveCriterion.lean` against the repository version. The existing
   declaration signature, docstring and two public imports are byte for byte
   unchanged. Its only changes are proof imports and the proof body. The three
   other modules are new; no existing definition, hypothesis or conclusion changes.
   No change record or forced adaptation is needed.

2. **Proof and axioms — pass as a decomposition.** Independently compiled all four
   modules in dependency order using `lcompile.py`, without errors or warnings,
   and compiled scratch copies with `#print axioms` for every declaration. The
   generator definition and separator theorem use only `propext`, `Classical.choice`
   and `Quot.sound`; the private integer separator uses `propext` and `Quot.sound`.
   The section-size theorem and original injectivity theorem additionally use
   `sorryAx`, as expected from the one named remaining hole. There is no sorry in
   a definition, no forbidden declaration, and no arbitrary witness of an
   unproved existence result. Coproducts, free sheafification and comparison
   equivalences specify objects by their universal properties. In the final proof
   `M.arrow` is monic, `hT` applies to its codomain G, and the second lifting-square
   face is automatic because its target is zero.

3. **Split-off statement — pass.** Read the section-size docstring and both DAG
   steps against the actual construction, Mathlib's `AffineEtale`,
   `CompatiblePlus`, `CompatibleSheafification`, and `Grp.Ulift`. On the small
   model, the arrows of a sieve, matching-family diagrams and set of covering
   sieves are u-small. AddCommGrpCat's lift preserves the needed limits and
   colimits. The two lifted versions of the integer coefficient are canonically
   isomorphic, so the free representables, sheafifications and their u-small
   coproduct agree up to isomorphism with the lift of the small-valued construction.
   Uniqueness of sheafification identifies the concrete twice-plus computation
   with the sheafification instance used by the definition. The comparison's
   restriction isomorphisms give the bound on affine objects; sheaf separatedness
   embeds sections on an arbitrary etale U into the product over all its affine
   opens. This index is a subset of the u-small opens of U. Empty U gives singleton
   sections, and no finite-cover assumption enters for non-quasi-compact U.
   Empty X and the zero sheaf cause no exclusion. The statement concerns only
   values of this fixed generator, not T, hT or injectivity, and is strictly a
   part of the argument. Its source and complete proof are in its docstring and
   matching node. It is not a several-minute formalization, so its hole remains.

   Independent searches used LeanFinder for objectwise small abelian
   sheafification, Loogle for `"PreservesSheafification", "ulift"`, and rg with
   small-section and sheafification terminology over Mathlib, upstream and
   lean/Sheaf. LeanFinder returned general small-site results and a module-sheaf
   limit smallness instance, not this transported-generator bound; Loogle had
   zero hits. Direct reading found the generic `sheafifyCompIso` and lift
   preservation results that substantiate the proof plan, but no theorem closing
   the specialized bound.

4. **Route and imports — pass after repair.** Read
   [Stacks 01DO](https://stacks.math.columbia.edu/tag/01DO) and
   [03EW (3)](https://stacks.math.columbia.edu/tag/03EW), Mathlib's
   `Sheaf.isSeparator`, `generatingMonomorphisms_rlp`, and
   `injective_iff_rlp_monomorphisms_zero`. They give the precise free-representable
   and categorical reductions used here. The proved Mathlib reduction is shorter
   than importing the still-holed
   `Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator`; that module is
   correctly avoided. Removed the redundant added `LiftingProperties` import
   supplied by `EnoughInjectives` and recompiled. The construction's public imports
   support its exposed definition body, while the item's added imports are
   proof-only. The old direct site-definition proof edge is accounted for under
   No longer needed; the site definition remains reachable. No original module is
   pruned. Read `dag/units/sk-prop-h2.json`: its Kummer/Picard/Brauer route is untouched,
   and its existing empty `realized` entries are not changed or bypassed by this
   auxiliary injectivity argument.

5. **Nodes — pass.** Compared each node with its actual declaration and proof.
   The original node's proof records the concrete G, its separator and size facts,
   hT on subobjects, the Grothendieck-abelian instance at u+1, and the two lifting
   results in the exact order used in Lean. Its proof_deps is the union of the
   cited uses. The new definition node has empty proof/proof_deps; the separator
   node records the integer helper, free-Yoneda result and both equivalences; the
   remaining node records the coefficient-lift and affine-cover size argument.
   All three new nodes have sources, searches, created/blueprint records, Lean
   declarations, and the item's chapter and unit. The existing statement and
   stmt_deps are unchanged.

Second-reading changes: removed one redundant proof import; supplied source,
blueprint tag and title in the three new module docstrings; clarified the old
site-definition edge in No longer needed; recorded this independent reading.
No mathematical statement or definition was changed. One original hole is
closed and one new hole is left: this delivery remains a net-zero decomposition.
