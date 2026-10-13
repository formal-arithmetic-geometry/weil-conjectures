## What changed

The statement and visibility of
`AlgebraicGeometry.exists_canonicalEvaluation_open_restriction` are unchanged.
Its proof now constructs the two comparisons from a compatible strong monoidal
restriction structure and Hom comparisons. The fully proved private helper
`closedMonoidal_evaluation` transports evaluation of the dual using the inverse
unit comparison, applies injectivity of the tensor-Hom equivalence, and proves
the remaining equation with associator naturality, tensorator naturality,
monoidal associativity and right-unit coherence. No data is chosen in a definition.

The new module `Sheaf.AlgebraicGeometry.OpenRestrictionClosedMonoidal` states the
remaining representative/localization construction. Its theorem supplies tensor
and unit coherence and the Hom uncurrying equation for arbitrary objects. It does
not restate the original dual-evaluation square. Its source and complete proof in
words are in its docstring and its new DAG node. The parent node records the new
route. The original module imports this new module privately.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_canonicalEvaluation_open_restriction`
(node `lem-pc-canonical-evaluation-open-restriction`).

Added one hole:
`AlgebraicGeometry.exists_openRestriction_closedMonoidal`
(node `lem-pc-open-restriction-closed-monoidal`).
There are no other sorries in the delivered modules and no sorry in the private helper.
This is a decomposition, not a completed proof of the entire representative theory:
one original hole is closed and one construction hole is added (net zero).

## No longer needed

Removed the redundant public import `Mathlib.CategoryTheory.Monoidal.Functor`
from the new module (all its statement types remain publicly available through
`CanonicalDerivedTensorHom`).

Removed these direct proof imports from the original module:

- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
  (also removed from the new module after scratch compilation showed it redundant);

- `Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel`;
- `Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor`;
- `Sheaf.Algebra.Homology.HomComplexRestrictOpen`;
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`;
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`;
- `Sheaf.Algebra.Homology.KFlatResolution`.

Their nodes remain needed by the construction in the new module, whose imports
retain them. None is claimed pruned from the targets' import closure. The parent's
proof dependencies are now the new construction node and
`def-pc-canonical-derived-tensor-hom-bijection`. Every removed parent proof dependency is:
`def-pc-derived-category`, `def-pc-scheme-derived-tensor-structure`,
`def-pur-derived-internal-hom`, `lem-pc-kflat-resolution`,
`lem-pc-open-restriction-kflat-model`, `lem-pc-open-restriction-total-tensor`,
`lem-sc-derived-internal-hom-restrict-open`, `lem-sc-derived-k-injective-restrict-open`,
`lem-sc-hom-complex-restrict-open`, and
`lem-weil-pbc-module-restriction-open-immersion-colimits`. They remain dependencies
of the new construction node; none is pruned from the import closure. No unit statement or unit step
is bypassed; `sk-thm-picard-duality` has no realized node binding on this item.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing
`exists_derivedRestriction_tensorHom_coherence` does not apply directly: it uses
a derived functor of a composite and one common localization universe, requires
localizations for every open, and supplies only tensor naturality and uncurrying.
The present statement needs the composite of two derived functors in independently
specified universes and the tensor-unit and associator laws. The new construction
node states those missing data together, rather than trying to use unrelated
object isomorphisms. The generic final calculation demonstrates exactly why these
coherence laws are needed.

The local Stacks source path is absent on this machine. The cited
[08DJ](https://stacks.math.columbia.edu/tag/08DJ) and
[08DL](https://stacks.math.columbia.edu/tag/08DL) were read online. The new proof
origin records that its explicit coherence argument is written by an agent.
Mathlib searches found generic monoidal and Cartesian closed functor results,
not the required derived restriction comparison. LeanSearch returned HTTP 500
and is recorded as unavailable. Empty opens and zero objects impose no
nonvanishing hypothesis: all structure maps are the corresponding isomorphisms,
and the categorical calculation uses only category and monoidal laws.

## New nodes

`lem-pc-open-restriction-closed-monoidal` in
`dag/nodes/sec-picard-framework/lem-pc-open-restriction-closed-monoidal.json`
is the construction part of steps 1–3 and the uncurrying part of step 4 of the
parent node. It supplies a strong monoidal structure on the specified composite
restriction and compatible internal-Hom comparisons; the derived dual-evaluation
square is proved separately in the original module. Its Lean module is
`Sheaf.AlgebraicGeometry.OpenRestrictionClosedMonoidal`. No existing interface
changed and no forced adaptation or change record is needed.


## Second reading by P4

1. **Existing interface: pass after repair.** Compared the original module and parent
   node against the repository. The sole existing public theorem's entire signature,
   from its name through the conclusion, is byte for byte unchanged after removing an
   extra space before `:= by`. Its docstring and local instance definition are unchanged.
   The parent node changes only `proof`, `proof_deps`, and `proof_origin` semantically;
   JSON Unicode escaping is only serialization. No target, definition, public import,
   or existing visibility was changed. No change record is required.

2. **Kernel proof: pass, with the declared construction hole.** Compiled both modules
   in import order with `lcompile.py`. Scratch copies with explicit `#print axioms`
   showed `closedMonoidal_evaluation` uses exactly `propext`, `Classical.choice`, and
   `Quot.sound`; the two public theorems additionally use `sorryAx`. Scanned both
   delivered sources: the new construction theorem is the only remaining `sorry`;
   no forbidden declaration or hollow definition exists. The main proof obtains
   structure inside a theorem, never defines data from a mere unproved existence.
   Read the helper throughout: `d` uses the inverse unit comparison in the Hom's
   covariant variable, `a` the inverse tensorator followed by `id tensor d`, and
   `b = h K N`. The counit equation `hd` follows from first/third-variable
   naturality and `hh` on the identity. Injectivity of `f` reduces the target to
   associator naturality, the monoidal associator law, tensorator naturality, and
   right-unit coherence, all proved by the listed Mathlib rewrites.

3. **Split statement: pass as decomposition, not net proof progress.** Read
   [Stacks 08DJ](https://stacks.math.columbia.edu/tag/08DJ),
   [08DL](https://stacks.math.columbia.edu/tag/08DL), and
   [06YH](https://stacks.math.columbia.edu/tag/06YH). The new theorem keeps arbitrary
   unbounded derived objects, arbitrary opens, and the separately specified over-site
   and standard open-scheme localization universes. It asserts the restriction
   construction and uncurrying law, leaving the nontrivial dual-evaluation calculation
   to the fully proved helper; it is not a renamed copy of the target. Empty opens
   give the zero module category, where the unit and all comparisons still exist;
   zero inputs give zero tensor and Hom objects; the full open gives restriction
   equivalent to identity even with different localization universes. No perfectness,
   boundedness, or nonvanishing is needed. Its docstring supplies the representative
   argument. Repeated LeanFinder search for strong monoidal preservation of internal
   Hom evaluation, Loogle for the right-unitor law, and grep for monoidal restriction
   and uncurrying restriction. Results were generic groupoid/Cartesian closed-functor
   facts and scalar restriction, not this construction. Searched `lean/Sheaf`,
   `lean/WeilConjectures`, and the upstream checkout with evaluation/restriction words.
   Read `exists_derivedRestriction_tensorHom_coherence` in full: its functor is a
   derived composite, its localization universe is common, and its conclusion lacks
   the monoidal unit and associator laws, so it is not a direct replacement.

4. **Shortest route, imports, and unit route: pass after repair.** The final categorical
   calculation needs neither a second new lemma nor the old representative imports
   in the parent. Removed the redundant private `ExactFunctor` import from both
   modules after both scratch files compiled without it. A further scratch compile showed that the new module's direct public import
   of `Mathlib.CategoryTheory.Monoidal.Functor` was redundant; removed it. The remaining
   public import of `CanonicalDerivedTensorHom` supplies all statement types, including
   `R.Monoidal`, transitively; construction dependencies remain private. Expanded `No longer needed` to name
   every removed parent proof dependency, including definitions. None is removed from
   the target import closure: one hole closed, one added, net zero. Inspected
   `dag/units/sk-thm-picard-duality.json`: its `realized.statement` and sole realized
   step are empty, and the item lies below its finite-duality argument. No unit route
   is bypassed or changed. The literature unit text is not installed locally; its
   full statement and step are present in that unit JSON.

5. **DAG versus Lean: pass after repair.** Parent step 1 uses exactly the new theorem;
   step 2 records the helper's actual construction and cancellation calculation.
   The new node's four steps describe over-equivalence/localization, tensor and unit,
   Hom restriction, and uncurrying. Read each imported statement: K-flat resolution,
   `openRestriction_isKFlat`, `openRestriction_totalTensor_iso`,
   `homComplex_restrict_open`, `kInjective_of_restrict_open`, and
   `derivedInternalHom_restrict_open` provide the corresponding representative facts.
   Added the previously uncited `lem-pur-hom-kflat-into-kinjective` to step 4 and its
   private import, since representability of maps into Hom uses precisely that theorem.
   For step 2 added `lem-pc-open-restriction-tensor-natural` for naturality and the
   separate proved `lem-pc-adjoint-module-pullback-monoidal` for unit/associator laws,
   with their private imports. Thus coherence is taken from a statement that actually
   supplies it, not inferred from a mere objectwise isomorphism or another node's
   proof. The new node has its source, complete proof steps, exact Lean signature,
   recorded searches, creation metadata, chapter/unit, and blueprint ancestry;
   `proof_deps` is exactly the union of step citations. The cross-unit monoidal
   pullback and K-injective Hom facts are generic proved tools, not alternate unit
   arguments. No split hole could be closed in a few minutes from existing statements.

Second reading changed: signature whitespace, redundant private imports, missing
construction dependency citations/imports and docstring explanation, and the complete
list of removed parent dependencies. The working final-square proof was retained.
