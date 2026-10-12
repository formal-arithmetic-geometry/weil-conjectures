## What changed

Corrected the returned delivery's false arbitrary-comparison theorem. The disputed block was deleted and the proved degree-zero normalized existence construction is now the public `fullAffineEtale_cohomology_comparison_point` theorem with the required blueprint. The all-degree comparison proof obtains its zero-degree component from this theorem. Updated the comparison-point node, parent proof dependency, and change record.

## Proved and sorry left

Eight existing holes are closed with unchanged statements (names are in namespace
`AlgebraicGeometry.Scheme`):

- `fullAffineEtaleInclusion_continuity_sheaf_condition`
- `fullAffineEtale_special_cocontinuity`
- `fullAffineEtale_sets_equivalence`
- `fullAffineEtale_ab_equivalence`
- `fullAffineEtale_cohomology_comparison`
- `fullAffineEtale_cohomology_base_left`
- `fullAffineEtale_cohomology_base_right`
- `fullAffineEtale_cohomology_base`

The old false `fullAffineEtale_cohomology_comparison_point` is retired and replaced
under the same name by a proved normalized-existence statement. This is a statement
repair, not a proof of its former statement, and is excluded from the eight above.
Of ten original holed declarations, eight keep their statements and receive proofs,
one is repaired, and one remains open. No new holes or split-off statements are added.

The one remaining hole is `fullAffineEtale_cohomology_comparison_data`, node
`lem-weil-pbc-affine-etale-cohomology_comparison_data`. Its unchanged statement has a
source and complete mathematical proof in its docstring. The main comparison and
right/base cohomology theorems have closed bodies but still depend on this hole;
their axiom sets contain `sorryAx`. The four site lemmas above, the corrected
comparison-point theorem, and base-left use only `propext`, `Classical.choice`, and
`Quot.sound`. The already-proved continuity instance and conjunction of equivalences
also have only those axioms. This module is not fully proved.

## No longer needed

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`

The Ext representing-object proof avoids the K-injective bridge for the displayed
base theorem. This does not settle or prune that bridge for other targets.
No whole-library module is claimed unreachable by this delivery.

The old parent node's direct proof-dependency list is replaced by its actual
component lemmas and cohomology definition. Every removed direct dependency is
accounted for below; "retained" means used by the component route or its underlying
Mathlib instances, rather than applied directly by the parent's conjunction proofs.

| Removed direct parent dependency | Disposition |
|---|---|
| `def-pc-scheme` | Scheme definition remains in the signatures; no proof application. |
| `def-weil-pbc-etale-site` | Retained by the component route. |
| `lem-weil-pbc-etale-base-change-finite-limits` | Underlying Mathlib pullback instances; no separate lemma application. |
| `lem-weil-pbc-fibre-product-affine-spectra` | Retained by continuity, special cocontinuity and equivalence components. |
| `def-weil-affine-spectrum` | Underlying `AffineEtale.Spec` image-cover construction; no separate proof application. |
| `lem-weil-pbc-etale-composition-cancellation` | Retained by special cocontinuity and affine-refinement construction. |
| `lem-weil-pbc-etale-covering-base-change` | Existing site/pullback instances; no separate lemma application. |
| `def-weil-pbc-special-cocontinuous-functor` | Retained in special cocontinuity. |
| `lem-weil-pbc-etale-covering-affine-refinement` | Retained by all site comparison components. |
| `def-weil-open-immersion` | No independent obligation; affine-refinement theorem supplies the needed open refinement. |
| `lem-weil-pbc-pretopology-sheaf-condition` | Retained by continuity. |
| `def-weil-pbc-etale-sheaf-of-sets` | Retained in the sets equivalence. |
| `def-weil-pbc-abelian-etale-sheaves` | Retained in the abelian equivalence. |
| `lem-weil-pbc-affine-etale-induced-sheaf-equivalence` | Its Mathlib spectrum-site density supplies small image covers; retained by site components. |
| `lem-weil-pbc-site-equivalence-sheaf-transport` | Unneeded: direct one-hypercover-density comparison replaces transport. |
| `lem-weil-pbc-site-sheaves-enough-injectives` | Retained in the remaining comparison-data proof plan. |
| `lem-weil-pbc-left-exact-injective-resolution-degree-zero` | Unneeded for degree zero: direct Ext-zero/adjunction/Yoneda proof. |
| `lem-weil-pbc-equivalence-injective-resolutions` | Retained in the remaining comparison-data proof plan. |
| `def-weil-pbc-etale-cohomology` | No bridge to this encoding is asserted by the displayed Ext-based base statement. |
| `def-weil-pbc-kinjective-resolutions` | Unneeded by the displayed Ext-based base proof. |
| `prop-weil-pbc-kinjective-resolutions-exist` | Unneeded by the displayed Ext-based base proof. |

The finite affine refinement and image-cover arguments still appear in the Lean.
The unit `sk-thm-p1` and all of its `realized` statement and step nodes are unchanged;
this item is below that unit's route.

## Where the brief, the DAG or earlier work was wrong

The prior delivery retained a statement quantified over an arbitrary all-degree comparison family and requiring degree-zero normalization. Negating a comparison on the constant integer sheaf over a nonempty affine gives a counterexample. The corrected theorem asserts existence of a normalized degree-zero comparison, exactly matching the implemented construction. See `coord/changes/fullAffineEtale_cohomology_comparison_point.md` for the old and new interfaces and its sole user.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

The corrected module compiles through `lcompile.py`. The comparison-point declaration now has the normalized-existence signature and its complete proved body; only `fullAffineEtale_cohomology_comparison_data` retains `sorry`. The main comparison uses the corrected theorem. DAG statement, Lean statement, proof, and parent dependency agree. No signatures other than the mandated correction changed, and no new node was added.

## Second reading by K1

1. **Interfaces — pass after record repair.** Read the full diff against the
repository module and used its declaration parser to compare every existing
signature, then compared their raw source text byte for byte. Removed one extra
space before `:=` in the all-degree comparison signature. The sole changed interface is the explicitly declared correction of
`fullAffineEtale_cohomology_comparison_point`; its change record now contains both
verbatim signatures and a users table. All other signatures and public imports
are unchanged. Read-only downstream search finds no external caller of the
corrected declaration, so no forced adaptation is needed. No target or definition
changes.

2. **Proof and axioms — pass, with the reported open dependency.** Compiled the
module through `lcompile.py --all` without errors or warnings. Compiled a fresh
scratch copy with `#print axioms` for every public theorem. Only the standard
three axioms occur, plus `sorryAx` exactly for comparison-data and the three
results depending on it. Inspected all private constructions: they are real
adjunction, Yoneda, free-abelian, and sections constructions, with no arbitrary
witness extracted from an unproved existence theorem into a definition. There
is one `sorry`, in the named comparison-data theorem, and no forbidden command.

3. **Remaining statements — pass.** There are no new split-off statements. The
unchanged all-degree comparison-data obligation is true by equivalence of sheaf
categories and identity of the corresponding section complexes; its docstring
spells out preservation of injectives, the Ext/sections identification, and
naturality. The empty affine and zero sheaf give zero section groups and no
exception. Degree-zero normalization is now proved by an explicit construction,
not assumed for arbitrary comparisons. Independent Loogle, Lean Finder and grep
searches for Ext under equivalence found general Ext and resolution tools, not an
exact ready-made site comparison. The upstream `Adjunction.extAddEquiv` is a
possible shorter future route, but still needs exact-equivalence/representing-object
setup and, for that lemma, an enough-injectives instance for these universes.
No duplicate public statement was introduced. The similar open-immersion sections
helpers use `uliftYoneda` and coefficients in universe `u + 1`, so do not replace
these universe-`u` helpers directly.

4. **Shortest route and pruning — pass after report repair.** Read the finite
refinement, induced-topology, one-hypercover-density and representing-object
arguments. They use Mathlib directly and avoid an unnecessary underlying-category
transport and K-injective bridge. The three added imports are private proof
imports and have concrete uses: affine refinement, openness of etale maps, and
whiskered free-abelian adjunctions. The three public imports are needed by public
signatures. The complete pruning accounting is above. Read `dag/units/sk-thm-p1.json`:
none of its realized nodes is bypassed or altered.

5. **DAG — pass after repair.** Read every delivered node and checked its proof
route against Lean. Added the missing normalized-comparison dependency to the
parent's `proof_deps` union. Recorded affine-pullback use in the abelian equivalence
node. Expanded the corrected comparison-point statement, verbatim Lean statement,
proof dependencies and statement-change metadata. All delivered `proof_deps` lists
now agree with the union of step uses; no new nodes are needed. The existing
comparison-data node retains its genuine smaller, unnormalized comparison problem.

Second reading changed the report, change record, parent dependency union,
abelian-equivalence pullback accounting, and comparison-point node. The only Lean edit in this reading removes that extra signature space; no proof
needed repair. The eight unchanged-statement closures are separated from the
false-statement repair and from claims of fully axiom-free completion.
