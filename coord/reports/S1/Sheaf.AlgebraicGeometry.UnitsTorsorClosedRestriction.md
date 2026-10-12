## What changed

Proved AlgebraicGeometry.Scheme.unitsTorsor_closed_restriction_class using the existing
representative-extension and extension-fibre pushforward declarations. The proof constructs
an equivariant torsor isomorphism, passes to quotient classes, and applies classH1_lifts.
The original definition and theorem signature are unchanged.

Added Sheaf.AlgebraicGeometry.UnitsTorsorClosedRestrictionBoundary with the proved theorem
AlgebraicGeometry.Scheme.units_extension_pullback_boundary_comparison. It identifies the
boundary of one with the Ext extension class, constructs the counit morphism from the
inverse-image pullback sequence to the original sequence, proves its quotient component
is the constant-sheaf comparison by uniqueness of adjoints, and uses Ext naturality.
The private equiv_zero_one helper is also proved. Updated the item's proof DAG.

Rechecked both modules through lcompile.py --all (exit code 0); the new boundary module uses
only existing proved declarations. Edge cases include the identity immersion and empty
Z: the adjunction identities and boundary calculation remain valid without choosing
points or nonzero sections. All local choices of extension data occur inside a theorem
proof, not in any definition.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.unitsTorsor_closed_restriction_class (1 of 1).
There are no sorries in either delivered module and no new holes.
The proof still depends on the existing holes in
CategoryTheory.Sheaf.torsor_h1_boundary_representative
(lem-sc-torsor-h1-boundary-representative) and
CategoryTheory.Sheaf.Torsor.closedImmersion_extension_fibre_pushforward
(lem-sc-torsor-h1-ext-pushforward). This is a proof from the existing planned dependencies,
not an assertion that the entire transitive closure is sorry-free.

## No longer needed

Removed import Sheaf.Topology.ClosedPushforwardBoundaryNaturality and the direct
proof dependency lem-sc-closed-pushforward-boundary-naturality. Its abstract universal
delta-functor argument is replaced by a proved concrete Ext/counit calculation.
Consequently this item no longer requires that module's private proof imports
Sheaf.CategoryTheory.DeltaFunctor, Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal,
Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor, or
Sheaf.Topology.ClosedImmersionPushforwardCohomology through that branch.
These may remain needed elsewhere; no global unreachability is claimed.
The boundary-comparison module also compiles without its initially listed direct imports
Mathlib.CategoryTheory.Sites.SheafCohomology.Basic, Mathlib.Topology.Sheaves.Abelian,
Mathlib.Algebra.Category.Grp.AB, Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf,
Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt, and
Mathlib.Algebra.Homology.DerivedCategory.Ext.Map; those declarations arrive through the
remaining public imports and are not proof dependencies of this delivery.
The representative-extension and extension-fibre pushforward imports remain used.

## Where the brief, the DAG or earlier work was wrong

The boundary-naturality declaration is expressed using an existential abstract
cohomological delta-functor comparison, whereas unitsPushforwardCohomologyComparison
is a specific Ext map. Its signature does not supply the identification of those
comparisons. The new lemma proves that specific compatibility directly.
No mathematical error or statement change was necessary, and the unit route is kept.

The local literature/stacks-project/cohomology.tex file is absent on this machine.
Read the cited source online at https://stacks.math.columbia.edu/tag/02FQ and
https://stacks.math.columbia.edu/tag/02UV. The concrete Ext implementation is marked
agent-written in proof_origin. WANTED: the local Stacks cohomology.tex source for these tags.
LeanSearch returned Internal Server Error; Loogle, LeanFinder and source searches ran.

## New nodes

lem-sc-units-extension-pullback-boundary-comparison records the proved boundary calculation
in Sheaf.AlgebraicGeometry.UnitsTorsorClosedRestrictionBoundary. It is strictly the
extension-class compatibility step and contains no assertion about torsor classes.
Its statement, source, full proof, search results, and Lean signature are recorded.
No existing public interface changed and no forced adaptation or change record is needed.

The resumed attempt rechecked the complete proof and corrected the new node’s proof
and search notes to name the Ext lemmas actually used, rather than an unused combined
upstream theorem.

## Second reading by S1

1. **Visible changes:** Diffed both delivered modules against the repository versions. The
   existing definition and theorem signature are byte-for-byte unchanged; the new module is
   the declared split-off node. Verdict: pass.
2. **Proof and axioms:** Compiled both modules with `lcompile.py --all`; grep found no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The new boundary
   theorem has only `propext`, `Classical.choice`, and `Quot.sound`; the target theorem's
   `sorryAx` comes only from its two explicitly listed upstream open dependencies. Verdict:
   pass.
3. **Statements and searches:** Checked the split-off statement against the construction in
   the target proof and searched the local library plus Loogle for the Ext/naturality result.
   The lemma is a strict extension-class compatibility step, not a restatement of the target,
   and its source/proof docstring and DAG node agree. Verdict: pass.
4. **Pruning and route:** Removed the obsolete abstract boundary-naturality import and the
   six unused direct imports from the concrete boundary module. The representative-extension
   and extension-fibre dependencies remain, and the unit route is unchanged. Verdict: pass.
5. **DAG consistency:** Verified the node declaration, proof steps, proof dependencies,
   proof origin, and `lean` signature against the compiled code. Verdict: pass.

Changed only proof bodies, the new boundary module/node, its import pruning, and this report;
no statement or definition was changed.
