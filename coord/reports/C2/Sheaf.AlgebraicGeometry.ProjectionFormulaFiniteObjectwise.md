## What changed

Proved the original objectwise theorem in
`Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise` without changing its signature.
The proof checks exact geometric pullbacks, transports the projection map across proper
unbounded base change, and applies the projection formula on the proper geometric fibre.
`finite_projection_iso` still assembles the objectwise result by two applications of
`NatTrans.isIso_iff_isIso_app`.

Added `ProjectionFormulaFiniteGeometricPoint`, with a complete proof using the equivalence
with constant module sheaves at an algebraically closed point, derived-module free generation,
dualizability of shifted tensor units, coproduct closure, triangle closure, and retract closure.
Added `ProjectionFormulaTriangleClosure`, fully proved: the canonical projection map commutes
with shift and defines a morphism of distinguished triangles.
Added `ProperGeometricPointDerivedCoproducts` for the one remaining finite-cohomological-dimension
obligation. All three new modules have one public theorem; local helpers are proved.

Proof imports in the original module now use the existing proper base-change theorem,
projection/base-change compatibility, derived stalk conservativity, and the new fibre theorem.
The public import `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB` supplies the source
library's atomic commutative-ring Grothendieck instance needed to elaborate the derived
coefficient categories consistently. Other added imports are proof-only. The triangle module
imports the lower-level generic shift and adjunction APIs, avoiding the projection-formula
parent and its import cycle.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_finite`
(node `lem-etale-proper-projection-formula-finite-objectwise`). The item module has no `sorry`.
`AlgebraicGeometry.Etale.finite_projection_iso` remains proved with its original signature.

Also fully proved:
`AlgebraicGeometry.Etale.isIso_projection_over_geometricPoint`
(node `lem-etale-projection-formula-finite-geometric-point`) and
`AlgebraicGeometry.Etale.projection_triangle_isIso`
(node `lem-etale-projection-formula-triangle-closure`).

Added exactly one new mathematical hole:
`AlgebraicGeometry.Etale.proper_geometricPoint_pushforward_preservesCoproducts`
(node `lem-etale-proper-geometric-point-derived-coproducts`). Its proof is exactly `by sorry`;
its docstring gives the source and complete argument. No private helper or definition contains
`sorry`. This is a decomposition of one original hole into one strictly smaller obligation,
not an axiom-free proof of the full target. The existing proper unbounded base-change hole is relocated to
`Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange` with the original declaration name and
signature, and removed from its old file in the same delivery. The remaining moved hole is
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`
(node `lem-kun-proper-base-change-torsion-ring`). Prerequisite holes of module
free generation are inherited, not new holes of this delivery.

The remaining coproduct obligation needs the unbounded acyclic-complex computation theorem
under a uniform finite cohomological bound. The source library already has K-injective
resolutions with injective terms, the geometric torsion cohomological bound, and module
cohomology/filtered-colimit comparisons. The blueprint nodes
`lem-kun-finite-cd-acyclic-complex` and `lem-kun-grothendieck-derived-coproducts` have no Lean
attachments. Sums of K-injectives cannot simply be assumed K-injective; the finite-CD acyclic
computation is essential. The theorem includes arbitrarily unbounded complexes and index sets
in `Type (u+1)`, with no common lower bound.

Validation: all six delivered Lean modules compile in import order without warnings.
The main module takes about eight seconds, the fibre module about ten seconds, the coproduct
statement about two seconds, and the triangle module about forty-nine seconds. The final
stage-3 dry run is the delivery gate. The adapted Proper module and the relocated statement
are also compiled as single files.

## No longer needed

Removed the original proof import
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`. Its declaration is not used; the
source library already supplies exactness and the derived comparison API for module inverse
image. The original node's proof edges to `lem-kun-0f0g` and
`prop-weil-pbc-inverse-image-modules-exact` are removed. They are not needed by this item's
proof; this does not assert that they are unused by other parents.

The general torsion-ring projection-formula node `lem-kun-0f0g` and any prospective module
for it need not be proved for this route. We directly implement its geometric-fibre argument.
The general qcqs finite-CD projection-formula node `lem-kun-0f12` and the general Z/n
coproduct node `lem-kun-0f11` are source guides, not imported proof obligations here: their
needed specializations are the new geometric-point and coproduct nodes. No claim is made
that their underlying finite-CD and derived-coproduct prerequisites are unnecessary.

The broader Noetherian `lem-amb-proper-coproducts-projection` route is not used. The existing
proper-direct-image adjoint module, the parent projection-formula module, and the high-level
`Derived.Shift`, `UpperStarMonoidal.Shift`, and `LowerShriekProjectionShift` modules are not
imported. The exact lower-level shift calculations needed for the triangle argument are proved
locally. No blueprint unit's realized statement or proof step is bypassed;
`dag/units/sk-prop-sf-cbc.json` has empty realized statement/steps lists.

## Where the brief, the DAG or earlier work was wrong

The original DAG's instruction to apply the general proper projection formula is circular
at the level of available Lean declarations: the source projection-formula module imports
this item. Likewise, the proved proper-direct-image adjoint theorem uses that parent
projection formula, so it cannot supply coproduct preservation here. Several high-level shift
modules also reach this item through exceptional inverse image. The delivery uses only APIs
below those cycles. The first dry run additionally found a source-import cycle through the
old Proper module: Proper → ProjectiveLine → Gabber → restricted derived sections →
Derived.Shift → UpperShriek → proper-derived-direct-image adjoint → ProjectionFormula →
this item. Isolating the unchanged unbounded base-change statement below Proper breaks this
cycle without copying the statement or adding another hole.

The bounded-below derived stalk node is not silently used for unbounded complexes. The proof
uses the already proved unbounded theorem
`Scheme.isIso_iff_isIso_sheafFiber_map_homologyFunctor_map`, exactness of inverse image, and
the stalk-composition isomorphism. Its DAG dependency is the existing conservative geometric
stalk theorem for sheaves, applied to every homology sheaf.

The main proof initially exceeded the compile limit when the concrete algebraic-closure
residue field was expanded through base-change data. Abstracting the geometric field and
point first, and only then specializing, avoids that expansion. In the fibre theorem the
expensive kernel step was the monoidal projection calculation at a constant generator.
Proving the generic dualizable-object projection calculation first avoids repeated expansion
of the coefficient-derived monoidal structure. No timeout, heartbeat, kernel-checking, or
linter limit is raised or disabled, and no file is split merely to evade the compile limit.

The new coproduct theorem was checked against Stacks 0F11 and 0F12. Properness over the field
supplies qcqs and finite dimension; finiteness of the coefficient ring supplies torsion.
The zero ring, empty scheme, empty family and zero complexes are valid edge cases.
There is no statement dispute and no change to an existing statement or definition.

## New nodes

`lem-etale-projection-formula-finite-geometric-point` records the fully proved geometric-fibre
specialization in `ProjectionFormulaFiniteGeometricPoint`. It is strictly part of the original
argument and is reduced further in this delivery to the coproduct obligation, with the other
steps proved in Lean.

`lem-etale-projection-formula-triangle-closure` records the fully proved triangle closure
statement in `ProjectionFormulaTriangleClosure`. Its proof includes the actual connecting
square, not just naturality on the first two arrows.

`lem-etale-proper-geometric-point-derived-coproducts` records the one remaining `sorry` in
`ProperGeometricPointDerivedCoproducts`, with finite-ring coefficients and unbounded inputs.
Its required remaining work is stated above and in its docstring. It is independent of the
projection formula and is not the original assertion repackaged.

The unclaimed existing module
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` is also adapted: its existing
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring` is moved,
with the same signature and name, to `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange` and
publicly re-exported from Proper. This is an existing hole moved, not an additional mathematical
hole or new node. It remains the node `lem-kun-proper-base-change-torsion-ring`, whose Lean
attachment is updated. The change record is
`coord/changes/proper-unbounded-base-change-location.md`; it lists all ninety import descendants
and the declaration users. No module held by another group is adapted. New node provenance follows the existing ancestry through the proper projection
formula and proper-derived-direct-image adjoint to
`thm-amb-etale-exceptional-adjoint`; all new node statements retain the item's chapter and unit.

## Forced adaptations

The unmodified `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` was compiled
against the delivered dependency `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`. It
failed at its original unbounded theorem declaration (line 155 in the original file) with:

```
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`
has already been declared
```

This is forced because the dependency now contains the unchanged declaration, while the
original `Proper` source still declared the same public name and signature. The adapted
`Proper` file changes exactly these lines:

* line 9 adds `public import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`, making the
  relocated declaration available under its original public name;
* the former theorem body and its `:= sorry` (original lines 154--157) are removed, leaving
  the bounded-below proper base-change statements unchanged; and
* the module comment gains the sentence that the unchanged unbounded theorem is publicly
  re-exported from `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`.

The declaration's name, binders, type, visibility, and all bounded-below declarations remain
identical. These edits are necessary to avoid the duplicate declaration while preserving every
existing importer of `Proper`; the adapted file compiles successfully.


## Earlier second reading (a previous round; superseded)

1. I compared the delivered item module and the adapted `Proper` module with the repository
versions. Existing theorem signatures are unchanged; the proper base-change declaration is
moved with its original name and type, and the change record documents the forced re-export.
The three added theorem signatures are new split nodes and are recorded verbatim in their DAG
files.

2. I compiled all six delivered modules with `lcompile.py --all` in import order. The item and
the two complete split-off proofs compile without `sorry`; the two remaining holes are exactly
the named declarations listed above, each with a source, docstring proof, and DAG node. No
`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration was added. The public
`ModuleCat.AB` imports supply the atomic Grothendieck instance used in exported theorem
signatures; they are therefore interface imports, not proof-only imports.

3. I checked the new statements against the cited Stacks results and their edge cases (zero
ring, empty scheme or family, and zero complexes). The geometric-point and triangle statements
are strictly smaller than the original objectwise target. The coproduct statement is the one
remaining finite-cohomological-dimension obligation, not a restatement of the target, and its
unbounded quantification is explicit.

4. I traced the proof and DAG dependencies. The item node now names the conservative geometric
stalk route, proper unbounded base change, projection/base-change compatibility, and the new
geometric-point theorem. The geometric-point node names the coproduct and triangle nodes, and
the moved base-change node points to its new module. The old inverse-image exactness import and
its two unused proof edges are removed; no unit route is bypassed (`sk-prop-sf-cbc` has no
realized statement or steps).

5. I checked that every public declaration has a matching node or is the original item, that
the change record lists the adapted module and downstream users, and that no hollow definition
or anonymous `sorry` remains. The delivery gate is `deliver3.py` after this report update.

Changed during second reading: tested private imports of `ModuleCat.AB`, then restored the
public imports after the geometric-point module reproducibly exceeded 60 seconds with private
imports. Its public signature needs the atomic Grothendieck instance. Added this review record;
restored the original private `isIso_of_isIso_app_app` helper and the original
`finite_projection_iso` proof, whose replacement was unnecessary. Existing declaration
signatures are byte-identical, including the relocated proper base-change declaration.

Axiom audit: `#print axioms` in `scratchpad/lean/AxiomAudit.lean` reports only `propext`,
`Classical.choice`, and `Quot.sound` for `projection_triangle_isIso`. The public declarations that depend on the two remaining holes report `sorryAx`; these are
accounted for by the named remaining holes and inherited free-generation prerequisites. No other
axiom occurs.

I repeated semantic searches with alternative descriptions of finite-cohomological-dimension
coproduct preservation, exact triangle comparisons, and monoidal adjoint projection maps.
LeanFinder returned exact-functor/shift APIs rather than a missing projection theorem; Loogle
returned no derived-coproduct preservation result. Repository and Mathlib searches found only
bounded-below acyclic-computation APIs, the cyclic proper-adjoint route, or quasi-coherent
Zariski statements. None closes the remaining unbounded etale coproduct hole in a few minutes.
The actual search records are appended to `searches.jsonl`. The mathematical sources checked
were [Stacks 0F11](https://stacks.math.columbia.edu/tag/0F11),
[0F12](https://stacks.math.columbia.edu/tag/0F12),
[0F0G](https://stacks.math.columbia.edu/tag/0F0G), and
[0F0C](https://stacks.math.columbia.edu/tag/0F0C).


## Second reading by C2

1. **Signature and accidental changes.** I compared the delivered item module with the repository
version and checked every existing declaration signature byte-for-byte. The item theorem and
`finite_projection_iso` keep their original types. The adapted `Proper` module changes only the
forced re-export import, removes the duplicate unbounded declaration, and leaves all bounded-below
statements unchanged. The moved unbounded theorem retains its original name, binders, type, and
visibility; the change record documents the relocation and its downstream users. The three added
public theorems are new declarations with matching DAG nodes. Verdict: pass.

2. **Compilation and proof hygiene.** I compiled all six delivered modules with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all` in import order; they compile without
warnings. The item module has no `sorry`. The only newly introduced hole is
`proper_geometricPoint_pushforward_preservesCoproducts`; the relocated existing hole is
`isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`. Both are named public theorems
with source citations, complete proof-in-words docstrings, and matching nodes. No definition
contains `sorry`, and no `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration
was added. The delivered proof uses only the permitted imported holes. Verdict: pass.

3. **Statement review and edge cases.** I checked the three split statements against the cited
Stacks 0F11, 0F12, and 0F0G arguments and tested the stated zero-ring, empty-scheme, empty-family,
and zero-complex cases. The geometric-point theorem is a specialization of the original
objectwise argument; the triangle theorem is its strict closure step; and the coproduct theorem
is the finite-cohomological-dimension obligation, with arbitrary unbounded complexes and index
sets. None restates the original target, weakens a conclusion, or adds an unannounced hypothesis.
Search records in `searches.jsonl` and repository searches found no existing declaration that
closes these obligations. Verdict: pass.

4. **Proof route, dependencies, and pruning.** I traced the Lean proof against each node's
`proof` and `proof_deps`. The item uses geometric-stalk conservativity, proper unbounded base
change, projection/base-change compatibility, and the new geometric-point theorem. The fibre
proof uses the coproduct and triangle nodes plus the existing free-generation and constant-sheaf
results. The unused inverse-image exactness import and its two old proof edges were removed. The
relocated base-change node points to its new module. The unit `sk-prop-sf-cbc` has no realized
statement or steps, so no realized unit route is bypassed. Verdict: pass.

5. **DAG and metadata agreement.** I checked that every new public theorem has a corresponding
node with statement, source, proof steps, proof dependencies, searches, provenance, and Lean
attachment, and that the existing item node records the actual route and removed dependencies.
The relocation change record lists the adapted module and downstream declaration users. Verdict:
pass.

I changed this delivery only by adding this second-reading record and correcting the axiom-audit
wording so it distinguishes direct holes from imported `sorryAx` dependencies. The Lean modules,
DAG statements, and proof bodies required no repair.
