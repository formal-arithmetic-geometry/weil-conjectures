## What changed

Replaced `AlgebraicGeometry.Scheme.affine_boundedAbove_fiberBetti_eq`'s whole-proof
sorry with a proof from a derived-object model. The original signature and all public
imports remain unchanged. The proof obtains K-flatness from bounded-above free terms,
applies the geometric model, takes derived homology, commutes exact field sections and
scalar restriction with homology, uses the tilde/Gamma unit termwise, and compares ranks
under the explicit residue-field isomorphism. The construction works without finite
dimensionality: the last step uses cardinal ranks and `Cardinal.toNat`.

Added `Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel`, with the geometric part
as a single new theorem, and updated the item's node to match this reduction.
The new theorem is not the Betti equality under another name: it has a K-flat hypothesis,
no degree, bound or freeness parameters, and concludes an isomorphism of derived sheaf
objects before any cohomology or dimension calculation. The completed proof supplies
K-flatness and performs those subsequent calculations in Lean.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affine_boundedAbove_fiberBetti_eq`
(node `lem-sc-affine-bounded-above-fiber-betti-comparison`).
No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.affine_kFlat_residuePullback_model`
(node `lem-sc-affine-kflat-residue-pullback-model`), the entire proof in the new module.
This is a decomposition, not a net elimination of sorry: one hole closed, one added.
All other lemmas used are existing declarations. No data definition, target, signature,
instance or visibility was changed, and no arbitrary object was chosen from existence.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport` and
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`.
Their nodes `lem-pc-affine-localized-site-derived-transport` and
`lem-pc-affine-derived-pullback-tensor-tilde` are now dependencies of the new geometric
model; they remain transitively needed. No entire module or node is globally pruned.
The bounded-flat module, associated-sheaf leaf, and fibre-Betti definition remain needed.
The unit `sk-prop-av-cube` has no realized node removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan describes the correct mathematical argument, but its cited interfaces do
not directly assemble the ambient residue pullback from an arbitrary localized affine
model. In particular the localized derived transport theorem gives an existential
equivalence compatible with tilde; it does not characterize that arbitrary witness's
compatibility with the ambient residue morphism. The new geometric node records use of
the canonical exact restriction equivalence and the missing residue-point comparison.

The two residue fields are not definitionally equal. The proof explicitly composes
`U.ι.residueFieldMap`, the inverse affine-chart residue map, and `Spec.residueFieldIso`,
and uses restriction of scalars along that map. A same-field linear equivalence alone
would not state the required comparison.

Checked the source text of Stacks Tags 08DW(2) and 0BDI: the former computes affine
pullback and states compatibility with open restriction; the latter reduces the Betti
calculation to affine free models. The new lemma adds no finite-rank requirement.
Empty U has no point z. Zero complexes and degrees above the bound are handled by the
same functors; infinite-rank free terms are allowed, and infinite-dimensional cohomology
is handled by the rank calculation. The new derived-object lemma accepts unbounded
K-flat models and does not claim their cohomology is finite.

Searches: LeanFinder returned eight unrelated algebraic dimension results; Loogle's
finrank/restrictScalars search returned no hits; msearch grep returned no exact match;
repository searches found affine pullback, stalk residue computations, and perfect
localized comparisons, none with this ambient K-flat derived-object statement.
Blueprint search found no duplicate. LeanSearch was unavailable (Internal Server Error).
The existing one-point evaluation equivalence is used as an exactness tool; it does not
replace any theorem-of-the-cube route.

## New nodes

`lem-sc-affine-kflat-residue-pullback-model` in
`dag/nodes/sec-abelian-varieties/lem-sc-affine-kflat-residue-pullback-model.json` states the
geometric derived-object comparison in
`lean/Sheaf/AlgebraicGeometry/AffineKFlatResiduePullbackModel.lean`.
It isolates the first two geometric steps of the original plan; its docstring supplies
the open factorization, canonical exact transport, residue-field scalar compatibility,
and K-flat affine computation. The remaining K-flatness and homology/rank steps are
proved in the original module. No change record is required: all existing interfaces
are preserved, and the new module is imported only for a proof.

## Second reading by N4

1. **Interfaces: PASS.** Diffed both delivered modules against the read-only repository.
   The only existing declaration is `affine_boundedAbove_fiberBetti_eq`; its complete
   signature is byte-for-byte identical, as independently checked by extracting the
   text before `:= by`. Its docstring, universes, visibility, and public imports are
   unchanged. The other module is new. No definition, target or instance was changed;
   no change record or consumer adaptation is needed.
2. **Proof and trust: PASS.** Read the completed proof in full: bounded-above free terms
   give the tensor-acyclicity criterion for K-flatness; the new geometric comparison
   is passed through derived homology; exact field-spectrum sections and scalar
   restriction commute with homology; the tilde/Gamma unit gives the complex iso;
   linear equivalence and rank transport give the stated finrank equality. A scratch
   copy compiled without warnings and printed the axioms of both public theorems:
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is
   expected because the geometric comparison remains open. The only delivered sorry
   is the whole proof of the named new theorem; no forbidden trust mechanism or
   holed data definition occurs. The locally chosen iso is used only inside a proof,
   not to define data from an arbitrary existence witness.
3. **Split statement: PASS.** The new statement is the geometric object comparison,
   strictly a part of the argument, not a renamed Betti equality. It requires K-flatness
   rather than asserting it from freeness and boundedness, and does not take homology
   or assert dimension equality. Checked its scalar direction: `e` maps the ambient
   residue field to the affine residue field, so `restrictScalars e.hom` puts the
   extended complex over the ambient field. Checked empty opens (no z), zero complexes,
   identity affine charts, unbounded K-flat complexes, and infinite-rank free terms:
   none requires a missing finiteness assumption. Read its complete docstring proof
   against [Stacks Tag 08DW](https://stacks.math.columbia.edu/tag/08DW) and the affine
   reduction in [Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI). Independent
   LeanFinder, Loogle and grep searches with different queries found no duplicate;
   the closest existing localized comparison requires strictly perfect complexes,
   while the global stalk comparison needs a global sheaf representative. The
   natural-language construction uses canonical restriction, not an unspecified
   witness of the existential affine transport theorem.
4. **Route and pruning: PASS.** Inspected the existing affine transport and affine
   pullback interfaces, the field evaluation equivalence, the tilde adjunction, and
   possible stalk/affine-coordinate shortcuts. None closes the general local geometric
   comparison in a short application. Every added proof import serves a step of the
   completed proof; the new theorem's proof imports retain its stated geometric plan.
   The two removed direct imports are both listed in `No longer needed`, and remain
   transitive dependencies of the new module. All other old proof dependencies remain
   used. `dag/units/sk-prop-av-cube.json` has empty realized lists, and this reduction
   does not remove or bypass any unit statement or step. No module is globally pruned.
5. **DAG: PASS.** Parsed both node files and compared the existing node structurally:
   only `proof`, `proof_deps`, and `proof_origin` change. Checked the declarations of
   every dependency, the unions of proof-step uses, the new node's source, searches,
   created/item/group, blueprint ancestry, chapter/unit, and verbatim Lean statement.
   The new node records the geometric steps; the parent records the actual K-flatness,
   exact evaluation, homology, and rank reduction. Both agree with the Lean.

Second-reading changes: added this review and three independent search records to the
new node. No Lean repair was necessary. One original hole closed and one geometric
hole added remains a decomposition, with net hole reduction zero. The geometric hole
requires the open-restriction, canonical affine transport, and residue-map comparisons;
its full proof is not a few-minute closure from the current interfaces.

Validation: `lcompile.py --all` compiled both delivered modules in import order with
no errors or warnings. The required `deliver3.py ... --no-push` printed OK and
classified the delivery as CODEX because of the new node/module and its named open
geometric theorem. Its compilation, axiom probes, and preflight passed.
