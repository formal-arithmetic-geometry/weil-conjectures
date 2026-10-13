## What changed

Replaced the whole proof hole of
`AlgebraicGeometry.Scheme.picard_direct_image_test_sections` by a compiling proof.
The existing signature and public imports are unchanged. The proof obtains the
cohomological comparison from the new module
`Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality`, then constructs the
residue comparison by `pullback.lift`, proves its two projection identities and its
cartesian property, and proves the required point-surjectivity using the image of
the residue map and `Scheme.Pullback.range_fst`. It explicitly constructs the
coefficient isomorphism as the conjugate of the canonical pushforward composition
under the pinned tensor adjunctions; no object is chosen from mere unproved existence.
The final compatibility follows by specializing the new cohomological naturality lemma.

The new lemma isolates steps 1 and 3 of the old plan. It has no residue point,
open-neighbourhood quantifier, geometric image assertion or existential coefficient
isomorphism: the coefficient comparison is fixed explicitly. The target's geometric
step 2 and the construction of that coefficient comparison are real Lean proofs here.
Its statement and docstring specify the remaining canonical-comparison argument.
The existing DAG node now follows this proof. No unit or chapter route is bypassed;
`sk-prop-av-cube` has no realized entry assigned to this node.

## Proved and sorry left

Closed the textual hole in
`AlgebraicGeometry.Scheme.picard_direct_image_test_sections`
(node `lem-sc-picard-direct-image-test-sections`); no sorry remains in the item's module.
Added one public theorem with its entire proof `by sorry`:
`AlgebraicGeometry.Scheme.picard_direct_image_section_naturality`
(node `lem-sc-picard-direct-image-section-naturality`).
This is a decomposition, not a sorry-free proof of the mathematical theorem:
one hole closed, one hole added, net zero. The remaining work is the cohomological
comparison and its canonical naturality, not the residue-fibre geometry.

Both modules compile locally in import order. The new statement was checked for the
empty-scheme case (the section groups and derived Hom groups are zero), identity base
changes (the canonical unit and composition comparisons), and arbitrary non-flat
successive base changes (0B91 applies because the coefficient module is relatively
flat, with no flatness assumption on the test morphism). Projection compatibility
is essential: it pins j to the cartesian map, rather than allowing an arbitrary
scheme morphism with a coefficient isomorphism.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`,
`Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf`, and
`Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare`.
Their nodes `lem-pc-rf-perfect-base-change`,
`lem-sc-derived-pullback-structure-sheaf-local`, and
`lem-pc-canonical-degree-zero-mate-square` are not direct dependencies of the completed
item proof. They remain planned dependencies of the new cohomological lemma, together
with `lem-pc-ringed-spaces-derived-pullback-composition`; they are not claimed to be
mathematically pruned. No node or module is globally declared unnecessary. All existing
public imports were retained; the only new proof import is the new naturality module.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the existing statement was found. The old node's argument
includes a canonical naturality computation that is not immediately supplied by the
signatures of perfect base change, structure-sheaf pullback and the degree-zero mate
square: their composition and evaluation is still a separate proof obligation.
The new lemma records this obligation, while the residue geometry is completed.

The local published build lacks `TensorPullbackCompositionIso`, although its source
is present. The proof uses the same canonical conjugate-iso expression directly as
local terms, from the already published tensor adjunction module. It does not redeclare
or change that library definition, or compile another holder's module.
The literature checkout is absent on this machine; Stacks Tags 0B91, 08HY and 0D5S
were read on the official Stacks website. Tag 0B91 clause (2) gives arbitrary base change
for a finitely presented relatively flat coefficient, 08HY gives its adjunction-mate
construction, and 0D5S gives composition. LeanSearch returned Internal Server Error;
Lean Finder, Loogle and grep searches succeeded and found ingredients, no exact match.
Blueprint searches for test sections and canonical mate found no matching blueprint node.

## New nodes

`lem-sc-picard-direct-image-section-naturality` in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-direct-image-section-naturality.json`
is the cohomological, successive-base-change part of the original proof, with its
fixed coefficient comparison, complete proof in words, source and actual search records.
Its module is `lean/Sheaf/AlgebraicGeometry/PicardDirectImageSectionNaturality.lean`.
There are no interface changes, change records or forced adaptations.

## Second reading by J3

1. **Interface and accidental changes.** Compared the delivered target module with the repository version. The theorem statement and existing public declarations are byte-for-byte unchanged; the only interface addition is the separately named naturality theorem and its matching DAG node. Verdict: pass.

2. **Proof and trust.** Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The target proof contains no `sorry`, and the only remaining `sorry` is the named theorem `picard_direct_image_section_naturality`, documented and represented by node `lem-sc-picard-direct-image-section-naturality`. No axiom, unsafe, opaque, extern, or hollow definition was added. The explicit scratch `#print axioms` checks for both declarations show exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; no other axioms occur.
Verdict: pass subject to the documented decomposition.

3. **Statements and searches.** Read the new theorem statement against the target reduction. It isolates only the additive section comparison and its naturality under successive base change, with the coefficient isomorphism fixed by the canonical tensor adjunction conjugate. It adds no residue-point or image assertion. Empty schemes and identity maps are covered by the same categorical equivalences. Existing library and Mathlib searches found no duplicate declaration. Verdict: pass.

4. **Pruning and route.** The target proof uses the new naturality theorem, pullback lifting, `IsPullback.of_right`, and `Scheme.Pullback.range_fst`. The three former direct proof-only imports removed from the target are not referenced by its proof; they remain appropriate dependencies of the open naturality theorem. Public imports in both modules are retained where their statements require them. Verdict: pass.

5. **DAG and unit route.** The target node proof, dependencies, and origin match the Lean proof. The new node records the open cohomological step with its source, proof description, search records, and Lean declaration. The unit route is unchanged (`sk-prop-av-cube` remains unrealized for this node). Verdict: pass.

Second reading changed: added private imports of PerfectDirectImageBaseChange,
DerivedPullbackStructureSheaf, DerivedAdjoint, and Picard.CanonicalDegreeZeroMateSquare
to the open naturality module, matching its planned DAG dependencies. No theorem
statement or proof was rewritten. Independent searches used the queries
"global sections comparison compatible with successive pullbacks via adjunction mates",
"Adjunction.homEquiv_naturality_left", and
"conjugateEquiv_pullbackComp|unitHomAddEquiv_comp|pullbackObjUnitToUnit".
Lean Finder and grep found only constituent results; Loogle found no matching
identifier. Read the official Stacks pages for Tags 0B91, 08HY, and 0D5S.
The remaining comparison needs substantial canonical-map coherence work and
cannot be closed by a short application of the existing declarations.
