## What changed

Replaced the sorry in AlgebraicGeometry.Etale.strictHenselizationStalkFormula with a
proof of both clauses, leaving its signature unchanged. The ordinary sheaf clause applies
AlgebraicGeometry.Etale.unrestricted_strictHenselization_stalk, an existing declaration
with the identical canonical restriction and no torsion hypothesis. The derived clause
chooses the unique germ restriction, proves its invertibility using the first new lemma,
and composes it with the inverse-image/homology isomorphism, the global-sections image of
the base-change mate using the second new lemma, and the strict-local Leray isomorphism.
The latter three factors are exactly those written in the original conclusion.

The two new modules are proof imports, and introduce no definitions. Each contains one
named public theorem with sorry. The existing node's proof and proof_deps now follow the
compiled reduction. Public imports and all existing declaration signatures are preserved.

## Proved and sorry left

Proved the assembly theorem AlgebraicGeometry.Etale.strictHenselizationStalkFormula
(node prop-weil-pbc-strict-henselization-stalk-formula): one of one original sorries removed.
This is a reduction to named statements, not a claim that its transitive axioms are closed.

The delivery adds exactly two sorries:

- AlgebraicGeometry.Etale.isIso_strictHenselizationStalkRestriction, node
  lem-weil-pbc-strict-local-germ-restriction-iso, in
  Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso.
- AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology, node
  lem-weil-pbc-strict-local-base-change-global-homology, in
  Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology.

The existing unrestricted_strictHenselization_stalk and
existsUnique_strictHenselizationStalkRestriction remain open in their existing modules;
this delivery does not modify them. Each new sorry has a source and a full proof sketch
in its docstring and node. The germ lemma is independent of any morphism f or complex K.
The mate lemma concerns only the middle factor between strict-local global sections,
not the stalk, the germ restriction, or the final cohomology comparison. Neither restates
the original conjunction or either of its canonical composites.

## No longer needed

Removed these six direct proof imports from the item's module:

- Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
- Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal
- Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit
- Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity
- Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit
- Sheaf.AlgebraicGeometry.StrictHenselization

The ordinary continuity node lemma-weil-pbc-etale-cohomology-continuity and its module
Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity are unnecessary for this route: general
derived continuity works also on degree-zero sheaves. All other removed direct imports
are retained below the unrestricted formula or the new mate lemma's proof plan; they
are not claimed to be globally pruned. Definitions of stalks, neighbourhoods, schemes,
inverse image and direct image remain needed through the statements and imported
infrastructure. The injective representative and sheafification-invariance nodes remain
needed for the new mate lemma, rather than being pruned.

## Where the brief, the DAG or earlier work was wrong

The presheaf formula currently provides an unspecified Nonempty isomorphism. Its signature
alone does not identify the canonical restriction with the continuity cocone, so this
compatibility must be supplied in the remaining mate lemma. The sources 03Q9 and 0GIT
work without torsion; this is used in the two smaller lemmas, while the item's torsion
hypotheses are unchanged. No mathematical error in the original statement was found.

Read Stacks 03Q9 and 03QO online because the local literature tex file is absent. Checked
StrictlyHenselianSectionsStalk, InverseImageStalkGerm, StrictHenselizationRestriction,
AbelianHigherDirectImagePresheaf, DerivedEtaleCohomologyLimit and the fibre-product limit.
The unit sk-prop-h2 has no realized nodes for this item's statement or proof, and the
new mate sketch preserves the affine-neighbourhood/limit/continuity/injective route.
The existing unrestricted formula is an existing generic tool with that same route.

Edge cases checked mathematically: f the identity (mate is the identity comparison),
K zero, every integer n below a representative's bound, an empty X, and S already strict
local with its closed geometric point. For the germ lemma there is no qcqs hypothesis on
S: strict-local sections and the inverse-image stalk argument apply to every S and every
abelian sheaf. The mate lemma claims invertibility only after global sections, so it does
not incorrectly assert arbitrary sheaf-level base change on the strict-local scheme.

Searches ran through msearch.py: LeanFinder returned structure-sheaf stalk and scheme
pullback facts, no match; grep found no Mathlib match. LeanSearch returned an internal
server error and is recorded as unavailable, without a no-match verdict. The Loogle
queries also produced errors and are recorded as such. Local repository and whole
blueprint searches found the two generic strictly-henselian sections and inverse-image
stalk lemmas, but not either of the proposed canonical factor statements.

## New nodes

lem-weil-pbc-strict-local-germ-restriction-iso: identifies the canonical germ restriction
for any abelian sheaf with the inverse of the strict-local global germ, using the
inverse-image stalk comparison. Its statement does not involve f or higher direct images.
File: dag/nodes/sec-curve-estimates/lem-weil-pbc-strict-local-germ-restriction-iso.json.

lem-weil-pbc-strict-local-base-change-global-homology: the middle base-change factor
is invertible after strict-local global sections in every degree for bounded-below K.
Its proof plan is presheaf/stalk colimits, affine neighbourhood limits and continuity,
then checking that the derived mate gives exactly the projection restrictions on an
injective representative. File:
dag/nodes/sec-curve-estimates/lem-weil-pbc-strict-local-base-change-global-homology.json.

No change records: no existing definition or statement changed.

The germ node also explicitly uses lem-weil-pbc-etale-local-ring-triples and
lem-weil-pbc-strict-henselization-triples to supply strict henselianity and the chosen
geometric closed point; this does not infer strict henselianity from a definition name.
Their Lean signatures were read before adding these proof dependencies.

## Second reading by W2

1. Compared the delivered item with the repository version. The theorem signature and
all existing declarations are byte-for-byte unchanged; only proof imports and the proof
body changed. The two added declarations are new split-off statements with matching DAG
nodes.

2. Compiled all three delivered modules with `lcompile.py --all`. The item has no
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the only remaining
`sorry`s are the two named theorems listed above, each documented and represented by a
node. Their transitive `sorryAx`s are therefore explicit and intentional.

3. Read both new statements and their proof plans against the existing declarations.
The germ statement is the needed invertibility fact for the unique restriction, while
the base-change statement concerns only the global-sections homology mate. Neither
restates the item or adds hypotheses to an existing declaration. Edge cases in the
worker report remain valid.

4. Checked the proof from the top down. The ordinary clause uses the existing unrestricted
formula; the derived clause obtains the unique restriction and composes the three
isomorphism instances. The six direct imports removed from the item are unnecessary for
this compiled route, and the new modules retain only their statement infrastructure.

5. Checked the DAG proof and dependency lists against the Lean proof and confirmed that
the unit `sk-prop-h2` route is preserved: the target still uses the restriction node,
the two split lemmas, and the unrestricted formula. No statement or definition change
record is needed.

I changed only this report section after review; no Lean or DAG repair was necessary.
