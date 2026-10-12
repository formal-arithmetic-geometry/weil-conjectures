## What changed

The fixed-degree theorem is assembled from a normalized comparison homomorphism and its
two-sided inverse. Each new statement lives in its own module:
`Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom` and
`Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeInverse`.
`Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization` supplies the
homomorphism normalization predicate and holds the five existing comparison definitions,
moved byte-for-byte. The original module publicly re-exports them. The new proof imports
are plain imports. Existing theorem signatures and all existing definition bodies are unchanged.

The relocation, with the three direct users checked, is recorded in
`coord/changes/singletonTensorDegreeComparisonDefinitions.md`. Expanding the tensor-pullback
objects in the intermediate signatures caused slow definitional comparison; referring to
the shared existing definitions makes every delivered module compile in under ten seconds.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison_degree`
(node `new-etale-affine-singleton-tensor-degree-comparison-degree`). Its proof combines two
strict parts of the argument and verifies both categorical inverse identities.

Holes added and left:
- `AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison_hom`, node
  `new-etale-affine-singleton-tensor-degree-comparison-hom`;
- `AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison_inverse`, node
  `new-etale-affine-singleton-tensor-degree-comparison-inverse`.

`AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison` was already proved by
dependent choice in the repository; its proof is unchanged and is not an additional hole closed.
There are no sorries in the item's module or the normalization module. Both new holes are
entire proofs of named public theorems with sources and complete docstring proofs.
This is a decomposition: one old hole closed and two lower holes added, net minus one
before any whole-project ledger measurement. Neither module completion nor axiom-free
proof of the geometric comparison is claimed.

## No longer needed

No globally pruned module is claimed. The old six direct proof dependencies of the degree
node are replaced by the homomorphism and inverse nodes:
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-pc-module-pullback-identity-composition`,
`lem-sc-etale-qcoherent-presheaf-functorial`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-affine-sections`, and `def-sc-etale-qcoherent-module`.
All six remain in the lower geometric proof plans.

The item's old proof imports `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` move to the lower theorem modules.
Its four original public imports move to the shared normalization module and remain publicly
reachable through the item's replacement public import. The shared object definitions need
those imports. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The first report counted the existing all-degrees assembly as newly proved and did not state
the net hole increase. It also put both new statements and the new predicate in the original
module. The final delivery puts the statements in their own modules, records the definition
relocation, and reports the decomposition honestly. No mathematical error or target
statement change was found.

## New nodes

`new-etale-affine-singleton-tensor-degree-comparison-hom` isolates existence and the
pure-tensor formula, without invertibility. Its module is EtaleAffineSingletonTensorDegreeHom.

`new-etale-affine-singleton-tensor-degree-comparison-inverse` isolates invertibility of
an arbitrary normalized comparison, given its pure-tensor formula. Its module is
EtaleAffineSingletonTensorDegreeInverse. Neither hole restates the full isomorphism-existence
claim: the upper proof actually combines map construction with two inverse identities.

`new-etale-affine-singleton-tensor-degree-comparison-hom-normalization` defines the
homomorphism normalization and records the shared module containing the unchanged object
definitions. It has no sorry. The change record is
`coord/changes/singletonTensorDegreeComparisonDefinitions.md`.

## Second reading by A3

1. Compared the delivered sources with the repository, including the relocated declarations.
   All seven existing signatures and all five definition bodies are unchanged; the fixed-degree
   theorem changes only its proof. The all-degrees proof is unchanged. The relocation and public
   import are explicitly recorded; no target or downstream statement changes its meaning.
2. Compiled all four modules in import order. They have no errors or warnings and contain exactly
   the two reported theorem sorries; no hollow definition or forbidden axiom mechanism is present.
   A scratch `#print axioms` check of both comparison theorems reports only propext,
   Classical.choice, Quot.sound and the expected sorryAx. The delivery probe checks every constant.
   Choices of the map and inverse occur only inside a theorem proof, not a data definition.
3. Read both smaller statements and their proof docstrings. Degree zero is ordinary affine
   pullback sections. With empty W the tensor and section groups vanish; no surjectivity of g or
   faithful flatness is needed for the comparison. Tensor and indexed tensor induction show the
   normalization determines an additive map uniquely, justifying the inverse statement for every
   normalized map. Searched Mathlib independently with leanfinder, loogle and grep, and searched
   the project's affine-section and fibre-product modules. Found the existing affine pullback
   sections primitive and Mathlib pullbackSpecIso, but no theorem closing either complete lower
   statement. LeanSearch was unavailable and is recorded as such.
4. The original categorical assembly is the direct route once these two geometric parts are
   supplied; the actual geometric work remains in the named lower statements. Imports serve the
   shared interfaces or the lower proof plans. All six replaced direct dependencies are listed
   above. `dag/units/sk-prop-h2.json` has no realized node involving this item; no unit or chapter
   route is bypassed or changed.
5. Checked the degree node's proof steps, dependency union and proof origin against the Lean.
   Each new node has a complete Lean signature, source, parent provenance and real recorded
   searches. The inverse plan uses the affine comparison and generator uniqueness, rather than
   claiming that an existence theorem for a normalized map alone gives its bijectivity.

Changed the organization of the new declarations and shared definitions to respect separate
modules without an import cycle, strengthened the natural-language proof documentation,
corrected the DAG records and progress count, and checked the three unchanged direct users:
EtaleAffineSingletonTensorAmitsur, EtaleAffineSingletonTensorCofaces and
EtaleAffineSingletonTensorPureCofaces (held by K3; its source was not changed).
The geometric source calculation was checked against
[Stacks 03P2](https://stacks.math.columbia.edu/tag/03P2) and
[Stacks 01IA](https://stacks.math.columbia.edu/tag/01IA).
