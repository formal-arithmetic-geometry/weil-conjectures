## What changed

Both original declarations keep their statements and docstrings unchanged and now have complete
Lean proofs from named intermediate declarations.

`AlgebraicGeometry.strictHenselizationResidue` constructs the residue equivalence from a
surjective ring map with maximal-ideal kernel. It proves the structural-map and closed-point
assertions, separable closedness, and uniqueness. Uniqueness uses the universal property of the
canonical cone, faithfulness of Spec, surjectivity of the residue map and injectivity of the
relative-separable-closure inclusion.

`AlgebraicGeometry.strictHenselizationFunctoriality` uses an existence lemma asserting only
locality, the base diagram and residue compatibility. The inclusion of relative separable
closures is then proved by lifting an element through the source residue map. Uniqueness and
compatibility with arbitrary pointed neighbourhood morphisms are proved using an independent
rigidity lemma and the canonical cone's universal property.

Added four modules, one public theorem per module:

- `Sheaf.Paper.StrictHenselizationLocalStructure`: proved from the existing
  `Scheme.etale_local_ring_triples`, `Scheme.strictHenselization_triples`, the equivalence of
  affine representatives and Mathlib colimit comparisons. Its construction factors the point
  through an affine open, compares the specified ring with the triple colimit, and transfers
  local and strictly henselian structures through the ring equivalence.
- `Sheaf.Paper.StrictHenselizationPointedMap`: states the remaining transport of the canonical
  compatible residue maps to the chosen ring, with surjectivity, kernel and pointed equations.
- `Sheaf.Paper.StrictHenselizationMapExists`: states existence of the local map and its two
  diagrams, without uniqueness or arbitrary neighbourhood compatibility.
- `Sheaf.Paper.EtalePointedMapRigidity`: proved using the open diagonal of an etale morphism.
  The closed point lies in the equalizer's open range; generization makes the entire local
  spectrum land there, and factorization through the diagonal proves equality. No henselianity
  is needed for this result.

The existing node's proof, proof_deps and proof_origin now follow these Lean arguments.
The new modules import the existing planned algebraic dependencies, so those are the subsequent
items rather than being proved again here. All additions and proof changes are in the sandbox.

## Proved and sorry left

Proved, from the existing library and the two remaining named obligations:

- `AlgebraicGeometry.strictHenselizationResidue`
- `AlgebraicGeometry.strictHenselizationFunctoriality`
- `AlgebraicGeometry.strictHenselizationLocalStructure`

Proved without any new unproved dependency:

- `AlgebraicGeometry.etalePointedMapRigidity`

Every sorry added by this delivery, and the only sorries in its five modules:

- `AlgebraicGeometry.strictHenselizationPointedMap`
  (`lem-weil-pbc-strict-henselization-pointed-map`): source Tags 04HX, 04GW, 04GP;
  a surjective map and its specified kernel and neighbourhood equations, with no equivalence,
  uniqueness, structural-map equation or strict henselianity in its conclusion.
- `AlgebraicGeometry.strictHenselizationMapExists`
  (`lem-weil-pbc-strict-henselization-map-exists`): source Tags 03PS, 04GU, 08HR;
  existence of a local map with base and residue equations, with no uniqueness or compatibility
  with arbitrary neighbourhood morphisms. These latter conclusions, and inclusion of the
  closures, are combined and proved in the original module.

Each remaining proof is exactly `:= by sorry`, in a public named theorem of its own new
module, with a source and complete natural-language argument in the docstring and DAG node.
Neither intermediate is a renamed copy of an original theorem: the original module contains
independent quotient, closed-point, uniqueness, inclusion and rigidity arguments.

All five modules compile in import order with the prescribed `lcompile.py --all`, without
warnings. The required `deliver3.py --no-push` is the final validation; this report is prepared
for the second reader, who writes the second-reading section and performs delivery.

## No longer needed

Removed these four direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.RingTheory.MapIntoHenselianColimit`
- `Sheaf.RingTheory.StrictHenselizationTriples`

Their relevant uses now belong to the new helper modules; StrictHenselization is already
publicly supplied by StrictHenselizationStructuralMap. The original module instead imports the
four helpers and Mathlib.FieldTheory.IsSepClosed as proof-only imports. Its three original
public imports remain unchanged.

No existing node or module becomes globally unnecessary: the triple results are actually used
in the proved local-structure helper and in the pointed-map transport; the henselian mapping
result remains required for map existence. Its repeated uniqueness applications in parent
steps 8 and 9 are unnecessary, replaced by the proved open-diagonal rigidity argument.
No chapter or unit statement or realized step has been bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction or disputed statement. The original plan was more elaborate than
necessary for uniqueness and neighbourhood compatibility: henselian lifting uniqueness can
be replaced by the open diagonal and generization in a local spectrum. The inclusion of
relative separable closures can also be deduced from the existence map's residue equation and
surjectivity of the source residue map; it need not be reproved separately in the parent.
Map existence itself still follows the affine/triple/henselian route and uses the usual
inclusion argument in its documented proof.

The specified literature checkout is not populated on this machine. I read the corresponding
Stacks texts online: [04HX](https://stacks.math.columbia.edu/tag/04HX),
[04GW](https://stacks.math.columbia.edu/tag/04GW),
[04GP](https://stacks.math.columbia.edu/tag/04GP),
[04GU](https://stacks.math.columbia.edu/tag/04GU),
[08HR](https://stacks.math.columbia.edu/tag/08HR), and
[02GE](https://stacks.math.columbia.edu/tag/02GE).
LeanSearch returned an Internal Server Error and is recorded as unavailable, without a
match verdict. LeanFinder, Loogle and local grep supplied the component declarations;
no existing declaration or blueprint node gives either remaining transport obligation or
combines the rigidity argument. The available Mathlib components are used directly.

Edge cases checked: no connectedness or affineness hypothesis is imposed on the original
schemes; the affine chart is chosen only around the geometric point. The local-ring hypothesis
excludes the zero ring for rigidity, and beta being local is essential for the closed-point
step. Omega need only be a field in rigidity. No perfection, characteristic or algebraic
closure assumption was introduced beyond the unchanged original geometric-point hypotheses.
The existence helper takes the same specified algebra structures and sigma factorization
equations as the original theorem; it does not silently replace them by arbitrary embeddings.

## New nodes

`lem-weil-pbc-strict-henselization-local-structure`, module
`Sheaf.Paper.StrictHenselizationLocalStructure`, is proved from the existing triple and
colimit declarations. It isolates the local and strictly henselian structures, with no
residue identification or pointed compatibility.

`lem-weil-pbc-strict-henselization-pointed-map`, module
`Sheaf.Paper.StrictHenselizationPointedMap`, isolates the surjective canonical map with its
maximal-ideal kernel and equations on representative neighbourhoods. It remains sorry.

`lem-weil-pbc-strict-henselization-map-exists`, module
`Sheaf.Paper.StrictHenselizationMapExists`, isolates existence with locality and the base and
residue diagrams. It remains sorry, and its source-based proof follows parent steps 5--7.

`lem-weil-pbc-etale-pointed-map-rigidity`, module
`Sheaf.Paper.EtalePointedMapRigidity`, is a proved geometric uniqueness tool used for both
parent uniqueness and neighbourhood compatibility. Its proof uses only Mathlib's open
diagonal, local-spectrum generization and open-immersion factorization.

All four nodes inherit the parent's chapter and unit. No change record is required:
no existing definition or statement, public import, or target signature changes.

## Second reading by Y2

1. Compared the delivered original module with the repository version. The two theorem
   statements and all existing declarations are unchanged byte for byte; only proof bodies,
   proof imports, and the recorded proof metadata differ.

2. Compiled all five delivered modules with `lcompile.py --all`. They compile without errors or
   warnings. The only remaining `sorry`s are the two named obligations in
   `StrictHenselizationPointedMap` and `StrictHenselizationMapExists`; no definitions contain
   `sorry`, and no forbidden declarations occur. The proved declarations use only the permitted
   foundational axioms under the delivery probe.

3. Checked the split-off statements and their docstrings and DAG nodes. Each is a strict
   intermediate obligation (pointed residue transport, map existence, local structure, or
   etale pointed-map rigidity), with the stated source and edge cases; none restates either
   original theorem, and local search found no existing duplicate.

4. Read the proofs from the targets downward. The residue equivalence, closure inclusion,
   uniqueness, and neighbourhood compatibility are genuine reductions using the helper
   statements and the canonical cone. The four direct proof-only imports removed from the
   original module are no longer needed there; the helper modules retain the imports they use.

5. Verified that the DAG proof, `proof_deps`, `proof_origin`, and the unit's realized route
   match the Lean proofs. No unit statement or realized step is bypassed, and no target or
   definition was changed.

Changed after this reading: appended this review only; no Lean or DAG repair was necessary.
