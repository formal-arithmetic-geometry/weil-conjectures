## What changed

Replaced the sole sorry in
`AlgebraicGeometry.exists_affineBaseChangeTildeSourceModel` with a compiling
construction and combination of two partial comparisons. Its signature and
all original public imports are unchanged.

The proof reflects the cartesian Spec square to a ring pushout, constructs the
canonical tensor-algebra isomorphism using Mathlib pushout uniqueness, and
proves its two projection equations. It instantiates the existing
`ModuleCat.baseDerivedTensorCohomologyModel`, constructs its actual source module
by extension of scalars, and constructs its actual arrow from
`localizedComparison`. The target coordinate is built from exact tilde,
ordinary tensor-pullback, the inverse universal counit and the supplied e.
No data definition contains sorry or chooses an arbitrary mere-existence witness.
The source model has an already proved existence theorem and is characterized
by its universal counit and scalar/comparison equations.

Added proof-only imports of `AffineBaseChangeTildeGlobalComparison`,
`AffineBaseChangeTildeStalkComparison`. Second reading removed redundant explicit
imports of `Mathlib.AlgebraicGeometry.Pullbacks` and
`Mathlib.Algebra.Category.Ring.Constructions`; the shortened module compiles.
Added the three new modules and
matching nodes listed below. There are no changed existing definitions,
statements, adapted modules or change records.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_affineBaseChangeTildeSourceModel`
(lem-pc-affine-base-change-tilde-source-model), one of one original holes.
There is no sorry in the item's module.

Added two holes, constituting a decomposition, not an unconditional proof:

- `AlgebraicGeometry.exists_affineBaseChangeTildeGlobalComparison`
  (lem-pc-affine-base-change-tilde-global-comparison): only the global natural
  direct-image presentation and mate square for a prescribed constructed U,a.
- `AlgebraicGeometry.affineBaseChangeTildeModuleMap_localized`
  (lem-pc-affine-base-change-tilde-stalk-comparison): only the localized square
  for that same prescribed U,a, with no global mate or direct-image conclusion.

Each hole has exactly `:= by sorry`, its source and a full proof in its docstring,
and its own new module/node. Neither restates the original theorem. The original
proof supplies the ring algebra, proves its projection equations, constructs the
coordinates and combines the two independently usable comparisons.

Proved without new holes: `AlgebraicGeometry.affineBaseChangeTilde_preservesZero`
and `AlgebraicGeometry.tilde_preservesHomology`. All three coordinate definitions
are real constructions. The zero-complex case gives zero source and target,
identity-localization cases retain the same comparison equations, and an empty
prime spectrum imposes no stalk obligation. No boundedness, flatness of a ring
map, nonzero-ring assumption, or restriction on i is added.

## No longer needed

Removed the two redundant added proof imports
`Mathlib.AlgebraicGeometry.Pullbacks` and `Mathlib.Algebra.Category.Ring.Constructions`.
No original imports removed: all four original public imports are statement
requirements and remain identical. The unused planned direct proof dependencies
are replaced by the two partial comparisons and the coordinate definition.

`new-affine-qcoh-derived-equivalence-core` /
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore` is not needed for this
termwise-tilde computation: M and e are already supplied. The target coordinate
uses exact tilde and the given invertible pullback counit directly.

`lem-pc-affine-derived-base-change-comparison-map` /
`Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison` is not needed by this
route: the existing `BaseDerivedTensorCohomologyModel` directly carries the
source, comparison and counit equations. The new stalk node uses the existing
balanced-model localization theorem directly. This bypasses the redundant
functorial tensor-lift/affine-comparison packaging for this item.

The complete list removed from this item's direct `proof_deps` is:

- `def-pc-affine-base-change-into-pullback`
- `def-pc-derived-base-change-map`
- `lem-pc-affine-derived-base-change-comparison-map`
- `lem-pc-affine-derived-cohomology-presentation`
- `lem-pc-affine-derived-pullback-tensor-tilde`
- `lem-weil-pbc-localization-module-exact`
- `lem-weil-pbc-spec-tilde-stalk-localization`
- `new-affine-qcoh-derived-equivalence-core`

Except for the two packaging nodes described above, these are used indirectly
through the new coordinates and comparison nodes. Removing a direct DAG edge
here does not claim that its module leaves the targets' import closure.

The remaining former dependencies, including exact localization, tilde stalks,
affine pullback computation, cohomology presentation and the stalk map definition,
remain needed by the new partial comparisons or their statement definitions;
no claim is made that these mathematical branches are pruned.

## Where the brief, the DAG or earlier work was wrong

The planned declarations compute the ring span and its localization but do not
state its compatibility with the actual scheme-derived mate, or the precise
canonical stalk coordinate on the supplied representative. Those two bridge
statements have now been separated. The existing affine cohomology presentation
module provides stalk coordinates and naturality, not the natural affine
pushforward isomorphism d; that construction is part of the global bridge.

The item is not a unit's statement or realized step: the unit record's realized
lists are empty. The route retains the affine tensor cohomology calculation and
localization step of Stacks 0DJ8 and changes no unit or chapter record.

The literature checkout on this machine does not contain the cited perfect.tex
or blueprint unit file. Read the unit/chapter JSON records and the official
Stacks sources instead: https://stacks.math.columbia.edu/tag/0DJ8 and
https://stacks.math.columbia.edu/tag/06Y6. The new proof_origin records explicitly
mark the expanded bridge arguments as written by an agent.

LeanSearch was attempted and returned Internal Server Error. LeanFinder returned
cotangent-complex base change/localization results, which do not state these
comparisons; Loogle returned ordinary tilde/stalk infrastructure. Source grep
found existing exact-tilde proofs (private), BaseDerivedTensorCohomologyModel,
tensorPullback-tilde, and the balanced-model localization theorem. The private
exact-tilde argument is reused and proved here; no public identical declaration
was found. Blueprint search for affine base change cohomology returned no exact
match. These searches are recorded on every new node.

## New nodes

`def-pc-affine-base-change-tilde-coordinates`:
`Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates`. Constructs the canonical
target coordinate, tensor-source module, and tensor comparison arrow. It also
proves exactness of tilde using localized injectivity and preservation of
cokernels. No sorry is added.

`lem-pc-affine-base-change-tilde-global-comparison`:
`Sheaf.Algebra.Homology.AffineBaseChangeTildeGlobalComparison`. The global affine
mate square for the explicit module and arrow; one named sorry remains.

`lem-pc-affine-base-change-tilde-stalk-comparison`:
`Sheaf.Algebra.Homology.AffineBaseChangeTildeStalkComparison`. Localization of the
same explicit arrow agrees with the source-only stalk arrow; one named sorry
remains. It does not depend on the global comparison, so both are independent
proof items. Its statement is self-contained, and its Lean module does not import the global
node.

## Second reading by R3

1. Compared the whole original module with its sandbox version and compared the
   theorem signature byte for byte: identical. Only two proof imports and the
   proof body changed. The three other modules are new. No existing definition,
   signature, visibility or target changed, and no change record is required.
2. Compiled the delivered set and the item separately through lcompile.py.
   A scratch audit printed axioms for all eight declarations: the five coordinate
   declarations use only propext, Classical.choice and Quot.sound; the original
   theorem and the two comparison holes additionally use sorryAx. Exactly two
   named theorem holes remain, each `:= by sorry`; there is no prohibited command
   or hollow definition. The tensor-pullback coordinate is selected from an
   already proved unit-compatible isomorphism theorem. The existing tensor model
   is fixed up to compatible isomorphism by its universal counit, scalar action
   and comparison equations; no unconstrained existence witness is introduced.
3. Read both comparison statements and their complete docstring arguments against
   the affine cohomology and localization identities of
   [Stacks 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8) and the choice-independent
   derived change-of-rings construction of
   [Stacks 06Y6](https://stacks.math.columbia.edu/tag/06Y6).
   The global statement fixes U and a and asserts no stalk comparison; the stalk
   statement asserts no global presentation or mate square. They are strictly
   separate parts of the original argument, not restatements. Checked zero
   complexes, identity ring maps/localizations and empty prime spectra: none
   requires flatness of R to A or a nonzero ring. Repeated searches with
   `CategoryTheory.Functor.PreservesHomology` (Loogle) and natural affine derived
   pushforward/restriction of scalars (LeanFinder), and source grep with homology,
   pushforward and stalk keywords. Mathlib supplied general homology and ordinary
   pushforward infrastructure, not either complete comparison. Existing
   affineDerivedTilde_homology_comparison and
   qcoh_acyclic_derived_pushforward_cohomology give constituent comparisons but
   not the prescribed tensor-model mate or stalk square. Neither hole can be
   closed by one of these existing declarations alone.
4. Read from the original existential down through the explicit source/arrow and
   the two comparisons. The pushout construction and shared-witness packaging
   are actual reductions. All public imports in the new modules support signatures
   or public definition bodies; the original's two retained added imports are proof-only. A scratch copy compiled
   after removing both added Mathlib imports, confirming that those explicit
   imports were redundant; they were removed.
   In particular TensorPullbackTilde is needed by the public coordinate definition,
   so its public visibility is appropriate. The original dependency removals are
   now listed completely above. The unit sk-thm-picard-semicon has empty statement
   and step realization lists; no realized route is bypassed. Verdict: valid
   decomposition, one original hole closed and two lower holes added, net minus
   one hole, not an unconditional proof or a claimed closure improvement.
5. Compared each node with its Lean declaration and read its proof/dependency
   union and origin. The source node records pushout uniqueness followed by the
   global and stalk comparisons on identical coordinates. New comparison nodes
   record the remaining mathematical arguments and sources; the coordinate node
   records real definitions and proved exactness helpers. New nodes carry source,
   search, creation, blueprint, chapter/unit and Lean records. Verdict: consistent.

Second reading removed the two redundant Mathlib proof imports from the item.
It also completed the removed-direct-dependency list, recorded independent searches
and the axiom audit, and made the net hole count explicit in this report.
No proof-body repair or additional split was necessary; no module is claimed
pruned from the targets' transitive import closure.
