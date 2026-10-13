## What changed

Proved the body of AlgebraicGeometry.exists_affineBaseChangeOrdinaryStalkComparison
from two strictly smaller intermediate statements. Its signature, visibility and
existing public imports are unchanged. Added a proof-only import of
Sheaf.Algebra.Homology.AffineLocalizedTensorStalkSquare. The proof obtains a
termwise germ-normalized chain isomorphism, applies the algebraic localization
square to it, and composes the two equations in Lean.

Added AffineOrdinaryTensorStalkCoordinates and AffineLocalizedTensorStalkSquare.
The former has no source cohomology model, derived module-category assumptions or
K-flatness assumption; the latter has no derived sheaf-homology target coordinate
and applies to any chain isomorphism satisfying the specified germ formula.
The common map affineTildeHomologyLocalization is a complete construction from
IsLocalizedModule.iso, exact tilde homology and affineRepresentativeStalkIso.
No arbitrary witness of an unproved existence theorem is used in a definition.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.exists_affineBaseChangeOrdinaryStalkComparison
(node lem-pc-affine-base-change-ordinary-stalk-comparison).
Added two holes, exactly the public theorem bodies:

- AlgebraicGeometry.exists_affineOrdinaryTensorStalkCoordinates
  (lem-pc-affine-ordinary-tensor-stalk-coordinates).
- AlgebraicGeometry.exists_affineLocalizedTensorStalkSquare
  (lem-pc-affine-localized-tensor-stalk-square).

This is a decomposition, not a sorry-free proof of the mathematical result.
There are no holes in the item's module, in private helpers or in definitions.
The new statements were checked on zero complexes, identity localizations,
arbitrary degrees, and zero rings (which supply no prime). The termwise germ
formula normalizes tau; compatibility is not asserted for arbitrary additive
source equivalences.

## No longer needed

None. The original public imports are needed by the unchanged statement. The
old direct proof dependencies remain needed transitively in the two new nodes;
no node or module is claimed pruned. The unused KFlat import was removed
from the new ordinary coordinate module, whose statement has no K-flatness
assumption. The target's direct proof_deps now name
exactly the two intermediate nodes.

## Where the brief, the DAG or earlier work was wrong

The original DAG packages the algebraic localization square and identification
of the ordinary sheaf target into one step. Its localization theorem concerns
ring-complex coordinates and needs explicit transport to the actual stalk
complex and to the ordinary target coordinate; it cannot be applied directly
to the original conclusion. The new interfaces make these two separate steps
precise without changing the target. The unit route is retained.

LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and source
searches were performed. No existing exact match was found. The local clone does
not contain the literature TeX, so the Stacks pages 0DJ8 and 01I9 were read directly.

## New nodes

lem-pc-affine-ordinary-tensor-stalk-coordinates: the chain identification determined
by its unit pure-tensor germ formula and its ordinary target-coordinate equation.
It also records the completely constructed ordinary tilde homology-localization
map. Source: Stacks 0DJ8, 01I9, 01HV and 01AG.

lem-pc-affine-localized-tensor-stalk-square: the algebraic derived tensor
localization square in any chain coordinates satisfying that germ formula.
Source: Stacks 0DJ8 and 06Y6. Both nodes inherit the item's chapter and unit.
No statement change record or forced adaptation is needed.

## Second reading by H3

1. Interface: compared the delivered item with the repository using diff. The
   entire existing theorem signature, universes, hypotheses, conclusion and
   visibility are byte-for-byte unchanged. The only Lean changes are a plain
   proof import, a local heartbeat option and the proof body. The two other
   modules are new; no statement change record or forced adaptation is needed.
2. Proof: compiled all three modules in import order through lcompile.py, with
   no errors or warnings. A scratch-copy #print axioms check of all four
   delivered declarations found only propext, Classical.choice and Quot.sound
   for affineTildeHomologyLocalization; the three theorems additionally depend
   on sorryAx from the documented open statements. The scratch copy was removed.
   The item rewrites the target-coordinate equation and
   the localized square, then evaluates ModuleCat compositions. Exactly the two
   reported public theorem bodies remain sorry. affineTildeHomologyLocalization
   constructs its equivalence from IsLocalizedModule.iso, mapped tilde homology
   and affineRepresentativeStalkIso, with no data chosen from a holed existence
   theorem. No prohibited declaration or hidden proof hole was found.
3. Split statements: read Stacks [0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
   (the affine localization identity), [01I9](https://stacks.math.columbia.edu/tag/01I9)
   (functorial tilde pullback), and [06Y6](https://stacks.math.columbia.edu/tag/06Y6)
   (derived change of rings). Read exists_tensorPullback_tilde_iso, its unit
   normalization, exists_tensorStalkIso and its specified components,
   affineRepresentativeStalkIso and its naturality, and
   derivedTensor_localization_cohomology with its comparison square. The first
   split only concerns ordinary target coordinates, for arbitrary complexes;
   it requires no m or K-flatness. The second concerns the algebraic source
   comparison and ends at homology of the stalk complex, without the final
   derived-sheaf target coordinate. Thus neither is a renamed original theorem.
   Stalk-linearity and localization show that the stipulated unit-tensor germs
   generate; they fix tau, so the second statement does not wrongly quantify
   over arbitrary additive coordinates. For identity maps the factors cancel
   to the localization comparison; zero complexes give zero maps and zero
   homology; every integer degree is allowed; a zero fourth ring has no primes.
   Both docstrings supply the construction and comparison argument, and each
   hole has its node. Additional msearch LeanFinder query on localized homology
   and stalk coordinates returned the individual Mathlib tilde-stalk interfaces;
   Loogle on ShortComplex.mapHomologyIso reported an unknown identifier; grep
   on stalk/homology returned exact-stalk facts in Topology/Sheaves/Abelian.
   Source searches in lean/ and the upstream PullbackTilde module found no exact
   replacement for either split statement. The existing ring localization
   theorem requires the ring-complex-to-sheaf-stalk transport isolated here.
4. Route and imports: the top proof uses precisely the two smaller results.
   Its existing public imports supply the unchanged signature; the new import
   is proof-only. Each new public import supplies notation or a definition in
   its statement. The old direct proof dependencies are all retained
   transitively: derived-tensor-localization-cohomology, the source model,
   localization-module-exact, spec-tilde-stalk-localization, the stalk condition,
   and affine-tensor-pullback-stalk-coordinates. No old node or library module is
   pruned. Read dag/units/sk-thm-picard-semicon.json: its realized statement and
   step lists are empty; neither the unit statement nor its base-change route
   is replaced or changed. The decomposition retains the affine localization
   argument of its blueprint ancestor.
5. DAG: the existing node differs only in proof, proof_deps and proof_origin.
   Its two named dependencies match the two theorem applications. Both new
   nodes' lean.statement fields match their Lean theorem signatures verbatim;
   their declaration lists include the new constructed equivalence where
   relevant. Source, complete proof steps, dependency unions, creation record,
   chapter, unit, blueprint provenance and actual search records are present.

Verdict: acceptable decomposition, closing one original hole and adding two
strictly smaller holes (net minus one), not a sorry-free result. No mathematical
or Lean repair was necessary. Second reading added this independent review only;
no proof, definition, signature or node was rewritten.
