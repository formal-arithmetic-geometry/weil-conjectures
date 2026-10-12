## What changed

Proved `AlgebraicGeometry.Scheme.picard_cohomology_pullback` without changing its
signature. Degree one is assembled from the existing etale torsor pullback
functoriality and `classH1_eq_map_of_equivariant`, together with one new geometric
lemma giving an equivariant map to the tensor-pullback generator torsor.
Invertibility of tensor pullback is proved by uniqueness of the left adjoint to
module pushforward and transport of the existing Mathlib-pullback instance.

Degree zero is proved in full from
`Etale.cohomologyMap_zero_eq_globalSectionsUpperStarMap`, coefficient naturality,
the comparison adjunction identity, and composition of `appTop`. Three private
helpers are completely proved: `terminal_naturality`,
`torsor_terminal_independent`, and `classH1_map_of_hom`. They address the difference
between the chosen terminal etale object and the explicit identity object, and
avoid expensive elaboration of specialized torsor naturality terms.

The new proof-only import is
`Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackEquivariant`. Both sandbox modules
compile cleanly through lcompile.py --all (approximately 4 and 16 seconds).
The main theorem uses the default heartbeat limit. All public imports are preserved.
The item node's proof and proof dependencies now describe the Lean argument.

## Proved and sorry left

The original one sorry, in
`AlgebraicGeometry.Scheme.picard_cohomology_pullback`
(node `lem-sc-h1-gm-pic-pullback`), is eliminated by a complete Lean reduction.
There is no sorry left in the item's module, including its private helpers.

One new sorry is left:
`AlgebraicGeometry.Scheme.Modules.etale_generators_pullback_equivariant`
(node `lem-sc-etale-generators-pullback-equivariant`), in the new module
`Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackEquivariant`.
Its conclusion is a sheaf morphism and its equivariance identity; it mentions
neither Picard classes nor cohomology, so it is strictly the geometric step of
the argument. The existing dependency
`CategoryTheory.Sheaf.Torsor.etale_torsor_h1_functoriality` remains unproved in the
library and is used as intended by stage 3; it is not changed in this delivery.

## No longer needed

Removed direct proof import
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`:
node `lem-weil-pbc-cohomology-pullback-functorial` is not used separately by this
proof. It remains indirectly imported by the required torsor-functoriality module;
this delivery therefore does not claim that its module is globally unreachable.

Removed redundant direct imports
`WeilConjectures.AlgebraicGeometry.Sites.Gm`,
`WeilConjectures.CategoryTheory.Sites.Torsor`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
Their declarations remain used through the retained public imports.
No other existing proof dependency is removed. The contracted-product construction
and clause (2) of torsor functoriality are not used by the assembly: the existing
coefficient-equivariant-map theorem supplies the same class identity directly.
No unit statement or realized step is bypassed; the unit's realized fields are empty.

## Where the brief, the DAG or earlier work was wrong

The DAG's geometric step 2 was marked elementary but has no corresponding
usable Lean declaration: it requires constructing the generator map out of a
sheafified inverse image and proving its action compatibility. This is the one
new lemma. Merely applying the existing cohomology or torsor functoriality results
does not supply that geometric morphism.

The stated torsor functoriality and degree-zero theorem use the chosen terminal
objects, whereas the target uses explicit identity etale objects. These are not
definitionally equal. The proved private helpers transport the section and torsor
class identifications without adding any assumptions or new sorries.

The existing citation to Tag 03AH concerns the definition of torsors; the argument
that an equivariant map realizes change of group is supplied here by the already
proved `classH1_eq_map_of_equivariant`. Tag 040E was read online for its generator
construction because the literature tex is not present in this remote checkout.

## New nodes

`lem-sc-etale-generators-pullback-equivariant` states the missing geometric map
from an inverse-image generator torsor, identified by a sheaf isomorphism respecting
the adjunction-unit action, to the generator torsor of tensor pullback. Its proof
in words constructs pulled-back generators, extends by the inverse-image
adjunction and sheafification, and checks equivariance locally using the tensor
identity. Its public theorem has exactly `:= by sorry` as its proof.

The statement was checked conceptually for the identity morphism, the structure
line bundle, and the empty scheme: it is respectively the generator identification,
the units comparison, and the unique map of empty-site sheaves. The supplied
isomorphism eT can be arbitrary only subject to the specified action compatibility;
that compatibility is essential and is included in full. No new invertibility
hypothesis is imposed on the original theorem: the needed instance is proved there.

Mathlib searches were run through msearch.py: LeanFinder returned topological
vector-bundle results, Loogle returned general module pullback declarations,
grep found no etale generator-pullback result, and LeanSearch returned HTTP 500
(recorded as unavailable). Blueprint and repository searches found no existing
statement for this morphism. The new node inherits the item's chapter and unit
and refers to the original blueprint's Picard compatibility step. No change
record is needed, because no existing statement, definition, or public import
is changed.

## Second reading by R2

1. Compared both delivered modules with the repository. The only existing declaration,
   `AlgebraicGeometry.Scheme.picard_cohomology_pullback`, has a byte-for-byte unchanged
   signature; the declaration parser also reports no statement changes. There are no
   changed definitions. Restored the existing theorem's docstring, which accidentally
   called the pullback `Limits.pullback`. No change record is required.
2. Compiled both modules in import order with lcompile.py after the repairs: clean,
   approximately 5 and 17 seconds. The only textual sorry is the whole proof of the
   named geometric theorem listed above; no forbidden declaration or hollow definition
   occurs. Compiled a scratch copy with #print axioms for the main theorem, new theorem,
   and all three private helpers. Each helper uses only propext, Classical.choice and
   Quot.sound. The main and split-off theorems additionally use sorryAx, as expected
   from the named open geometric lemma and the existing torsor-functoriality dependency.
   This delivery closes the original local sorry by a reduction, not an axiom-free target.
3. Read the new theorem's complete statement, docstring argument, and node. It is the
   geometric step alone: no Picard class or cohomology occurs in its conclusion. Its
   action compatibility assumption is essential and exactly supplied by the existing
   torsor pullback theorem. Checked identity pullback (including translating eT), the
   trivial line bundle (the units comparison), and the empty scheme (unique sections).
   The extension argument is valid: base change of etale objects preserves finite
   limits, so representatives of a group section and a torsor section admit a common
   local refinement; the two inverse-image adjunction units give the pulled-back action.
   Independent searches used LeanFinder for natural maps of line-bundle trivializations,
   Loogle for pullback/IsInvertible, and grep for torsor/pullback and Iso/pullback.
   They found scalar compatibility and module pullback ingredients, not this result.
   Repository searches found the existing free-generator pullback lemmas and torsor
   isomorphism lemmas; they do not construct this inverse-image sheaf map. Re-read
   https://stacks.math.columbia.edu/tag/040E: it supplies the generator torsor construction;
   its pullback argument here is an elaboration, not a verbatim lemma in that source.
   Completing the new lemma requires geometric sheaf-map and coherence construction,
   rather than a few-minute application of an existing result.
4. Read the reduction from the theorem downward: invertibility is transported through
   uniqueness of left adjoints, the degree-one clause uses the existing torsor pullback
   theorem and proved coefficient-equivariance theorem, and degree zero is calculated
   in full. No shorter complete route was found. Narrowed the new module's public
   EtalePicard import to EtaleIsoTorsor, which supplies the actual signature dependency.
   All remaining imports supply signature dependencies or declarations used by proofs;
   the new module is imported privately by the item. The retained public degree-zero
   module exports the cohomologyMap definition used in the signature. The No longer
   needed section lists the sole removed old proof dependency, as confirmed by comparing
   the old and new proof_deps. Read dag/units/sk-prop-ext-invariance.json: its realized
   statement and all three realized steps are empty; the Kummer/Picard route is preserved.
5. Compared the existing node field by field: only proof, proof_deps, and proof_origin
   change. Their steps describe the code, and proof_deps is the union of their uses.
   The new node has the required source, statement dependencies, stepwise proof,
   searches, origin, creation record, inherited chapter/unit, and exact Lean signature.
   Both node declarations match their modules. Verdict: pass as a partial stage-3
   reduction with one genuine geometric statement split off.

Second reading changed only the accidental existing docstring edit and the new
module's overly broad public import; the mathematical proof and node statements
were left intact. The delivery dry run and final push follow this review.
