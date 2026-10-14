## What changed

Proved `AlgebraicGeometry.standardSingle_open_stalk_arrow` without changing its
signature or its docstring. Its proof applies derived open-arrow compatibility,
constructs the natural linear stalk comparison from Mathlib restriction-stalk maps,
and transports the square through degree-n homology. The scalar map is identified
using `Scheme.Opens.stalkIso_inv`. All private helpers are proved.

Added `Sheaf.AlgebraicGeometry.StandardSingleOpenDerivedArrow`, containing the proved
`AlgebraicGeometry.standardSingle_open_derived_arrow`. It works with an arbitrary chosen family of derived categories and specializes
`restricted_base_change_compatibility` to the pinned single-module counits and
transports its slice-site restricted coefficient through `overFunctorEquiv` to the
literal restriction used in the item. The pinned comparison predicate and its
coefficient naturality are proved locally. The mate naturality uses adjunction
Hom-equivalence naturality, the pinned composition comparison and the counit.
Neither theorem uses quasi-compactness,
quasi-separatedness, flatness, quasi-coherence, a point or a homology degree.

Added proof-only imports of that module and the source library's exact-functor
homology comparison. Updated the item's proof route and added the node for the
proved derived-arrow step. No existing statement, definition or public import was
changed. No other group's module was adapted.

## Proved and sorry left

Closed the item's sole hole: `AlgebraicGeometry.standardSingle_open_stalk_arrow`
(node `lem-pc-standard-single-open-stalk-arrow`).

Also proved the new `AlgebraicGeometry.standardSingle_open_derived_arrow`
(node `lem-pc-standard-single-open-derived-arrow`). There are no `sorry`s in either
delivered module and no holes added. This is a proof from the existing named
compatibility declarations, not a decomposition with new holes. Dependencies in
the shared library may still contain `sorry`; this delivery does not claim to close
those transitive holes.

The empty-open case of the item has no point satisfying `hV`; the derived helper
also applies to empty opens. Top opens and zero modules use the same natural
isomorphisms. The coefficient naturality proof applies to arbitrary module maps,
so it does not assume the module is flat or the single pullback counit invertible.

## No longer needed

No original import was removed: both public imports occur in the unchanged
statement. No delivered import is unused. The new derived helper imports the raw derived
mate and pinned single comparison definitions directly; it does not import
`StandardSingleBaseChangeMap`, whose standard specialization the target already
imports.

The direct proof dependency `lem-sc-open-module-stalk-restriction-comparison`
(`Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison`) is unnecessary:
its public theorem compares slice-site stalk functors for two opens, whereas this
proof constructs the linear ambient-stalk comparison directly from Mathlib. Its
private germ/linearity argument supplied the reusable proof pattern; the target
now contains proved private helpers with the necessary ambient interface.

The original direct proof dependencies
`lem-pc-restrict-derived-direct-image-open`,
`lem-weil-pbc-module-base-change-map-open-restriction`, and
`lem-pc-single-complex-open-counit-compatibility` are not applied by either new
proof. The geometric restriction machinery they describe is already packaged by
`restricted_base_change_compatibility`; those modules can remain in that theorem's
transitive closure. No claim is made that they are globally pruned.
`Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality` was removed from the new
helper: it would close an import cycle through the affine-global-Hom and proper-flat
model chain back to this item. Its short adjunction proof is reused as a proved
private helper against the definitions already imported. The original
compatibility dependency is now used by the proved derived-arrow helper.

## Where the brief, the DAG or earlier work was wrong

A dry run found that importing `DerivedBaseChangeNaturality` creates a cycle
back to this item. Its coefficient-naturality argument is reproduced privately
from the same pinned adjunction definition, with no new assumption or hole.
The direct naturality argument also used in `RelativelyFlatDerivedBaseChangeComplex`
avoids repeatedly unfolding the chosen adjunction while checking a normalized
composite; the derived helper stays abstract in the chosen derived-category family.
The target specializes this family to `HasDerivedCategory.standard`.
Profiling identified a redundant local `HasDerivedCategory` instance whose
normalization cost about twenty seconds. Removing that local alias gives the
same proof with the already available family instance, leaving ample room under
the sixty-second file limit. This changes no library definition or signature.

The planned last step's public open-module-stalk comparison has a slice-site
interface, not the linear ambient-module interface in the item. The latter is
proved from the additive restriction-stalk isomorphism and its germ formulas.
The planned derived compatibility theorem uses
`H = schemeOpenRestriction(Y,p inverse image S)(M)`, whereas the item uses literal
`M.restrict`. These coefficients are isomorphic via `overFunctorEquiv`; ignoring
that distinction would leave an unproved coefficient transport. The delivery
writes that transport and both naturality equations explicitly.

The existing docstring's Tag 0DJ7 refers to the stalk tensor base-change equation,
rather than the general derived mate construction. The new helper cites the
latter's actual source, [Stacks 08HY](https://stacks.math.columbia.edu/tag/08HY),
and the open direct-image comparison
[Stacks 08FE](https://stacks.math.columbia.edu/tag/08FE). The locality step was
checked at [Stacks 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9). The original
statement and docstring are preserved.

Searches were run through msearch.py (LeanFinder, Loogle, grep and LeanSearch).
LeanFinder found restriction-stalk isomorphisms; grep found `stalkIso_inv` and
`overFunctorEquiv`. Loogle did not know the project's exact-functor comparison;
LeanSearch returned an internal-server error. The searches are recorded in the
sandbox log and the new node. Blueprint search found no existing unit matching
this derived open-arrow step. The unit's realized route is preserved.

## New nodes

`lem-pc-standard-single-open-derived-arrow`, in
`dag/nodes/sec-picard-framework/lem-pc-standard-single-open-derived-arrow.json`,
records the proved square in the derived category before homology and stalks.
Its module is `Sheaf.AlgebraicGeometry.StandardSingleOpenDerivedArrow`. The node
records pinned-counit normalization, specialization of the existing compatibility
square, and coefficient transport/naturality. It carries no remaining hole and
stays in the item's chapter and unit. No change record is needed.

## Second reading by E1

1. Compared both delivered modules with the repository. The derived-arrow module is
   new. The existing stalk-arrow signature and docstring are byte-for-byte unchanged;
   its two public imports are unchanged. No existing definition or statement is altered.
   Verdict: pass; no change record or forced adaptation is required.
2. Read all proofs and constructions, then compiled both files through lcompile.py:
   34.1 s and 12.9 s, no errors or warnings. No delivered theorem contains sorry and
   no prohibited declaration or hollow definition occurs. The linear stalk maps are
   explicit maps from Mathlib's additive comparison; their inverses use proved
   bijectivity. Scratch #print axioms checks show only propext, Classical.choice,
   Quot.sound and inherited sorryAx. Thus the local holes are closed, while shared
   dependencies remain open. Verdict: pass with that transitive limitation.
3. There are no split-off holes. The new proved derived-arrow theorem is strictly
   the pre-homology step of the argument, not a restatement of the stalk theorem.
   Its coefficient transport is natural for all modules; no flatness is assumed.
   Empty opens require no point in the derived theorem; the target's empty V case
   is excluded by hV. Top opens and zero coefficients use the same comparisons.
   Repeated searches with different terms: LeanFinder for adjunction mate naturality,
   Loogle for homEquiv_naturality_left, grep for base-change naturality and linear
   restriction stalk maps, and rg across upstream and project sources. These found
   generic mate/Hom-equivalence tools and the known cyclic DerivedBaseChangeNaturality
   module, but no usable shorter replacement for the derived restriction square.
   The proof already uses the Hom-equivalence naturality lemmas. Verdict: pass.
4. Checked the proof from the target downward: derived square, exact-functor homology
   comparison, then a natural linear stalk comparison and categorical cancellation.
   Every public import in the new helper supplies names or instances in its statement;
   the compatibility theorem and exact-functor comparison are proof-only imports.
   The old proof dependencies omitted from the new route are all accounted for in
   No longer needed, including compatibility now used through the derived helper.
   No original import is removable and no globally pruned module is claimed.
   The unit record sk-thm-picard-coherence is unchanged (its realized entries are
   empty); these are local comparison steps below the unit, with no replacement of
   its coherence, Cech, or projective-space route. Verdict: pass.
5. Matched node statements, Lean declarations and proof routes. The new node's
   statement is verbatim the new theorem signature and its proof_deps are the union
   of step uses. Found and repaired one omission in the existing node: the final
   step unfolds standardSingleBaseChangeMap, so def-pc-standard-single-base-change-map
   must remain a proof dependency. The node now records it in that step and in
   proof_deps. The canonical-single dependency of the new node supplies its explicit
   construction; no invertibility theorem for arbitrary modules is invoked.
   Verdict: pass after this metadata repair.

Second-reader changes: restored the base-change-map definition dependency in the
stalk-arrow node and added this review. No Lean code needed repair. One original
hole closed (AlgebraicGeometry.standardSingle_open_stalk_arrow), zero holes added;
AlgebraicGeometry.standardSingle_open_derived_arrow is additionally proved.
