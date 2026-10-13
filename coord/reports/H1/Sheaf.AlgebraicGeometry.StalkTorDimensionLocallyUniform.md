## What changed

Replaced the sorry in `AlgebraicGeometry.stalkTorDimension_locally_uniform` by a complete
Lean proof selecting an affine target neighbourhood of f(x), then an affine source
neighbourhood inside its preimage. Two new proof-only imports implement the two
substantive steps already described by the node: finite Tor dimension for the affine
coordinate algebra, and preservation of a fixed bound when passing to source and target
stalks. Updated the original node's proof, proof_deps and proof_origin to match.
All existing signatures, public imports and docstrings are unchanged. No definition or
statement was changed and no other module was adapted. The unit record
`dag/units/sk-thm-picard-duality.json` is unchanged; this is the original route below it.

## Proved and sorry left

Closed: `AlgebraicGeometry.stalkTorDimension_locally_uniform`
(node `lem-pc-stalk-tor-dimension-locally-uniform`), one of one original holes.
There is no sorry left in the item module.

Added, both public theorems with exactly `:= by sorry`:

- `AlgebraicGeometry.affineSections_finiteTorDimension_of_stalkwise`
  (`lem-pc-affine-sections-finite-tor-of-stalkwise`). Its conclusion is a finite
  Tor bound for the coordinate ring Γ(V,O_X) over Γ(U,O_Y), rather than a bound for
  source stalks on a neighbourhood.
- `AlgebraicGeometry.affineSections_torBound_stalk`
  (`lem-pc-affine-sections-tor-bound-stalk`). It assumes an already fixed coordinate
  bound and preserves that exact bound at stalks. It has no Noetherian, finite type,
  or stalkwise finite Tor hypothesis and does not produce a bound.

This is a decomposition, not a sorry-free mathematical proof: one hole closed, two
holes added, net -1. The two pieces are distinct steps with different inputs and
outputs, not renamed versions of the item. All three files compile in import order
using lcompile.py. No axiom, private sorry or data definition was added.

## No longer needed

No existing import, node or module is pruned. The original proof dependency
`def-pc-perfect-morphism` is still a statement dependency and is used in the new
coordinate-ring lemma; its original public import remains. The original two steps
are retained and made into Lean, so no global work is claimed to be unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original node lists only the definition `def-pc-perfect-morphism` as a proof
dependency. Its polynomial/perfectness step and its localization step have no
matching stated dependency. The two new nodes expose precisely those missing steps.
The existing affine sheafification Tor-amplitude criterion assumes a sheaf Tor bound
already and does not supply the stalkwise-to-coordinate implication.

Read Stacks Tags 069C, 09U9, 0B67, 068X and 068W online because the local Stacks .tex
files are absent. Tag 068W requires bounded-below cohomology for global perfection;
the module B concentrated in degree zero satisfies this. The docstring explicitly
includes this condition. Tag 0B67 omits the proof of the direction needed here; the
new localization docstring expands it through flat localization and balanced Tor.

Checked edge cases for both new statements: empty affine source (zero coordinate
ring), d = 0, flat maps, and bases with no dimension bound. Neither statement
requires X quasi-compact. No arbitrary witness was chosen to define data.

Mathlib searches were run through msearch.py: LeanFinder returned finite-type and
Noetherian scheme declarations for the coordinate lemma and projective Tor vanishing
and flat-localization declarations for localization; none gives the required result.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as a negative match.
Loogle `Tor` returned an unknown identifier. Grep found no matching finite Tor
localization theorem; Mathlib/RingTheory/Flat/CategoryTheory.lean explicitly lists
relating flatness with Tor as future work. Blueprint searches for Tor dimension,
finite tor, localization, 069C and 0B67 found no duplicate of the new statements.

## New nodes

`lem-pc-affine-sections-finite-tor-of-stalkwise`, in
`lean/Sheaf/AlgebraicGeometry/AffineSectionsFiniteTorOfStalkwise.lean`, isolates the
polynomial presentation argument of Tag 069C. Its proof in words uses Noetherianity
to obtain pseudo-coherence, polynomial fibres and Tag 068X for local perfection,
then bounded-below Tag 068W to obtain a bounded flat resolution over the base.

`lem-pc-affine-sections-tor-bound-stalk`, in
`lean/Sheaf/AlgebraicGeometry/AffineSectionsTorBoundStalk.lean`, isolates fixed-bound
localization, Tag 0B67 (`lemma-tor-amplitude-localization`) applied to B in degree zero,
with the section/stalk identification used by Tag 069C. Its proof in words explains
the scalar restriction, localization of Tor and compatibility with f.stalkMap.

Both nodes are in `dag/nodes/sec-picard-framework/`, carry full Lean signatures,
source citations, proof text, actual search records and the item's unit and chapter.
There are no change records because no existing interface changed.

## Second reading by H1

1. **Interfaces: pass.** Read the full diff of the item against the repository.
   Only two plain proof imports and the theorem's proof change; the existing
   signature, visibility, public imports, definitions and docstrings are byte
   for byte unchanged. The other two modules are new, with no existing interface
   to replace. There is no statement change or forced adaptation.
2. **Lean proof and axioms: pass as a decomposition.** Recompiled all three
   modules in dependency order through lcompile.py, without errors or warnings.
   A scratch copy with explicit `#print axioms` checks shows only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` for all three declarations. The only textual holes are the two reported public
   named theorems, each with its entire proof `:= by sorry`. No data definition,
   axiom, unsafe declaration, opaque declaration or foreign implementation is
   introduced. The item is an assembly proof, not an axiom-clean result.
3. **Split statements: pass.** Independently read Stacks Tags 069C, 068X,
   068W and 0B67 online. For the coordinate lemma, affine finite-type source
   and target give a finite-type algebra over a Noetherian ring; a finite
   polynomial presentation makes the quotient pseudo-coherent. At a polynomial
   prime containing the kernel its localization is the corresponding source
   stalk; otherwise it is zero. The flat localized polynomial map has fibres
   of global dimension at most the number of variables, so 068X applies.
   The degree-zero complex is bounded below, as required by 068W to deduce
   global perfection. Its bounded projective polynomial resolution is flat
   over the base and supplies the coordinate Tor bound. For localization,
   base localization of a projective resolution first preserves the bound
   for every localized-base module; balanced Tor then lets exact localization
   in the algebra variable preserve the same bound. The affine germ-map
   compatibility identifies the resulting ring map with the actual stalk map.
   Tested empty V (zero algebra and vacuous stalk assertion), d = 0 (flatness),
   identity maps, and a Noetherian base without a dimension bound. No global
   quasi-compactness of X or uniform input stalk bound is used. Both docstrings
   contain the full arguments, sources and matching blueprint ids. The first
   lemma produces a coordinate bound, not the item's neighbourhood conclusion;
   the second assumes a fixed bound and only transports it. They are distinct
   proper steps, not copies of the target.
   New independent LeanFinder queries used “bounded flat dimension” and
   “Tor homology of a localized module”; results were smooth/flat ring maps
   and tensor-localization comparisons, not either statement. Direct rg on
   Mathlib's Tor and Flat modules and on lean/Sheaf, lean/WeilConjectures and
   dag/nodes found no duplicate. Mathlib's Tor file still explicitly notes
   that balancedness needs further theory, so neither remaining hole can be
   closed by a short application of its current API. Searches are also logged
   by msearch.py in searches.jsonl.
4. **Route and pruning: pass.** The proof chooses an affine target open and
   an affine source open in its preimage, obtains d on sections, then preserves
   that exact d at all stalks in the source open. Every added proof import is
   used. The public imports supply types and instances in the signatures.
   The old direct proof dependency `def-pc-perfect-morphism` is no longer in
   the item's proof_deps; it remains a statement dependency and an input to
   the coordinate lemma, so its module is not pruned. There are no other old
   proof dependencies to remove. The unchanged unit record
   sk-thm-picard-duality has realized.statement = [] and realized.steps = [[]];
   no unit realization or prescribed step has been bypassed.
5. **DAG: pass.** Compared the existing node against the repository: only
   proof, proof_deps and proof_origin change, matching the two actual lemma
   applications. Checked each new node's declaration and verbatim signature,
   source, docstring proof, dependency union, searches, status, creation record,
   blueprint ancestry, chapter and unit. Each new module has its own node.

Second reading changed only this report: recorded the independent checks,
explicitly identified the old definition's removal as a direct proof dependency,
and confirmed the decomposition count (one hole closed, two added, net -1).
No Lean or DAG repair was needed; no further hole was closed or import pruned.
