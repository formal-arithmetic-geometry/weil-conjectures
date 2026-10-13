## What changed

Replaced the sole remaining `sorry` in
`Sheaf.AlgebraicGeometry.DiagonalConormalAffineSectionsChosen` with a complete,
compiling reduction. The statement and visibility of both existing theorems are
unchanged. The previously proved `diagonalConormalDerivation_ext` is unchanged.

The proof constructs the ring derivation on affine sections directly from the
chosen presheaf derivation. It proves vanishing on base sections using
`Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app` and
`PresheafOfModules.Derivation'.d_app`, then constructs its linear Kähler lift
using `ModuleCat.Derivation.desc`. The formula on differentials follows from
`ModuleCat.Derivation.desc_d`. Injectivity and generation of the conormal
sections are isolated in two new modules, imported privately for the proof.
The proof derives surjectivity from the generation statement: each generator
D(a) has the explicit preimage da, so the linear-map range contains their span.
`LinearEquiv.ofBijective` then constructs the equivalence with its proved formula.
No definition chooses an arbitrary witness of an existence theorem.

Updated `stage3-diagonal-conormal-chosen` in the sandbox so its numbered proof
and dependencies describe this construction, injectivity, span-to-surjectivity
argument and final equivalence. Added the two matching new nodes.

Validation: all three delivered Lean modules compile together through
`lcompile.py --all`, in import order, without compiler warnings. The required
`deliver3.py --no-push` dry run is the final validation; nothing is pushed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_affine_sections_for_chosen_derivation`
(node `stage3-diagonal-conormal-chosen`). There are no remaining sorries in the
item module. Its other theorem, `AlgebraicGeometry.diagonalConormalDerivation_ext`,
was already proved and is not counted as a newly closed hole.

Added exactly two holes, each the full body `:= by sorry` of one public theorem
in its own new module:

- `AlgebraicGeometry.diagonalConormal_affine_lift_injective`, module
  `Sheaf.AlgebraicGeometry.DiagonalConormalAffineLiftInjective`, node
  `stage3-diagonal-conormal-affine-lift-injective`.
- `AlgebraicGeometry.diagonalConormal_affine_derivation_span`, module
  `Sheaf.AlgebraicGeometry.DiagonalConormalAffineDerivationSpan`, node
  `stage3-diagonal-conormal-affine-derivation-span`.

This is a decomposition, not a complete geometric proof or a net reduction of
holes: one hole closed and two added, net minus one before the project's closure
ledger computes shared dependencies. The first new statement only asserts
injectivity for a supplied linear lift; the second only asserts that normalized
derivation values span the actual target, without a comparison map or any
injectivity assertion. Neither alone is the original equivalence theorem.
The construction of the lift and the proof combining these distinct facts are
actual Lean proofs in the item module.

The docstrings and nodes give complete natural-language arguments from the
local closed diagonal, the actual restricted kernel, tensor pullback and J/J²,
including the unit formula. The closed-immersion affine theorem cannot be
applied directly to the global diagonal: proving its restriction and adjunction
transport to U ×_V U remains part of the new items, and is explicitly named.

Edge cases checked mathematically against the affine calculation: the empty
chart has zero section modules; identity and open immersions have zero local
diagonal cotangent; a polynomial algebra gives the usual free differential
module; no smoothness, reducedness, finite type, characteristic or separatedness
is assumed. For a nonseparated morphism only the closed diagonal on the local
open U ×_V U is used. The sign is 1 tensor a minus a tensor 1, agreeing with
`IsDiagonalConormalDerivation` and `KaehlerDifferential.D_apply`.

## No longer needed

None. No old imports are removed: the public derivation import supplies the
statements and the existing private uniqueness import is still used by the
unchanged extensionality theorem. No old node or module has been shown unnecessary
by this reduction. In particular the normalized derivation existence node remains
needed. The two new proof imports are both used.

The already stated `DiagonalConormalAffineSections`, its `Base` module, and
`DiagonalConormalAffineComparison` cannot supply a shorter proof: they depend
on this item. They were not imported, and this is not claimed as pruning.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The chosen node's only proof step named the
normalized derivation existence theorem, whose statement explicitly asserts no
universal property or affine bijectivity. That statement therefore constructs D
but does not supply the missing affine calculation. The reduction makes the two
remaining obligations explicit rather than assuming a consequence of existence.

Read the sources online because `literature/stacks-project/morphisms.tex` is not
present on this machine: [08S2](https://stacks.math.columbia.edu/tag/08S2),
[01R3](https://stacks.math.columbia.edu/tag/01R3), and
[01KJ](https://stacks.math.columbia.edu/tag/01KJ). Mathlib's
`RingTheory/Kaehler/Basic.lean` gives the ring-level quotient construction,
`D_apply`, `span_range_derivation`, and `submodule_span_range_eq_ideal`.
The generic `affine_conormal_sections_existence` theorem was read, including
its signature, but it concerns `i.ker.toModules` for a closed immersion, whereas
the present conormal uses the actual module-sheaf kernel of the global diagonal.
The necessary open-chart identification is not provided directly by its interface.

`tools/blueprint_refs.py ancestor stage3-diagonal-conormal-chosen` reports None:
the existing node uses module names in its creation history and a string for
`blueprint.from`. Its historical fields are not edited. New-node provenance is
traced through the existing derivation node to `lem-sc-finite-duality` and the
same diagonal-conormal affine calculation. Searching the imported blueprint for
“diagonal conormal” found no matching blueprint node. The unit record
`sk-thm-picard-duality` and its `realized` fields are unchanged.

## New nodes

`stage3-diagonal-conormal-affine-lift-injective` states only the injectivity of
a supplied normalized affine Kähler lift. Its proof identifies the local conormal
sections with J/J² and uses the ring definition and differential generators to
show that the lift becomes the identity. No surjectivity conclusion is included.

`stage3-diagonal-conormal-affine-derivation-span` states only generation of
conormal sections by the normalized derivation values. Its proof uses generation
of the multiplication ideal by tensor differences and the surjective quotient
class map, not the injectivity of the Kähler lift.

Both statements have source Tag 08S2's affine calculation, with 01KJ and 01R3
for the chart and the class-map identification, and 00RW for the ring calculation.
Each has the same chapter and unit as the item. The generic closed-immersion
conormal node `lem-weil-pbc-affine-conormal-sections-existence` is a tool in their
future proofs; it does not replace the unit's route. Its statement is used only
after restricting to the closed affine diagonal and identifying its ideal module.

Searches actually run through `msearch.py`: LeanSearch for generation and
injectivity (unavailable, HTTP Internal Server Error, recorded as unavailable),
LeanFinder for the diagonal cotangent equivalence and for generation (ring
Kähler declarations only), Loogle for `KaehlerDifferential.D` and
`LinearMap.range_eq_top`, and grep for diagonal conormal span/injectivity (no hits).
Additional `rg` searches read the project's generic affine conormal theorem and
Mathlib's ring quotient and derivation declarations. No exact usable theorem for
either new scheme-section statement was found. No change record or forced
adaptation is needed: all old signatures and public imports remain identical.

## Second reading by N3

1. Compared the complete delivered item module with the repository version by
   `diff -u`. Both existing declaration signatures, visibility and docstrings
   are byte for byte unchanged. The only Lean changes are two private proof
   imports and the body of `exists_affine_sections_for_chosen_derivation`.
   No definitions, target statements or existing public imports change. Pass.
2. Compiled all three modules in dependency order through `lcompile.py --all`: no
   errors or warnings. Scanned every delivered Lean file for forbidden constructs
   and holes: exactly the two reported named theorem holes, no definitions or
   additional holes. Compiled a temporary copy with `#print axioms` for all four
   declarations. The extensionality theorem uses only propext, Classical.choice
   and Quot.sound; the other three also use sorryAx from still-open statements.
   The temporary copy was removed. The chosen derivation is uniquely determined
   by normalization, as the unchanged extensionality theorem proves; the linear
   lift is constructed directly, not chosen from an arbitrary existence hole. Pass.
3. Read both split statements, docstrings and nodes. They assert distinct strictly
   partial obligations (injectivity and generation), and neither restates the
   target equivalence. Checked empty charts, identity/open immersions, polynomial
   algebras, and the nonseparated case using the closed local diagonal. Verified
   the first-factor A-action, sign, quotient class map, and the Mathlib source of
   `submodule_span_range_eq_ideal`, `D_apply` and `span_range_derivation`. Read
   Stacks Tags [08S2](https://stacks.math.columbia.edu/tag/08S2),
   [01R3](https://stacks.math.columbia.edu/tag/01R3), and
   [01KJ](https://stacks.math.columbia.edu/tag/01KJ). Independently searched using
   msearch LeanFinder for cotangent generation by pullback differences, Loogle
   for `KaehlerDifferential, Function.Injective`, and grep for cotangent diagonal
   or conormal sections; no directly usable scheme-section theorem appeared.
   Read the existing generic closed-immersion affine conormal theorem: applying it
   here still requires the restriction and kernel/adjunction identifications
   described in the new docstrings. Neither hole can be closed by a short
   application of that interface. Pass as a decomposition, not a net proof gain.
4. Followed the actual proof from the target down: derivation construction,
   universal linear lift, injectivity, span-to-range surjectivity, and
   `LinearEquiv.ofBijective`. Both new private imports are used, and the old
   private uniqueness import is used by extensionality. The old proof dependency
   (normalized derivation existence) remains used, so `No longer needed: None`
   is complete. Read the downstream affine comparison and its import chain;
   reusing it would be circular. Read `dag/units/sk-thm-picard-duality.json`: its
   realized fields and route are unchanged; the split is below unit level. Pass.
5. Checked all three nodes against their Lean signatures and proof. Every
   `proof_deps` is the union of step uses; the existing node changes only proof,
   proof_deps and proof_origin. The new nodes have matching verbatim signatures,
   source, provenance, searches, creation, chapter/unit and Lean records. The
   target node records exactly the reduction that compiles. Pass.

Changes made by this reading: appended this review and recorded independent
searches; no Lean proof, statement, import or node repairs were necessary.
One original hole is closed and two are added; the already proved
`diagonalConormalDerivation_ext` is not counted as a newly proved hole.
