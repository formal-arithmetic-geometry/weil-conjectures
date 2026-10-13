## What changed

Replaced the sole sorry in
`AlgebraicGeometry.exists_mixedAffineSectionsBaseChangeMate` with a complete Lean
proof from two strictly intermediate comparison statements. All existing signatures,
universes, definitions, and public imports are unchanged.

The proof takes the affine extension/sections comparison at Q = Rf_*E, extends the
inverse Leray comparison to construct a, and takes d to be the existing normalized
mixed Leray isomorphism for f'. It proves the transported unit equation by naturality.
For arbitrary L and m, it applies injectivity of the scalar adjunction Hom equivalence,
uses naturality of d, substitutes the base-change unit square, and applies naturality
of the scalar-square and g_X Leray comparisons. The final equality is the adjunction
identity eta_gX(E) followed by RgX_*(adjunct(m)) = m.

Added `Sheaf.AlgebraicGeometry.MixedExtensionSectionsUnit` and
`Sheaf.AlgebraicGeometry.MixedSectionsBaseChangeUnitSquare`, each with one public
statement, its source and a proof in words. Updated the parent's proof route and
proof dependencies. This follows the original four-step plan and preserves the unit
route (the unit's realized arrays are empty); no statement correction is made.

All three files compile together with lcompile.py --all, without warnings. The
parent proof is about 55 lines and has no sorry. The existing equal-universe spectra
analogue was read as a guide, but cannot instantiate the independent w and wA or
arbitrary affine Y and Y'.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_mixedAffineSectionsBaseChangeMate`
(node `lem-sc-mixed-affine-sections-base-change-mate`). No sorry remains in the
item's module.

Added two holes, both with proofs exactly `:= by sorry`:

- `AlgebraicGeometry.exists_mixedExtensionSectionsUnit`
  (node `lem-sc-mixed-extension-sections-unit`). This concerns only g and Q,
  and asserts an affine source comparison with its fixed unit; no f, square,
  base-change map, L or m occurs.
- `AlgebraicGeometry.mixedSectionsBaseChange_unit_square`
  (node `lem-sc-mixed-sections-base-change-unit-square`). This is an equality
  for the canonical sheaf unit at E, without affine or quasi-coherence hypotheses;
  it constructs no scalar-extension source isomorphism and handles no arbitrary m.

This is a decomposition, not a complete foundational proof: one original hole
closed, two simpler holes added, net minus one. Existing imported dependencies may
still rest on sorry. No data definition was added or changed, and no arbitrary
witness is extracted into a definition.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
  (`lem-pc-affine-qcoh-derived-equivalence`).
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`
  (`lem-pc-affine-derived-pullback-tensor-tilde`).
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`
  (`lem-pc-ringed-spaces-derived-direct-image-composition`).

These remain needed below the new intermediate statements: the first two in the
source comparison and the third in the unit square. Therefore no module is claimed
pruned from the targets' import closure. The parent now imports only the two new
proof modules in place of these three direct imports. All public statement imports
remain unchanged. No unit-level node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent's proof-dependency statements supply the affine equivalence, K-flat
pullback formula, and normalized Leray comparisons, but their signatures do not
state the two required compatibility equations with the fixed adjunction units.
The equal-universe AffineExtensionSectionsUnit and AffineSectionsBaseChangeUnitSquare
have spectra and a shared localization universe in their signatures; they cannot be
applied here directly. These are interface gaps rather than false statements.

Read Stacks Tags 0AA7, 08HY, 0D5T, 06Z0, 08DV and 08DW online, since the local tex
files are absent. 0AA7's invertibility theorem has qcqs and Tor-independence hypotheses;
only its canonical adjunct construction is used here. The unit identity itself uses
08HY and 0D5T and imposes none of those invertibility hypotheses.

The new statements were checked on Q or E zero, identity maps, empty affine bases
(the zero ring), and nonflat base change. No inverse of base change appears. Both
localization universes remain independent, and only the original hE is used to
construct the source isomorphism. No statement is disputed.

Searches: Lean Finder returned underived adjunction/composition and spectrum
naturality lemmas; Loogle returned general Hom-equivalence lemmas. LeanSearch was
unavailable (Internal Server Error). Mathlib grep found no matching comparison.
Direct project searches located the equal-universe analogues and affine module
representative/model results, but none provides the pinned mixed unit equations.
Blueprint searches for affine extension/sections unit and base-change unit square
returned zero blueprint nodes. The search records are in both new nodes.

## New nodes

`lem-sc-mixed-extension-sections-unit` in
`dag/nodes/sec-picard-framework/lem-sc-mixed-extension-sections-unit.json` formalizes
the source identification from steps 1 and 2 of the original plan, including its
unit compatibility. Its proof dependencies are the existing affine equivalence,
affine K-flat pullback formula, mixed scalar adjunction, and normalized mixed Leray.
Source: [06Z0](https://stacks.math.columbia.edu/tag/06Z0),
[08DW](https://stacks.math.columbia.edu/tag/08DW), and the canonical construction of
[0AA7](https://stacks.math.columbia.edu/tag/0AA7).

`lem-sc-mixed-sections-base-change-unit-square` in
`dag/nodes/sec-picard-framework/lem-sc-mixed-sections-base-change-unit-square.json`
formalizes the unit case of step 3. Its proof uses the canonical base-change
construction, normalized mixed Leray, scalar-square comparison, and derived
composition. The passage from this unit case to all L and m is proved in the
parent, rather than included in this hole.
Source: [08HY](https://stacks.math.columbia.edu/tag/08HY) and
[0D5T](https://stacks.math.columbia.edu/tag/0D5T).

Both inherit chapter sec-picard-framework and unit sk-thm-picard-duality, carry
verbatim Lean signatures and complete proof steps, and introduce no changed notion.
No change record is necessary: existing interfaces are unchanged.

## Second reading by V4

1. **Visible declarations and statements.** I diffed the delivered parent module against the repository version. Existing declaration signatures, including `exists_mixedAffineSectionsBaseChangeMate`, are byte-for-byte unchanged; only proof imports and the proof body changed. The two added declarations are new split-off statements and are recorded by matching DAG nodes.

2. **Proof and axioms.** I compiled all three delivered modules with `lcompile.py --all`; compilation succeeds without warnings. The parent proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The only remaining `sorry`s are the two named split-off theorems, each exactly `:= by sorry`, with source and natural-language proof documentation and a corresponding node.

3. **New statements.** `exists_mixedExtensionSectionsUnit` and `mixedSectionsBaseChange_unit_square` are strictly intermediate: the first concerns only an affine morphism and a quasi-coherent object, while the second concerns only the canonical unit at an arbitrary object. Neither restates the parent target, weakens a target, or duplicates an existing library declaration. Their edge cases and independent universes are addressed in their docstrings; repository searches found no existing equivalent.

4. **Route and pruning.** The parent proof follows the unit route through the two new intermediate statements, then uses the scalar adjunction injectivity and naturality. The three former direct proof imports are no longer used by the parent and were replaced by the two proof-only imports; the retained dependencies are still used by the new statements. No unit-level route is bypassed, and the unit record remains realized.

5. **DAG agreement.** The parent and both new node files agree with the Lean declarations, proof dependencies, proof origins, modules, and split status. The report lists the one target hole closed, the two strictly simpler holes added, and the removed direct proof dependencies.

I changed only this report section during second reading; no Lean statement or proof was altered.
