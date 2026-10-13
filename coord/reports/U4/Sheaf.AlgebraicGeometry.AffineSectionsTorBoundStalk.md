## What changed

Replaced the whole proof of `AlgebraicGeometry.affineSections_torBound_stalk` by a
compiling reduction to source-algebra localization and localized-base comparison.
Added the proof-only imports `Sheaf.RingTheory.TorVanishingLocalizedAlgebra` and
`Sheaf.RingTheory.TorVanishingLocalizedBase`. Existing signatures, definitions,
visibility, public imports and docstrings are unchanged.

The proof constructs the two affine germ localization instances with Mathlib,
proves the commuting ring-homomorphism square using stalk-map/germ naturality,
applies source localization to the scalar-restricted test module, transports
vanishing through the mapped scalar-restriction composition isomorphism, and
applies the localized-base comparison. Updated the original node's proof route.
The unit has no realized node binding here; its route is unchanged.

All three delivered modules compile together with lcompile.py, without warnings.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affineSections_torBound_stalk`
(node `lem-pc-affine-sections-tor-bound-stalk`). Its proof has no sorry.

Added two holes, each the entire proof of one named public theorem:

- `ModuleCat.isZero_tor_localized_algebra`
  (`lem-pc-tor-vanishing-localized-algebra`), in
  `Sheaf.RingTheory.TorVanishingLocalizedAlgebra`.
- `ModuleCat.isZero_tor_of_restrictScalars_localization`
  (`lem-pc-tor-vanishing-localized-base`), in
  `Sheaf.RingTheory.TorVanishingLocalizedBase`.

This is a decomposition, not a completed proof from sorry-free dependencies:
one upper hole closed and two lower holes added. Each lower statement handles
only one localization operation for a single degree and test module, independently
of schemes, affine opens, stalk maps and a uniform bound. Neither restates the
assigned conclusion. Each docstring contains its source and complete proof in words.

Edge cases checked mathematically: both statements hold for degree zero, the
identity localization and a submonoid containing zero. The base comparison requires
both modules to already be modules over the localization; dropping that condition
would be incorrect. No arbitrary data are chosen from an unproved existence theorem.

## No longer needed

None. No existing import or DAG dependency was removed. The proof retains the
scheme dependency and uses exactly the two new localization modules. The existing
`DerivedTensorLocalizationCohomology` and `TorSymmetry` modules were inspected;
the former has a different derived-category/cochain-model interface, and neither
is needed as a direct import of the assigned module. Their existing nodes are not
claimed to have been pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The node's single non-elementary proof step cited only `def-pc-scheme`, which does
not supply its homological localization argument. The delivery makes that missing
argument explicit as two independently provable algebraic statements. The original
statement appears correct, and no statement or definition was changed.

LeanSearch returned Internal Server Error. LeanFinder and direct searches of the
pinned Mathlib and both library roots found no matching Tor localization theorem.
The three search kinds and the service failure are recorded on the new nodes.

WANTED: `literature/stacks-project/more-algebra.tex`, Tag 0B67,
`lemma-tor-amplitude-localization`, for the two new nodes. The local literature
copy is absent; Tags 0B67 and 069C were read on the Stacks website. Tag 0B67 omits
the forward implication, so the new proofs in words are explicitly agent expansions
of that implication rather than claims to quote a printed proof.

## New nodes

`lem-pc-tor-vanishing-localized-algebra` states preservation of a single Tor
vanishing when the coefficient algebra is localized. Its proof uses Tor symmetry
and exactness of localization to compute with a resolution of the test module.
Its module is `Sheaf.RingTheory.TorVanishingLocalizedAlgebra`.

`lem-pc-tor-vanishing-localized-base` states the localized-base comparison for two
modules already over that localization. Its proof extends a projective resolution,
uses the localization counit and tensor cancellation, and reflects the resulting
zero homology through scalar restriction. Its module is
`Sheaf.RingTheory.TorVanishingLocalizedBase`.

No change record is needed: no existing interface changed and there are no forced
adaptations.

## Second reading by U4

1. Compared the existing module against the repository with `diff -u`: only two
   proof-only imports and the body of `AlgebraicGeometry.affineSections_torBound_stalk`
   differ. Its signature, docstring, visibility and existing public imports are
   byte for byte unchanged. No existing definition or other module is changed.
   Verdict: pass; no change record is required.
2. Independently compiled all three modules with `lcompile.py --all`, cleanly.
   Compiled scratch copies with `#print axioms` for all three declarations:
   each uses only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.
   Exactly the two reported named public helper theorems have `:= by sorry`;
   the stalk theorem has none. No forbidden declaration or hollow definition,
   and no data chosen from an unproved existence theorem. Verdict: pass as a
   decomposition, not a sorry-free proof.
3. Read both new signatures and their full resolution arguments independently.
   Source localization computes using a resolution of the test module and Tor
   symmetry, then exact scalar extension; base localization extends a projective
   resolution and uses the localization counit. Both statements are true and
   strictly smaller than the scheme theorem. Checked j=0, identity localization,
   zero localization, and zero test modules. In the base lemma both arguments
   being localization-modules is essential. Read Stacks Tags 0B67 and 069C online;
   the claimed forward proof is indeed omitted in 0B67, and the docstrings supply
   valid expansions. Independent LeanFinder query on flat ring epimorphisms,
   Loogle query and direct searches for Tor/change-of-rings/localization found no
   direct replacement. Loogle did not recognize `Tor'`; direct inspection of
   Mathlib's Tor module and the library compensated for that limitation.
   Verdict: pass; neither split-off lemma restates the item.
4. Read the reduction from its conclusion downward: affine germ localizations,
   naturality square, source localization, restriction-composition isomorphism,
   and base localization give the exact requested conclusion. Inspected existing
   TorSymmetry and DerivedTensorLocalizationCohomology: the former alone does not
   localize Tor and the latter needs cochain derived-category models and different
   comparison data. Neither helper can be closed with a direct existing lemma in
   a few minutes. All imports supply statement types or necessary instances,
   apart from the two explicitly proof-only helper imports in the original module.
   The sole old proof dependency, `def-pc-scheme`, remains used, so `No longer
   needed: None` is complete. The unit `sk-thm-picard-duality` has empty realized
   statement/step bindings and its route is unchanged. Verdict: pass.
5. Compared the existing node: only `proof`, `proof_deps` and `proof_origin` change.
   Its steps follow the actual Lean proof. Both new nodes have matching verbatim
   Lean signatures, existing dependency ids, proof-dependency unions, sources,
   searches, creation records and inherited chapter/unit/blueprint ancestry.
   Verdict: pass.

Second reading changed only this report by adding the independent review and its
validation evidence; no Lean or node repair was needed. Removed all scratch axiom
copies. One original hole closed, two named lower holes added: net -1 holes closed
before any later pruning by the pinned ledger. No modules are claimed pruned.
