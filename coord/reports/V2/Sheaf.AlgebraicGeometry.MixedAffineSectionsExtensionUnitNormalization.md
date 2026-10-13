## What changed

Replaced the proof of
`AlgebraicGeometry.exists_mixedAffineSections_extension_unit_normalization`
without changing its signature. Two proved private natural isomorphisms identify ordinary
sections on the canonical affine chart with the original module functor. Mapping this
isomorphism to complexes transports K-flatness from P to X.

The affine sections comparison is invertible by
`mixedAffineChart_sectionsComplexUnit_isIso`. Extension preserves K-flat quasi-isomorphisms
by `CochainComplex.mixedTensor_kFlat_quasiIso`. The proof constructs the source comparison
from the inverse sections comparison, left-adjoint uniqueness, and the K-flat derived
counit. It proves its unit equation using `derivedη_fac_app`, explicitly accounts for
quotient-to-homotopy factors, and obtains every f-transpose by naturality of exact restriction.
A declaration-local heartbeat budget matches the existing spectrum calculation;
the single-file wall-clock limit is unchanged. The calculation follows the existing spectrum-only `exists_affineExtension_model_unit`
proof, adapted to arbitrary affine charts and independent derived universes.

Sources checked: [Stacks 06Z0](https://stacks.math.columbia.edu/tag/06Z0),
[08DW](https://stacks.math.columbia.edu/tag/08DW), and
[0AA7](https://stacks.math.columbia.edu/tag/0AA7), together with the existing Lean
adjunction and K-flat counit implementations. No boundedness, flat ring map, or affine T
hypothesis is added. The construction uses natural isomorphisms and applies to zero rings,
zero complexes and zero maps.

## Proved and sorry left

Closed the one local hole:
`AlgebraicGeometry.exists_mixedAffineSections_extension_unit_normalization`
(node `lem-sc-mixed-affine-extension-unit-normalization`). No new holes or new nodes.
The proof still uses the existing public theorem
`AlgebraicGeometry.mixedAffineChart_sectionsComplexUnit_isIso`, whose independent module
retains its previously existing hole; this delivery does not prove that dependency.

## No longer needed

None. All original imports and all four planned proof dependencies are used.
No pullback, Leray or ordinary comparison module has been added. The spectrum-only
`Sheaf.AlgebraicGeometry.AffineExtensionModelUnit` served as a proof reference and is
not imported: its same-universe and spectrum-only theorem cannot directly specialize
to this statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The initial published build lacked
`Sheaf.AlgebraicGeometry.MixedAffineSectionsComplexUnit.olean`; compilation became
available after the normal library refresh. No dependency was restated or rebuilt to
work around the publication delay. Local Stacks source files were absent on this machine,
so their primary online tag pages were read instead.

## Second reading by V2

1. **Interface: pass.** Compared the complete delivered module with the repository by
   `diff -u` and checked the existing theorem signature byte for byte. It is unchanged,
   including arbitrary T, affine S, the independent w and wA derived universes, the
   additive instances, K-flatness of P, and the quantification over every Z and f.
   The sole additions before its proof are two private, fully constructed natural
   isomorphisms and a declaration-local heartbeat option. Imports and visibility of
   existing declarations are unchanged; no change record is needed.
2. **Proof: pass.** Compiled the delivered module using lcompile.py: exit 0, no warnings
   (29.9 seconds). Read both private constructions: the first checks scalar transport
   with isoSpec_hom, toSpecΓ_appTop and ΓSpecIso.inv_hom_id_apply; the second uses the
   inverse pushforward equivalence, restrictAdjunction.unit and toTildeΓNatIso.
   Neither chooses arbitrary data from an unproved existence statement. The main proof
   transports K-flatness along their complex isomorphism, constructs a from the inverse
   sections unit, leftAdjointUniq and the K-flat counit, and proves its equation before
   using naturality for f. No local sorry or forbidden construct occurs.
3. **Split statements: pass, none.** There are no added public statements, new nodes,
   or split-off holes. The existing mixedAffineChart_sectionsComplexUnit_isIso remains
   an explicit dependency, not a copied or newly hidden hole. Zero rings, zero P and
   zero f require no cancellation of scalars or nonzero hypothesis: cancellations in
   hstd are of isomorphisms only. There are no new edge cases to exclude.
4. **Route and pruning: pass.** Read AffineExtensionModelUnit and searched lean/Sheaf
   and lean/WeilConjectures for chart section isomorphisms, scalar extension counits,
   PreservesKFlatQuasiIso and the target name. The spectrum-only model does not have
   this chart statement or independent derived universes. The general scalar-extension
   counit module requires a different K-flat interface and does not supply the unit
   equation; the existing direct counit lemma used here is sufficient. All five imports
   are used: the sole public import supplies signature constants; the other four
   supply proof machinery. No old proof dependency is unused. The unit record
   sk-thm-picard-duality has empty realized statement/step arrays; neither it nor the
   chapter route is changed or bypassed by this local normalization calculation.
5. **DAG: pass.** Read lem-sc-mixed-affine-extension-unit-normalization in full. Step 1
   matches the private affine identification, mixedTensor_kFlat_quasiIso and K-flat
   counit; step 2 matches mixedGlobalExtensionAdjunction, the chart sections unit and
   leftAdjointUniq; step 3 matches derivedη_fac_app, hstd, ha and the final naturality
   calculation. All four proof_deps occur in the proof. Its existing proof_origin
   already describes this explicit adjunction/localization calculation. No node edit
   is necessary, and `## No longer needed` is complete.

Second reading changed only this report: no mathematical or Lean repair was needed.
The closed hole is exists_mixedAffineSections_extension_unit_normalization (one of
one); holes added: zero. This is a proof relative to the existing open dependencies,
not a claim that its import closure is free of sorryAx.

A scratch copy with `#print axioms` for the theorem and both private isomorphisms
compiled cleanly (28.4 seconds). Both private isomorphisms use only propext,
Classical.choice and Quot.sound. The theorem uses those three and sorryAx, as
permitted for its existing open dependencies; no other axiom appears.
