# AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit

## Reason

The compactification proof of adic finiteness needs exact closed direct image and its
counit. The existing generic closed-immersion counit was still a hole. Its module,
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion`, was unclaimed
in the supplied repository (`coord/claims/` has no corresponding claim). The forced
adaptation exception is therefore unnecessary: the launcher's unclaimed-module rule
allows proving it in this delivery. No existing signature, definition, visibility or
public import changes.

## Old

`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit` was `sorry`.
The DAG planned to compute inverse image by a separate presheaf formula and then glue.

## New

Prove full faithfulness first on quotient-spectrum immersions, using the existing
closed-site adjunction, opposites and precomposition. Transport it along affine scheme
isomorphisms. Use weakly etale base change, the iterated mate identity and open-cover
conservativity to obtain the counit isomorphism for any closed immersion. All helper
lemmas are private and proved. The closed-site input still depends on the existing
`affine_closed_site_functor_properties` theorem; its module is not changed.

The proof imports only `ClosedSiteAdjunction`, `BaseChange.WeaklyEtale`, and
`OpenImmersion.Conservative` privately. The original public imports and every existing
signature remain identical. The abstract private lemma for the double-mate calculation
keeps the scheme adjunctions opaque to that calculation: profiling reduced the module's
compilation from about 53 seconds to about four seconds without changing any definition
or compilation limit. The node's proof and proof dependencies follow this route.

## Users

No caller requires adaptation: existing declarations and public imports are identical.
The new `Sheaf.AlgebraicGeometry.AdicClosedImmersionFiniteness` uses the counit and the
existing exactness theorem from this module. The item module
`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` uses that new closed helper and the
two separately stated geometric finiteness inputs. No held module is adapted, and
`Challenge.lean` is unchanged.

## Status

landed 20261015T195758-L-1299658 2026-10-15 (merge of deliver/C3/WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar)
not delivered or pushed by this worker.
