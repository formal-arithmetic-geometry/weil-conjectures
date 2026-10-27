# etaleFiniteTwistPullback_base private proof imports

## Reason

The new imports needed by the assigned affine-line proof expose a source import cycle:
SfAffineLineCanonicalDuality -> EtaleFiniteTwistPullback ->
EtaleFiniteTwistPullbackBase -> WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction
-> RegularImmersionIso -> RegularImmersion -> Basic -> CohomologicalSmoothness ->
WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality -> SfAffineLineCanonicalDuality.
The same path is reached through the projective trace dependency.

The offending proof import is unnecessarily broad. The existing complete proof of
etaleFiniteTwistPullback_base constructs its comparison from normalized root-line pullback,
the finite Tate tensor family, and underived pullback coherence. It uses no purity,
exceptional pullback, supported fundamental class, or coefficient-reduction declaration.
The composition-unit lemma Etale.upperStarComp_id_left is already provided by the public
UpperLowerStar.Coherence import. Removing the broad import alone exposed two missing
names: isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit and
Etale.upperStarConstantSheafIso_hom_app_tensorUnit. Import their actual defining modules,
RootsOfUnityPullback and ProjectionFormula.Unit, directly. Replace the broad import with every
existing declaration, proof, attribute, option and public import preserved verbatim.
The module and its node were unclaimed when this repair was made.

## Old

```lean
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction
```

## New

```lean
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
```

The complete theorem proof is unchanged.
The adopted source module and all of its declarations remain intact in the library.

## Users

`tools/downstream.py --uses etaleFiniteTwistPullback_base` reported 790 transitive downstream
modules and two textual users (the defining module and EtaleFiniteTwistPullback). All public
imports and declarations are identical, so all consumers see exactly the same API. Direct
importers are listed below; none requires adaptation. The attached affine-line proof is the
only new consumer. The overlaid complete source import graph has zero strongly connected
components with cycles after this repair.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullbackBase | unclaimed | Replace one overly broad private import by the two actual lemma providers; theorem proof and signature unchanged; zero holes before and after. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | No public interface, definition or proof changed; private imports are invisible to importers. |

## Status

landed 20261024T015854-L-2461580 2026-10-24 (merge of deliver/R1/Sheaf.AlgebraicGeometry.SfAffineLineCanonicalDuality)
