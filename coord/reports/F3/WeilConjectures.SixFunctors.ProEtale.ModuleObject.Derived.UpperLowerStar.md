## What changed

In `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`, replaced the
proof of `AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatQuasiIso_upperStar` by the
existing exact-functor instance. Rebuilt `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIso`
from `Functor.leftDerivedFunctorCompIso` and
`Functor.leftDerivedFunctorIsoMapDerivedCategory`. Extension of scalars is left exact here
because the coefficient map is an isomorphism; transport exactness through
`Mod.extendScalarsIsoComapInv`.

Removed the now-unused K-flat preservation instance and updated the explanatory docstrings.
Retained every other existing declaration, signature, visibility, and import, including the
proved generic K-flat APIs. Updated the construction-verification proof and origin of
`def-weil-pbc-condensed-e-module-category` to record the exactness route. The unit route is
unchanged. Change record: `coord/changes/condensed-pullback-exact-pruning.md`.

## Proved and sorry left

There was one direct hole:
`AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar`.
It is removed by pruning, not proved and not split. Thus 0 of the original 1 statements are
proved; 1 unnecessary obligation is retired; 0 holes remain in the assigned module and
0 holes are added. The two replacement proofs above compile from existing library APIs.
Inherited sorries in other modules are unchanged; this delivery does not claim to close them.

Validation: the assigned module compiles through `lcompile.py`, with no warnings. All three
unchanged direct importers also compile against the sandbox overlay:
`Sheaf.Paper.CondensedQcqsPushforwardContinuity`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`.
The declaration comparison reports no changed statements and no added declarations.
Axiom inspection of both replacement proofs reports the standard axioms and inherited
`sorryAx`; there is no direct hole in this file. The required `deliver3.py --no-push` dry run
is the final check; nothing is pushed by this worker.

## No longer needed

The declaration `AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar`
is no longer needed by either former caller and has no external callers. The generic
`Functor.preservesKFlatQuasiIso_comp` and
`Functor.leftDerivedFunctorCompMapDerivedCategoryIso` are no longer used by the condensed
pullback proofs; their definitions remain available for other uses. No imports are removed.
No DAG node or whole module becomes unnecessary: the attached category-definition node also
realizes the coefficient category, pullback, pushforward, and exchange constructions.

## Where the brief, the DAG or earlier work was wrong

The attached node is a broad definition node whose `lean` attachment is now
`Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`; this item's module appears in its
source audit, not its primary attachment, and its proof was empty. It supplied no numbered
plan for the lone K-flat hole. The module's old docstrings treated preservation of arbitrary
K-flat complexes as necessary input, overlooking the existing exactness of the pullback and
of extension along its invertible coefficient map. The stronger assertion is not disputed:
it is unnecessary for the constructions used here. No source statement is weakened.

## Second reading by F3

1. **No accidental interface changes.** Compared the delivered module with the repository version. The
   existing declaration signatures and visibility are unchanged byte for byte; only explanatory
   documentation, the retired K-flat instance, and the two replacement proof bodies changed. The
   attached DAG record changes only its proof route and origin as reported.
   **Verdict: pass.**

2. **Proof validity.** Compiled the delivered module with `lcompile.py`; it succeeds with no warnings.
   The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
   The replacement uses exactness of both factors and the standard derived-functor comparison;
   `preservesKFlatQuasiIso_upperStar` is supplied by the exact pullback instance. **Verdict: pass.**

3. **Statements and pruning.** No new theorem statement was split off. The retired
   `preservesKFlatComplexes_mapMod_upperStar` obligation was not needed by any remaining caller,
   and no existing statement was weakened or strengthened. The exactness argument is strictly
   sufficient for the derived pullback computation. **Verdict: pass.**

4. **Top-down route and imports.** The proof follows the existing exact-functor derived-category
   APIs and the coefficient-isomorphism transport. The unit route and all imports remain intact;
   no unused public import was introduced or removed. **Verdict: pass.**

5. **DAG agreement.** The node's proof and `proof_origin` describe the exactness route used in the
   Lean body, with no proof dependencies. The unit's realized route is unchanged. **Verdict: pass.**

Changed: removed the unused K-flat-complex preservation instance and updated the two derived
pullback proofs and their documentation; updated the attached node's proof metadata accordingly.
