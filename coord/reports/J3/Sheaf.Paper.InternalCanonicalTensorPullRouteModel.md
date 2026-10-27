## What changed

Proved `AlgebraicGeometry.ProEtale.QuotientChange.canonical_tensor_pull_route_model`
in `Sheaf.Paper.InternalCanonicalTensorPullRouteModel`, keeping its statement and
both public imports unchanged. The proof specializes `Functor.tensorModelRoute_fac`
to the native ordinary module pullback and the fixed canonical scalar presentation.
It identifies the geometric derived tensor comparison with the canonical derived
oplax tensorator, supplies the existing counit equation, and cancels the coefficient
pullback isomorphism against its inverse inside the model target.

Added the fully proved helper module `Sheaf.Paper.NativeModulePullbackBraiding`.
It extracts the small ordinary coequalizer calculations already proved privately in
`Sheaf.Paper.TraceBaseChangeFirst` and applies them directly to the native pullback
monoidal structure. Its only public declaration is
`AlgebraicGeometry.ProEtale.CondensedRing.nativeUpperStar_braiding`.
The item privately imports this helper and
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`.
No existing definition or statement changes, no consumer adaptations, and no
source-library edits are required. Updated the item's proof docstring and DAG proof
metadata to match this route. Local irreducibility of the constructed coefficient
isomorphism and a restricted `simp only` avoid unfolding its large construction.
The final item compiles cleanly in 45.3 seconds; the helper compiled cleanly in
10.0 seconds through `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.QuotientChange.canonical_tensor_pull_route_model`
(node `lem-sfb-internal-canonical-tensor-pull-route-model`).

Added 0 holes and split off 0 unproved statements. The new native braiding theorem
and its three private helpers are proved. Both delivered Lean files contain zero
`sorry` tokens. This is a proof from the existing derived tensor-model API, not a
decomposition into new proof obligations.

## No longer needed

No original import was removed; the two original public imports remain unchanged.
The proof does not need `new-integral-residue-ordinary-tensor-normalization`
(`Sheaf.Paper.IntegralResidueOrdinaryTensorNormalization`): it uses the native
ordinary monoidal structure throughout and proves its braiding equation directly.
This dependency is removed from the item's `proof_deps` and proof steps.
The statement dependency `def-sfb-module-object-projection-map` is retained,
although it is no longer separately listed as a proof dependency: its needed
geometric comparison is handled by the more precise existing identification with
`leftDerivedTensorComparison`.

No module is withdrawn or deleted. No claim is made that these dependencies are
unused by other parts of the library. In particular, no source declaration is
removed and no unit realization is bypassed. The proof does not import
`Sheaf.Paper.TraceBaseChangeFirst`; the standalone helper avoids bringing its
unrelated trace and base-change theory into the item's proof imports.

## Where the brief, the DAG or earlier work was wrong

The planned identification between native and separately transported ordinary
monoidal structures is unnecessary. Monoidal structures on a fixed functor cannot
be identified merely by proof irrelevance. Instead the native structure satisfies
the required braided square by the explicit balanced coequalizer calculation.
The existing generic route theorem then applies with that same structure.
The unchanged target statement needs no flatness assumption, and none is added.
The calculation cancels only isomorphisms and coequalizer epimorphisms; it applies
also to zero modules, the zero coefficient ring, and empty schemes.

## New nodes

`lem-sfb-native-module-pullback-braiding`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-native-module-pullback-braiding.json`,
records the fully proved native ordinary braided square. The mapMod square follows
from its tensor-projection equation and ambient braidedness; comap along an
isomorphism is braided by the same projection calculation; its specified monoidal
transport makes extension braided. Composing these structures and cancelling the
invertible tensorator yields the required oplax equation. This is a strictly
ordinary module-tensor step of the existing route, with no new proof hole.
No change record is needed because no existing statement or definition changes.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
