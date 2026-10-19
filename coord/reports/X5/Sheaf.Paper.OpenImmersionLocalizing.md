## What changed

Completed `AlgebraicGeometry.ProEtale.openImmersionLowerShriek_localizing` in
`Sheaf.Paper.OpenImmersionLocalizing`, without changing its statement. The proof uses
existing source-library exactness, the derived open adjunction and coproduct preservation,
constructibility from `constantModelConstructible_openImmersionLowerShriek`, the proved
open projection comparison, and the defining localizing-closure intersection. For each
cohomology object it converts the supplied `Scheme.Stratification` to the recorded finite
locally closed stratification interface, retaining its constructibility field.
The conversion is proved for an arbitrary predicate on stratum immersions before
specializing to local models; this avoids expensive kernel reduction of module pullbacks.
The retained proof was checked against the current sources on 2026-10-19; its existing
theorem signature is identical, and it compiled without warnings in 21.5 seconds through
`lcompile.py`.
The added lexical scopes and local irreducibility attributes are documented in
`coord/changes/open-immersion-localizing-proof-interface.md`, with the full consumer audit;
they change no exported declaration or target meaning.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.ProEtale.openImmersionLowerShriek_localizing`
(node `det-proper-image-localizing-open`). One original hole closed; zero holes added;
zero split off. The dependency theorem
`AlgebraicGeometry.ProEtale.constantModelConstructible_openImmersionLowerShriek`
(node `lem-sf-open-extension-zero-constant-model-constructible`) remains an existing
`sorry` and is used as a stated dependency.

## No longer needed

Removed proof imports:

- `Sheaf.SixFunctors.IntTensorProjection`: the proved source-library
  `CondensedRing.openImmersionProjectionComparison` supplies precisely the open case;
  node `det-lem-int-tensor-projection` is not needed by this proof.
- `Sheaf.Paper.CartesianCoefficients`: exactness of open pullback and its comparison
  with derived pullback are already in the source library;
  node `sk-prop-sfb-cartesian-coefficients` is not needed by this proof.
- `Sheaf.CategoryTheory.Triangulated.LocalizingFunctor`: the defining closure
  intersection gives the restriction directly, avoiding both declarations of
  node `det-proper-image-localizing-principle`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`: redundant,
  already exported by the retained derived open-immersion module.

Removed obsolete direct tool uses `def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`lem-weil-pbc-ring-sheaves-grothendieck`, `lem-kun-grothendieck-derived-coproducts`, and
`lem-sfb-dc-open-lower-shriek-preserves`: existing module-object exactness and adjunction
instances and `localizingClosure_exists` replace those direct inputs. The latter
constructibility statement uses the weaker finite-presentation notion, so the proof
instead retains `lem-sf-open-extension-zero-constant-model-constructible`.

These are dependencies removed from this item's proof, not claims that no other target
uses their modules. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG listed a general tensor-projection module and a localizing-principle route, but the
available proved open projection comparison and the defining closure intersection make
those attachments unnecessary. The finite stratification conversion is kept locally so the
existing dependency interface remains unchanged.

The interrupted attempt's adaptation of
`Sheaf.Paper.OpenExtensionConstantModelConstructible` was unnecessary according to
the dry-run counterfactual compile. It has been removed; the original dependency's
signature, statement, proof and node are unchanged. No forced adaptations remain.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
