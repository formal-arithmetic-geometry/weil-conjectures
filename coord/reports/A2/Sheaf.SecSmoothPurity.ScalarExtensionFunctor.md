## What changed

Repair of the returned delivery: removed the inherited `warn.sorry` option.
The source hole census matched the option name as an unattributed hole after the
imports moved its source position. Warnings now remain enabled; the complete
proofs and all public signatures and definition bodies are preserved.
After a combined compile/probe timeout, the private cochain-model comparison was
changed from a data-valued definition to a proved `Nonempty` theorem; its sole
consumer obtains the isomorphism in the proof. This keeps the universal-derived
construction abstract during constructibility transport. No public API changed.

Proved the derived counit formulas, exactness, unchanged Tor interval, boundedness,
constructibility, rank-one preservation, and normalized composition and coherence.
Constructed the normalized signed Tate coefficient maps, their ordinary-tensor
isomorphisms, and the signed Kummer level maps. Positive powers are constructed
recursively with the binary tensor comparison; negative powers use the proved dual
comparison and precomposition by the inverse positive comparison. Unit, root,
tensor and evaluation formulas establish uniqueness and the exponent square.
Private normalization lemmas keep the chosen Tate and composition maps abstract
in the exponent and coherence proofs. The identity-extension formula is converted
once to the native interface and reused.
The degree-one tower isomorphism and its section formula are transported together
in a private structure, keeping the sheafification construction abstract.
All public declaration signatures and definition bodies remain unchanged.
Proof-context commands and local smallness instances are documented in
`coord/changes/A2-scalar-extension-functor-proof-context.md`.
Private proved helpers compare the two universal derived models, identify Tor
amplitude with bounded flat representatives, and transfer finite local models back
to the intrinsic constructibility predicate. The tensor/Tor comparison is proved
first in an abstract monoidal Grothendieck abelian category and then specialized,
avoiding repeated unfolding of the sheaf tensor construction.

## Proved and sorry left

Closed all 15 original holes, with zero new holes (namespace `AlgebraicGeometry.ProEtale`):

- `scalarExtensionFunctor_exact`
- `scalarExtensionFunctor_kflat_representation`
- `scalarExtensionFunctor_map`
- `scalarExtensionFunctor_preserves_constructible_tor`
- `scalarExtensionFunctor_line`
- `scalarExtensionTateMaps_existsUnique`
- `scalarExtensionTateIso_existsUnique`
- `scalarExtensionFunctor_tate`
- `scalarExtensionTateLevelIso_existsUnique`
- `scalarExtensionTateIso_exponent_naturality`
- `scalarExtensionFunctor_ringMap_comp`
- `scalarExtensionFunctor_composition_existsUnique`
- `scalarExtensionFunctor_composition_naturality`
- `scalarExtensionFunctor_identity_existsUnique`
- `scalarExtensionFunctor_coherence`

No `sorry` remains in the delivered module. No holes were split off. All private
helpers are proved. No new holes, nodes, or public definitions have been added.

## No longer needed

The Tor proof uses the ordinary bounded flat model theorem in the adopted source
library. It does not use the proposed derived restriction/projection-formula route.
The signed Tate proof constructs powers directly from proved binary tensor
and dual-comparison maps and Kummer maps; it does not import the cyclic signed Tate child.
No module has been withdrawn or deleted.

Direct proof imports removed (some remain transitively available):

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `Sheaf.Paper.CompletedIntegralCoefficients`
- `Sheaf.Paper.InvertibleTensorScalarExtension`
- `Sheaf.Paper.LocallyConstantTensor`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`
- `Sheaf.Paper.StratumScalarExtension`
- `Sheaf.SixFunctors.IntrinsicDerivedTensor`
- `Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses`
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
- `WeilConjectures.ConstructibleSheaf.Refinement`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The proof no longer uses these planned direct proof dependencies:

- `lem-trf-site-derived-tensor-restriction` and
  `lem-weil-pbc-restriction-derived-products`: the native bounded flat model
  proves Tor bounds directly, including boundedness.
- `lem-sp-stratum-scalar-extension`: the existing restricted scalar cohomology
  models supply the intrinsic finite local models on common strata.
- `lem-weil-pbc-site-flat-equational-criterion`: rank-one tensor equivalences
  give exactness and hence the needed single-complex K-flatness.
- `lem-sp-signed-tate-coefficient-exponent-normalization`: its import of this
  module is cyclic; the proved binary scalar tensor and dual
  maps, together with explicit Kummer formulas, prove the specialization here.
- `lem-pur-signed-line-scalar-tensor-tower` and
  `def-pur-signed-line-scalar-normalization-data`: direct recursive coefficient
  powers use the already proved binary comparison and dual evaluation, avoiding
  transport between two separately defined signed-power families.
- `lem-sfb-successive-derived-quotient-normalization`: the published universal
  derived-reduction composition supplies the normalized comparison directly.

`def-weil-proetale-tor-amplitude`, `def-weil-proetale-constructible-sheaf`,
and `def-pur-sheaf-tensor-product` remain statement dependencies; their removal
from the redundant proof-dependency list does not prune these definitions.
No module is withdrawn, and no adopted-source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The proposed `SignedTateCoefficientExponentNormalization` child publicly imports
this item module. Importing it back would create a Lean cycle. Its statement also
packages the Tate conclusions, so using it would merely return the
same assertions under a different name. The proof constructs the powers using
the proved binary scalar tensor comparison and dual evaluation, and proves the
coefficient/exponent specialization here.

The independent-universe derived scalar functor must use localization universe
`u + 2`, matching the standard derived category of these module sheaves. Fixed
coefficient sheafification instances require local control to avoid unconstrained
universe maxima. These are proof elaboration issues; no interface repair is needed.

The derived comparisons are constructed through the already published universal
left-derived scalar functor. No public declaration, definition body, attribute,
public import, unit record, or adopted-source module was changed. No forced
adaptations were needed.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
