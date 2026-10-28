## What changed

Replaced the assigned representative-associativity hole by the ordinary pure-triple
calculation, signed total-chain associativity, and a generic pasting argument for
four representative squares. Total tensors and ordinary pullback preserve the
flat K-flat representatives needed in these four squares. A new proved ordinary
pullback-associativity helper records the generator calculation separately.

Retained the finite monoidal coherence witness in
`CoefficientDerivedSystemFibers`. The existing resolution-model construction
already proves this witness; it now retains the finite component instead of
discarding it. The change record explains this interface correction and the
necessary semantic review of definitions used by targets. The original checked direct
importers and named users compiled unchanged; the newly landed canonical fiber
constructor requires the forced adaptation recorded below. No source-library module is edited.

## Proved and sorry left

Closed: `WeilConjectures.finitePullbackTensor_associativity_representatives`
(the assigned module originally had one hole).

Added holes: none. Remaining holes in delivered modules: none.
The adapted `CanonicalIntegralEvaluationCalculus` also has zero holes.
The new `WeilConjectures.proEtaleOrdinaryTensorPullback_associativity`,
`CategoryTheory.RingedForgetTensorTransposition.ringed_tensorComparison_associativity`,
`WeilConjectures.proEtaleOrdinaryTensorPullbackNaturalComparison`,
`WeilConjectures.proEtaleTotalTensorPullbackComparisonNormalization`,
`WeilConjectures.proEtaleCoherentTotalTensorPullbackComparison`, and
`WeilConjectures.ringedDerivedTensorComparison_associativity` are proved.
The categorical transport, the two model-naturality lemmas, and the normalized
associator-representative lemma in `RingedTensorRepresentativeTransport` are also proved.
The two repaired coefficient modules originally and currently have zero holes.
Imported named theorem dependencies may retain their own pre-existing holes;
this delivery proves the assigned statement from those declarations.

## No longer needed

None of the original node's declared mathematical dependencies is withdrawn.
The proof still uses the binary representative normalization, K-flat total
models, and ordinary tensor pullback construction. No module or node is pruned.
The direct chain-calculation imports are represented by the new proved coherent
total-comparison helper. Ordinary pullback associativity, ringed chain
associativity, native associator detection and the total-summand generator APIs
remain dependencies of that helper; none is withdrawn. The original public
import remains. No original import, module, or node is withdrawn.
The proof does not import `RingedForgetTensorTranspositionData` or
`RingedForgetTensorAssociatorModelSquare`: their internal-Hom dependencies
return through the adic Tate-twist tensor comparison to the assigned module.
The canonical total-summand inclusion is constructed directly, and the elementary
inverse-associativity cancellation is proved privately. Those existing modules
remain in the library for their other consumers.

## Where the brief, the DAG or earlier work was wrong

The plan implicitly needs associator normalization for the chosen finite
closed/tensor structures. The fiber record retained binary tensor and
internal-Hom normalization but discarded the monoidal coherence already proved
while constructing those structures. Binary closed adjunction alone does not
identify the associator. The added proof field retains the existing finite
coherence; the resolution-model constructor supplies it directly from `hTR`.
The existing ringed associator-square interface also bundles internal-Hom
comparison data. The new chain lemma states the tensor calculation using only
ordinary tensor associativity, naturality, and summand normalization.

This is recorded as a definition correction, with affected users and DAG
statement checks in `coord/changes/G2-finite-tensor-coherence.md` and the two
coefficient node updates. The assigned theorem's signature is unchanged.
The initial proof-only transposition import
created a cycle through adic Tate-twist comparisons; the tensor calculation now
uses only its canonical summand and elementary cancellation ingredients.

## New nodes

`lem-pur-ordinary-pullback-tensor-associativity`: proved ordinary module-sheaf
pullback tensor associativity. Its proof takes adjuncts, evaluates on local
pure triples, and uses the two binary unit-generator formulas. It has no
flatness hypotheses and no derived-localization assertion, and adds no hole.
The generator proof allows zero modules and zero sections and arbitrary coefficient
ring sheaves (including the zero ring); empty schemes make the same local statement.
No step restricts the finite level, so the assigned case n = 0 is included.
The definition correction is recorded in
`coord/changes/G2-finite-tensor-coherence.md`.

`lem-pur-ringed-tensor-comparison-associativity`: proved chain-level coherence
from an ordinary natural comparison, its inverse associativity equation, and
the summand formula for a natural total comparison. Pure-triple detection and
the existing abstract model-chain theorem give its complete proof. The coherence
proposition is a structure with one proof field, so later existential proofs do
not repeatedly expand the model formula. It requires
neither derived localization nor internal-Hom preservation, and adds no hole.
The abstract normalization keeps concrete sheaf colimit constructions out of
the finite representative calculation.

`lem-pur-coherent-total-tensor-pullback-comparison`: retains the existing natural
total comparison together with its specified components and its associativity on
pure-triple models. This proved interface keeps the large concrete totalization
construction out of the derived representative pasting proof. Its hypotheses are
ordinary ringed pullback data, without K-flatness or derived categories; it adds no hole.

`lem-pur-natural-ordinary-tensor-pullback-comparison`: packages the prescribed
ordinary component comparisons as a natural isomorphism, retaining their forward
associativity. Mathlib's `NatIso.ofComponents`, the existing naturality equation,
and the proved ordinary associativity give the complete proof. This interface
keeps the concrete natural-isomorphism construction out of the total comparison
proof, and adds no hole.

`lem-pur-total-tensor-pullback-comparison-normalization`: retains the existing
natural total comparison together with its pointwise and summand normalizations.
Rewriting those components gives the existing geometric summand identity. The
proved lemma separates normalization from coherence so both files stay within
the per-file compile limit; it adds no hole.

`lem-pur-ringed-derived-tensor-comparison-associativity`: proved generic derived
model transport from four binary representative squares and chain coherence.
It chooses the existing model associators, uses model naturality, and cancels
the nested model isomorphisms by a fully proved categorical pasting argument.
The finite theorem now supplies its preserved K-flat models to this abstract
argument. This avoids repeated unfolding of the chosen finite structures and
adds no proof hole.

`lem-pur-ringed-tensor-representative-transport`: proved categorical pasting,
left and right naturality of simultaneous tensor models, and normalized model
associator representatives. This reusable interface separates the categorical
transport and normalization proofs from their generic derived application.
All four public theorems are proved; no hole is added.

## Forced adaptations

Reviewer C-89dfb point 2b reported that the newly landed Y3 module
`Sheaf.Paper.CanonicalIntegralEvaluationCalculus` failed at line 88:41 with
`Fields missing: finite_tensor_coherence` in private definition
`CanonicalCoefficient.fibers`, while the original compiled against published data.
The refreshed current source is adapted by adding that proof field. A private
proved uniqueness lemma identifies the transported finite tensor model with the
fixed normalized duality model: represent the transpose of one inverse comparison
by a Hom chain map, apply both uncurrying equations, identify their chain maps on
pure tensors, and cancel the invertible comparison. Existing constraint completion
then supplies the required coherence witness. The helper and its proof-only
imports are necessary to prove the added field; no existing public signature,
visibility, attribute, or public import changes.

The change record now lists this module and the unchanged
`Sheaf.Paper.CanonicalCoefficientRepresentativeLaws` and
`Sheaf.Paper.CanonicalCoefficientCompositionLaws`. Their requested compile checks
passed: representative laws 43.0 s, composition laws 3.6 s, and the adapted
canonical calculus 27.6 s. Canonical reduction also compiled unchanged in 0.1 s,
and the assigned theorem compiled again in 24.8 s. Only the adapted canonical calculus source and its necessary proof
node update are added to the delivery; unchanged compatibility-check copies are
removed after compilation. All 14 current direct importers of the repaired
coefficient modules also compiled successfully against the delivery; their
unchanged temporary copies have been removed. No hole is added by this repair.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 16, "left_out": 0, "own": {"Sheaf.Algebra.Homology.RingedDerivedTensorComparisonAssociativity": "afdba75a019de1729931a94fbf00cf604f09361b", "Sheaf.Algebra.Homology.RingedTensorComparisonAssociativity": "f347bbb2723904fd7f29c9abf66ab6b1474a75ea", "Sheaf.Algebra.Homology.RingedTensorRepresentativeTransport": "79d4fff15cf3228af65c986291caa66ea9614634", "Sheaf.Paper.CanonicalIntegralEvaluationCalculus": "5b8c735e0c563e332219a22011d49b94c43acf33", "Sheaf.Paper.CoefficientDerivedSystemEvaluationData": "5536682da6f9cab3e032930eb70b2893d943e9c7", "Sheaf.Paper.CoefficientDerivedSystemResolutionModels": "4eb2236c139158b01f9348c82355176ca893a62d", "Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives": "b551e7ec1ef060fab24e07209d1981ee00eaa1b3", "Sheaf.Paper.ProEtaleCoherentTotalTensorPullbackComparison": "0846185af4908bbf35e33e1b71ae9a0dafa67152", "Sheaf.Paper.ProEtaleOrdinaryTensorPullbackAssociativity": "05042cafa114cdfdb60bb625adfb74fc4580c79b", "Sheaf.Paper.ProEtaleOrdinaryTensorPullbackNaturalComparison": "cd584a676568f4de77c5947ac52617a8d890b382", "Sheaf.Paper.ProEtaleTotalTensorPullbackComparisonNormalization": "2b5d4b69dcdf15aa081f6d4291db5f0692bb47e9"}, "own_failed": ["Sheaf.Paper.CanonicalIntegralEvaluationCalculus", "Sheaf.Paper.CoefficientDerivedSystemEvaluationData", "Sheaf.Paper.ProEtaleOrdinaryTensorPullbackAssociativity", "Sheaf.Algebra.Homology.RingedDerivedTensorComparisonAssociativity", "Sheaf.Paper.CoefficientDerivedSystemResolutionModels", "Sheaf.Paper.ProEtaleOrdinaryTensorPullbackNaturalComparison", "Sheaf.Paper.ProEtaleTotalTensorPullbackComparisonNormalization", "Sheaf.Paper.ProEtaleCoherentTotalTensorPullbackComparison", "Sheaf.Paper.FinitePullbackTensorAssociativityRepresentatives"], "results": {}, "time": "2026-10-28T09:30:11+0800", "transitive": 5, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
