## What changed

Replaced the whole proof hole in
`WeilConjectures.IntegralSystemRealization.integralCanonicalSystemCoherence`
by an assembly from three strictly smaller obligations. Its signature, universes,
existing docstring, and public imports are unchanged. Added three imports used only by the proof, three statement modules, and their DAG nodes. No existing dependency,
consumer, definition, exported instance or attribute, or target is edited.

The square argument is real Lean in the assigned module. Cancel the invertible
compositor for the path r,i at the tensor object. Expand the specified square
isomorphism. Apply tensor/composition compatibility on both two-arrow paths.
Equality induction proves compatibility with the equality transport between the
composite scheme morphisms. Functoriality of the tensor bifunctor and cancellation
of the inverse compositor on its two factors give the required square equation.
The algebra is checked with abstract objects and morphisms in one category
before it is instantiated with the large system models. The private `square_eq`
identifies the natural isomorphism first; `square_hom_app` obtains its component
formula by congruence and the generic `trans_hom_app` lemma. This avoids the
kernel timeout caused by directly reducing a square component across the full
coefficient constructions. Local irreducibility attributes prevent elaboration
from expanding their constructions; these attributes do not escape this module.
Thus no square equation is assumed as a new hole, and no equality is detected
by finite evaluation.

The new obligations separate the ordinary/derived construction, transport of
intrinsic proper/open coherence, and tensor compatibility for just two composable
morphisms. The construction obligation supplies neither proper/open coherence nor
tensor compatibility. The transport obligation takes already constructed models
and has no tensor conclusion. The tensor obligation contains no square, direct
image, open operation, or proper/open map. None is the assigned theorem under
another name.

Read the current blueprint's `fix-prop-coherence.proof.md`, its unit record,
Zheng Construction 4.1 and Lemma 4.10 (printed pp. 21 and 23), and the Stacks source
for 03D8, 03DI, 07A4 and 0F7B. The additional pure-tensor composition calculation
is recorded as agent-written below the unchanged unit route.

Validation: all three new statement modules compiled through `lcompile.py --all`.
The final assigned module compiled cleanly without profiling in 3.3 seconds through
`lcompile.py`; the profiled proof had 269 ms of kernel type checking.

## Proved and sorry left

This is a decomposition, not a net hole closure.

Closed the original whole proof hole in
`WeilConjectures.IntegralSystemRealization.integralCanonicalSystemCoherence`
(node `lem-sf-integral-canonical-system-coherence`), conditional on the following
three named public statements. The assigned module has zero remaining holes.

Added holes, each the whole proof of its named public theorem:

- `WeilConjectures.IntegralSystemRealization.integralSystemOperationModels`,
  node `lem-sf-integral-system-operation-models`.
- `WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransport`,
  node `lem-sf-integral-system-proper-open-transport`.
- `WeilConjectures.IntegralSystemRealization.integralSystemTensorComposition`,
  node `lem-sf-integral-system-tensor-composition`.

The private helper `tensorComparison_congr` is proved by equality induction.
The private helper `tensorComparison_square` proves the square algebra for
morphisms and an arbitrary tensor bifunctor. `systemTensorCongr` and
`systemTensorSquare` instantiate the generic lemmas with the system comparisons.
Textual accounting: one old hole replaced, three new holes, net minus two.
Every new hole has a source and a complete proof in words in its own module and
node. No data is chosen in a new definition, and no axioms are introduced.

## No longer needed

None. No existing import, node, module, or declaration is withdrawn. The original
proof dependencies are reorganized under the three new obligations and remain
required transitively. In particular the semilinear derived-section and
proper/open mate-pasting results are retained; their remaining holes are not
obstacles to using them in this stage. New statement modules import only what
their signatures need.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The existing proof plan compresses the
normalization and presentation-identification arguments: the cited generic
derived-section and coefficient-comparison theorems do not themselves return the
specific `Operations`, `Compositors`, `CanonicalBridge`, and `ProperOpenCoherence`
records. These exact construction and transport steps are now explicit obligations.
The tensor square reduces to the simpler composition law by categorical algebra;
it does not require a fresh four-arrow K-flat argument or faithful evaluation.

Searches found ordinary pullback composition, generic mate-pasting and derived
adjunction APIs, not an exact theorem for the fixed models. Also inspected
`RingedDerivedMonoidalComparisons`, `RingedDerivedCompositionComparison`, and
`RingedSquareTensorCompatibility`: they require ringed presentations and
representative identifications which the strict-system normalization still has
to supply. `PublishedSystemTensorComposition` and its ambient coherence theorem
quantify over finite-type schemes over a fixed algebraic closure, whereas this item
quantifies over all schemes; their extra geometric hypotheses cannot be introduced
here. Blueprint searches for the three proposed substeps found no duplicate.

Edge cases checked when stating the obligations: identity maps have the specified
canonical compositor rather than an arbitrary scalar automorphism; zero tensor
inputs and the empty scheme do not require nonempty assumptions. The empty open
has the same extension/restriction adjunction formulas. No coefficient quotient is
assumed flat, no boundedness or properness is added to tensor composition, and
no invertibility of proper exchange is claimed.

## New nodes

`lem-sf-integral-system-operation-models` realizes original construction steps
1 and 2 only. It retains all evaluation and section normalizations in the existing
records and omits both proper/open coherence and the tensor equation.

`lem-sf-integral-system-proper-open-transport` realizes original step 3, for any
already supplied section-normalized models. Its proof records how the bridge
identifies compositors, beta, the clopen map and lambda before transporting the
three intrinsic equations.

`lem-sf-integral-system-tensor-composition` realizes the two-arrow core of original
step 4. Its source is the pure-tensor calculation on flat-term K-flat complexes,
localized with the fixed representative equations. The assigned module proves the
passage from this law to the arbitrary commutative-square equation.

The assigned node's proof, proof dependencies and proof origin are updated to
match the Lean argument. No change record is needed: no existing interface changes.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
