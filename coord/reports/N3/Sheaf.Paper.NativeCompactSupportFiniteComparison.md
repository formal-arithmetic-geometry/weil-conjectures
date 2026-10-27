## What changed

The unchanged theorem
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_compact_support_finite_comparison`
is assembled from four strictly smaller scalar-comparison steps in four new modules, plus a proved
integral-to-rational localization bridge in a fifth new module.
The original `CoefficientFamily`, `FiniteComparison`, and theorem signatures and the
original normalization formula are unchanged. No existing module besides this item
is modified. All four added imports in the item are proof imports.

The assembly obtains the three ordinary realizations from the existing constructible
realization theorem and obtains their common coefficient maps from the new normalized
coefficient-change lemma. For each finite field it constructs an integral natural
isomorphism: the new integral natural morphism has two invertible outer factors,
and the new scalar-mate theorem makes its middle factor invertible. Native sections
reflect isomorphisms. The existing residue-Tor theorem covers every integral
constructible object. The existing `ScalarLocalization.naturalIso_of_integral`
then supplies a rational natural isomorphism with exactly these integral components.
The new scalar-coherence step gives transition compatibility. Explicit equality
transport proves the original normalization certificate for every common-stage
comparison with these components.

The proved theorem `native_compact_support_integral_localization` contains the
integral isomorphism and raw rational-localization argument above. Its abstract
source, target, and coefficient maps avoid expanding the chosen realization records.
The original all-in-one proof typechecked under profiling but took 79 seconds.
The concrete component predicate had already been simplified to avoid expensive
StageAction unfolding; this self-contained bridge is then compiled separately.
No file limit or transparency-respect option is relaxed.

`IntegralComponent` is the existing six-arrow normalization formula with the
component morphism made an explicit argument. Its arbitrary endpoints avoid unfolding
the entire StageAction and realization when transporting equalities. It is a concrete
predicate, with no postponed data or proof in its definition. `finiteSource` and
`finiteTarget` are abbreviations for the two displayed finite-stage functors.

## Proved and sorry left

Remote single-file compilation succeeded for all six modules. The four statement
modules took 6.4, 37.9, 8.1, and 16.6 seconds; the proved localization bridge took
52.8 seconds and the item 48.0 seconds. The bridge's sole long-line warning was
fixed by wrapping the line before delivery. Profiling options are removed.
The delivery tool checks the final sources and records the remaining axioms.

The one original hole in
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_compact_support_finite_comparison`
is replaced by a complete assembly proof. The item contains zero `sorry`.
This is a decomposition, not a net proof reduction: one hole is closed and four
strictly smaller holes are added (net minus three holes closed).

Each added hole has proof exactly `:= by sorry`, a source and full proof in words
in its docstring, and the following DAG attachment. Names below are in namespace
`WeilConjectures.LocallyFiniteAdicCompactSupport`.

- `native_completed_coefficient_change` in
  `Sheaf.Paper.NativeCompletedCoefficientChange`:
  `lem-sf-native-completed-coefficient-change`.
- `native_integral_scalar_morphism` in
  `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism`:
  `lem-sf-native-integral-scalar-morphism`.
- `native_compact_support_scalar_mate_invertible` in
  `Sheaf.Paper.NativeCompactSupportScalarMateInvertible`:
  `lem-sf-native-compact-support-scalar-mate-invertible`.
- `native_compact_support_finite_scalar_coherence` in
  `Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence`:
  `lem-sf-native-compact-support-finite-scalar-coherence`.

The first constructs coefficient maps only, without any compact-support comparison.
The second constructs a possibly noninvertible morphism on integral arrows only.
The third concerns the one ambient scalar mate, without realizations or rational
naturality. The fourth assumes already supplied normalized rational comparisons and
proves just their field-transition equation. None is the original existential
comparison theorem under another name.

## No longer needed

No original import is removed: the original public data import remains. No module
is withdrawn, and no globally unreachable module is claimed as pruned.

The old direct proof dependency
`lem-sf-constructible-exceptional-coefficient-construction` is unnecessary because
P is already a hypothesis; the construction-data and coefficient-coherence nodes
remain used. `lem-weil-pbc-closed-subset-closed-subscheme` is no longer a separate
step: the stated open reduction and constructibility-interval lemmas supply what
is needed without choosing a new closed complement here.

The raw `sk-prop-sfb-qlbar-colimit-x` argument is replaced by the already proved,
normalized `lem-sf-locally-finite-coefficient-ring-realization` in the scalar-mate
step. This does not claim that the raw colimit module is globally unnecessary.
The definitions `def-sf-native-weil-derived-framework` and
`def-weil-derived-complete-integral-detailed` remain transitively needed by the
data and integral constructibility APIs; they are not separate proof steps of
this assembly. All other old analytic proof dependencies are retained in the
four lower steps or used directly. The revised item DAG names exactly the
assembly dependencies; the proved bridge names the existing raw-localization
natural-isomorphism and integral-shift-linearity lemmas.

## Where the brief, the DAG or earlier work was wrong

The current server queue assigns a proof route, and the item has one original
hole. The archived build error about importing
`Sheaf.Paper.LocallyFiniteAdicCompactSupportData` is not a current reproducible
error: the unchanged source compiled against the published artifacts. This
packet does not claim a zero-hole definition repair or an import-collision repair.

The original source docstring mentions a final common-field passage in the
blueprint proof. The current blueprint proof of
`cor-coef-verdier-weil-equivariance` is shorter and does not contain that exact
old phrase. The mathematical source remains Bhatt--Scholze Sections 6.7--6.8,
particularly Proposition 6.8.14 and Remark 6.8.15. The new nodes state their
particular source steps and retain this coefficient/Weil compatibility ancestor.
No unit statement or realized proof step is bypassed.

The original plan's fraction-naturality step can use the already proved raw
scalar-localization theorem directly. This avoids a new lemma for fractions.
All four remaining analytic/normalization obligations are stated explicitly,
rather than hidden inside the assembly or definitions.

Edge cases checked: identity field changes and identity isoToStage are included;
finite extensions may be ramified; no absolute separatedness assumption is added;
the empty scheme and zero input impose only their usual unique/zero maps; the
coefficient prime is invertible by the finite-field datum and its inequality.
The integral scalar morphism asserts no invertibility until the separate mate
lemma is applied, and rational naturality comes from the actual raw localization,
not from objectwise isomorphisms alone.

## New nodes

`lem-sf-native-completed-coefficient-change` realizes the normalized coefficient
inclusion step. Jointly monic finite quotient projections and the pointwise
normalizations identify every presentation with the same function inclusion;
precomposition proves its pullback compatibility.

`lem-sf-native-integral-scalar-morphism` realizes the integral naturality and
six-arrow factorization steps. It groups the existing isomorphisms before and
after the actual proper/open scalar mate into typed outer isomorphisms. The
middle map is not assumed invertible.

`lem-sf-native-compact-support-scalar-mate-invertible` isolates the geometric
coefficient-change argument: open completeness and bounds, proper integral
realization, localization and bounded field push, then counit-normalized mate
pasting. It does not construct the stage comparisons or their coherence.

`lem-sf-native-compact-support-finite-scalar-coherence` isolates compatibility of
already normalized rational stage comparisons. The proof uses the specified
P scalar normalization, common-field realization equations, finite-free
completion comparison, and the pasted-counit identity.

`lem-sf-native-compact-support-integral-localization` is the proved bridge, with no
new hole. Its four steps are the actual Lean argument using the two new integral
scalar lemmas, residue Tor, reflection of isomorphisms by native sections, and
`ScalarLocalization.naturalIso_of_integral`. It asserts one rational finite-stage
comparison only, without field coherence or common-stage descent.

The generic localization theorem and integral shift linearity are proved tools from
other units; the continuous coefficient-realization API is the pointwise coefficient
tool used in the normalized inclusion node. These do not replace any unit route.
No `tool_uses` approvals are added by this worker.

All five new nodes carry the searches actually performed through the search service,
source citations, complete numbered proof plans and verbatim Lean signatures.
There are no change records because no existing signature, definition, instance,
attribute, or public import was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactSupportFiniteComparison": "dbc52e8cf8052c2336f6f0d6ec5f30d7ac5c065a", "Sheaf.Paper.NativeCompactSupportFiniteScalarCoherence": "71a0e97162a85a9872866aa9640c0a52dd3759ff", "Sheaf.Paper.NativeCompactSupportIntegralLocalization": "a40431ed8ef152b8f3fc7ba4e819a776c2b222a4", "Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism": "34864e553b7dc493207a886cd35bbde5cbbb0f16", "Sheaf.Paper.NativeCompactSupportScalarMateInvertible": "bddffac59956ee555bbb2feb2e9445eaee0ee698", "Sheaf.Paper.NativeCompletedCoefficientChange": "2129338bde49d0787f06a379f22278234d935945"}, "results": {"Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization": {"hash": "b1222b33661731a5f010777a9242825042cdc6f7", "status": "OK"}}, "seconds": 103, "time": "2026-10-28T01:04:35+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
