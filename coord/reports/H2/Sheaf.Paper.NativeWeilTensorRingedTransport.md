## What changed

The existing theorem `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_transport`
keeps its exact signature and all three original public imports. Its proof imports
`Sheaf.Paper.NativeWeilTensorRingedDerivedSquare`, constructs the representative data explicitly,
and fills the seven presentation axioms individually. No other existing Lean module is changed.
All seven delivered modules compile together with `lcompile.py --all` (exit code 0).
The single unused-simp-argument warning in that run was removed before delivery.

Six new modules separate and implement actual steps of the original three-step argument:

- `NativeWeilTensorForgetKFlat` proves preservation of the full acyclic-test K-flat condition.
  Its proof constructs the zero-orbit inclusion and projection as chain maps, tensors the
  resulting retract, and applies homology. The exact orbit-induction functor is the existing
  explicit integer coproduct; no object is selected from an unproved existence theorem.
- `NativeWeilTensorRingedComplexes` states the normalized underived comparison, signed total
  comparison, preservation of K-flatness under the ringed equivalence, and K-flat localization.
  It does not mention a derived tensor structure or a tensor-forgetting comparison.
- `NativeWeilTensorRingedComplexModel` constructs the middle comparison from the supplied
  ringed one-K-flat representative to the localization of the native total, and proves its
  naturality from the ringed-model square and the localized chain square.
- `NativeWeilTensorRingedModel` constructs the native one-K-flat model as a fully faithful
  preimage of an explicit composite: equivalence counit, exact-functor factors, the middle
  comparison above, and inverse total factor.
- `NativeWeilTensorRingedModelNaturality` proves naturality of the fully faithful pullback.
  Generic mapped-square, product-square and four-square lemmas keep these equalities abstract.
  `Functor.mapDerivedCategory` is locally irreducible in these new modules only; this exports
  no reducibility attribute and changes no shared definition. Separating the middle comparison
  from the final pullback bounds the elaboration work in each file.
- `NativeWeilTensorRingedDerivedSquare` isolates the remaining comparison of the two derived
  tensors, the ordinary normalized model, and coherence. Its native model is the explicit
  construction above, not an existentially chosen tensor model.

The native tensor convention has its right parameter first. Consequently the comparison with
ringed totals reverses the two cochain directions and includes `(-1)^(p*q)` on a summand. This
sign and the underived inverse-adjunction formula are part of the new complex-comparison record.
They fix its data by evaluation and the total-summand universal property; the other fields are
proofs. The Koszul scalar uses an explicit ringed Hom group to avoid expensive instance search.
The new record disables automatic constructor-injectivity and size-spec generation, following
the existing bridge record; no shared definition or reduction behavior is changed.
The ordinary model in the derived-square conclusion is also required to be natural in both
inputs. Its normalization on two K-flat inputs and this naturality determine its value on an
arbitrary second input using a K-flat resolution. Thus its data are not an arbitrary choice
from a mere existence assertion. The two remaining theorem statements contain complete proof
descriptions and sources.
The parent DAG proof follows the explicit assembly and reaches all six new nodes.

## Proved and sorry left

This delivery is a decomposition, not a sorry-free proof of the original obligation.

One original hole is closed syntactically:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_transport`.
There is no `sorry` left in the item module. The complete combining proof constructs
`NativeWeilTensorComplexData` and all seven `NativeWeilTensorPresentationAxioms` fields.

New complete proofs (no added holes):
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_forget_kflat`,
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedTensorComplexModel_naturality`, and
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedTensorModel_naturality`.
The model definition itself is a composite of supplied isomorphisms, with no `sorry` data.

Two holes are added, each the whole proof of a named public theorem in its own module:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_complexes`, node
  `lem-sf-native-weil-tensor-ringed-complexes`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square`, node
  `lem-sf-native-weil-tensor-ringed-derived-square`.

The first covers the underived/complex/localization part of original steps 1--2, independently
of derived monoidal choices. The second assumes that complex part and the explicit native
model, and covers the residual derived square of step 3. Neither restates the original
presentation-existence theorem. Total delivered textual holes: two; original holes: one;
net holes closed minus added: minus one. No claim of an axiom-free target proof is made.

## No longer needed

No original public import is removed. No existing module is withdrawn, and no adopted source
library declaration is removed or changed. The following original planned proof dependencies
are not invoked by this proof:

- `lem-sf-native-weil-underived-tensor` / `Sheaf.Paper.NativeWeilUnderivedTensor`: the native
  bifunctor, adjunction, comparison and normalization are already theorem inputs.
- `lem-sf-native-weil-tensor-chain` / `Sheaf.Paper.NativeWeilTensorChain`: the chain comparison
  and its summand formula are already theorem inputs. The node stays a statement dependency.
- `lem-sf-weil-frobenius-action-resolutions` /
  `Sheaf.Paper.WeilFrobeniusActionResolutions`: the exact orbit-retract proof needs no action-site
  existence or geometric finite-type hypotheses. The bridge itself is already an input.
- The existence conclusion of `lem-sf-ringed-derived-closed-symmetric-monoidal`: both ringed
  closed structures, representative comparisons and coherence are supplied. The modules
  defining their types remain available through the original imports.
- The existence conclusion of `lem-sf-ringed-forget-tensor-descent`: `d` is supplied, so the
  remaining square transports its fields rather than invoking another existence result. Its
  module and node remain needed for the `TensorComparison` interface and the lower square.

These are removals from this proof's planned route, not claims that their modules have no
other consumers. The unit record `sk-prop-sf-biduality-general` is unchanged; its `realized`
statement and step lists are empty. No unit route or target statement has been altered.

## Where the brief, the DAG or earlier work was wrong

The existing theorem statement is retained. Two details in its informal plan required care.
First, the Frobenius-action-resolution existence theorem has geometric hypotheses absent here;
using it directly would add assumptions. The explicit orbit retract avoids this.
Second, `NativeOrdinaryTensorModels` supplies a model for a K-flat first input and arbitrary
second input, but its normalization hypothesis tests only two K-flat inputs. It does not state
naturality of those arbitrary values. The lower derived-square theorem therefore constructs a
natural extension to an arbitrary second input by K-flat replacement, instead of treating the
unconstrained witness from `hS` as already normalized there.

The mathematical checks include zero and unbounded complexes, arbitrary schemes satisfying
the original binders, and degenerate/empty site presentations. The orbit retract uses no
termwise-flat hypothesis. The explicit native model uses the second ringed factor's K-flatness
via `Or.inr`, consistently with the reversed tensor convention.

## New nodes

`lem-sf-native-weil-tensor-forget-kflat` records the fully proved orbit-retract argument and its
source in original step 2 / Stacks 06YS. It realizes a strict part of K-flat representative
transport, independently of all ringed and derived tensor choices.

`lem-sf-native-weil-tensor-ringed-complexes` records original steps 1--2 restricted to normalized
underived and signed complex comparisons and the K-flat localization. Its source is the
native tensor proof and Stacks 06YS, 06YU. Its `sorry` is the first remaining item.

`def-sf-native-weil-tensor-ringed-complex-model` records the explicit middle two-factor
comparison and its proved naturality. Its source is original step 2 and Stacks 06YU.

`def-sf-native-weil-tensor-ringed-model` records the actual composite native model, using the
middle comparison. Its source is original step 2 and Stacks 06YU, 0FPT.

`lem-sf-native-weil-tensor-ringed-model-naturality` records the fully proved naturality of the
native model. Its source is original step 2 and Stacks 06YU, 0FPT.

`lem-sf-native-weil-tensor-ringed-derived-square` records original step 3 for this explicit model:
the naturally extended ordinary representative, normalized tensor-forgetting square and
coherence. Its source is the native tensor proof and Stacks 06YU, 0FPT. Its `sorry` is the
second remaining item.

All six inherit the parent's chapter and unit. The blueprint ancestor lookup for the parent
returns `None`; the blueprint search for `tensor transport` returns zero matches. The new
records preserve the parent's ancestor chain and cite the internal-Hom/evaluation paragraph
of the current blueprint. LeanSearch, LeanFinder, Loogle and Mathlib source searches are recorded for each node.
There are no shared-interface changes and no change records.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
