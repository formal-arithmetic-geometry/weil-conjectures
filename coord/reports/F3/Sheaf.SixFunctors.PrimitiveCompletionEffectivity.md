## What changed

Replaced the body of `WeilConjectures.GeneratorReduction.primitiveCompletionEffectivity`
by a complete Lean reduction, preserving its signature and its public import.

The reconstruction clause follows from `purNormalizedReconstructionOfScheme` at the
fixed calculus. Finite-Tor inputs are complete by the intrinsic/legacy tower comparison;
the scalar tensor unit is complete by the existing proved `tensorUnit_complete` helper
of `OpenReconstructionEffectivity`. This helper is accessed by a proof-only `import all`.

For tensor completion, the cases involving a scalar unit use the actual left and right
unitors. For two finite-Tor inputs the new tensor lemma supplies only completeness of
the ordinary tensor. `RingedModels.tensorClosed` transports that assertion to the supplied
tensor model. The Roos/intrinsic completeness equivalence makes the actual completion
unit invertible; composition with the recorded tensor comparison proves the asserted
`IsIso`. The same argument applies to pullback using the new ordinary-pullback lemma.
No identification of derived arrows by their evaluations is used.

Added two statement modules with matching DAG nodes and revised the item's proof route.
No existing definition, statement, visibility, or source-library module changed.

Validation: `lcompile.py --all` compiled all three modules successfully on the first
attempt (54.1 s, 51.6 s, 54.1 s respectively), with exit code 0. Every added import is
used: the two new object lemmas, the existing private scalar-unit/iso-transport helpers,
normalized reconstruction, the Roos criterion, the good localization, and an auxiliary
coefficient-test datum. The original public import is preserved.

## Proved and sorry left

Original hole: `WeilConjectures.GeneratorReduction.primitiveCompletionEffectivity`
(node `lem-sf-primitive-completion-effectivity`) is reduced to two strictly smaller
completeness assertions. Its body contains zero `sorry`. This is a decomposition,
not a net proof: one old hole is replaced by two new holes, so the packet's net is -1.
The reconstruction clause and the tensor cases involving the scalar unit need neither
new hole.

New holes, and all holes in this delivery:

- `WeilConjectures.GeneratorReduction.finiteTorOrdinaryTensorComplete`, node
  `lem-sf-finite-tor-ordinary-tensor-complete`, in
  `Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete`.
- `WeilConjectures.GeneratorReduction.finiteTorOrdinaryPullComplete`, node
  `lem-sf-finite-tor-ordinary-pull-complete`, in
  `Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete`.

Each is a property of an ordinary operation object, independent of the `Operations`
record and of the primitive comparison maps. The tensor lemma handles only two finite-Tor
inputs; its scalar-unit cases are proved in the owning theorem. Neither new statement
asserts the reconstruction clause or repeats the original three-part conclusion.
Their docstrings give the source, argument, and zero/empty cases.

## No longer needed

No original import is removed and no module is withdrawn. Pruned modules: none.

The owning proof no longer directly uses `lem-fix-constructible-tensor-completion`
(`Sheaf.SixFunctors.ConstructibleTensorCompletion`) or `lem-fix-operation-reduction`
(`Sheaf.Paper.BasicOperationsCoefficientReduction`). Neither statement supplies the
ordinary-object assertions on this item's full domain. The relevant local tensor
and projective-chart steps remain dependencies of the new tensor node.

`lem-coef-normalized-dvr-effectivity` (`Sheaf.Paper.NormalizedDVREffectivity`) is no
longer a direct dependency of this node: it remains used through the proved
`purNormalizedReconstructionOfScheme` argument. The tensor/pull normalization definitions
remain used. No global unreachability of these dependencies is claimed.

## Where the brief, the DAG or earlier work was wrong

The listed tensor theorem has extra qcqs and residue-prime-invertibility hypotheses,
and its existential tensor presentation differs from the fixed ambient tensor here.
The ordinary-pullback theorem found in the library has Noetherian hypotheses.
`basicOperationsCoefficientReduction` concerns completed operations and finite comparison
maps; it does not by itself prove completeness of this ordinary ringed pullback.
The new obligations isolate those gaps without adding any hypothesis to the assigned
statement. Source checking: Bhatt--Scholze Section 6.5, pp. 49--51, and the local Stacks
`proetale.tex` proofs of Tags 099M/099N. In particular Tag 099N(5) describes completed
pullback; ordinary-pullback completeness still requires the local-model argument.

The current blueprint proof text gives its maps-used sentence but does not contain the
numbered generator-realization step 3 named by the existing docstring. The existing
docstring and theorem signature are preserved; the DAG now records the actual Lean route.

## New nodes

`lem-sf-finite-tor-ordinary-tensor-complete` states completeness of the fixed ordinary
tensor for two finite-Tor constructible integral inputs. Its source is Bhatt--Scholze
Lemma 6.5.5 and its proof is local finite-projective devissage through constructible
strata. It does not include scalar-unit cases or assert any comparison-map property.

`lem-sf-finite-tor-ordinary-pull-complete` states completeness of ordinary ringed pullback
for the primitive input domain. Its source is the local-model pullback argument of
Bhatt--Scholze Section 6.5 and Stacks 099N(5), with the distinction between ordinary and
completed pullback retained explicitly. Both nodes record LeanSearch, LeanFinder,
Loogle and source grep searches; blueprint phrase searches found no duplicate.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
