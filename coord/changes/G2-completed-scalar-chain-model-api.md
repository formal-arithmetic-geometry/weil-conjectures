# Canonical completion-chain proof API

The additional module `Sheaf.Paper.IntegralScalarExtensionConstructible` is unclaimed
(no claim file on 2026-10-26). Only proved private lemmas and a theorem proof are changed.
All existing declaration signatures, visibility, attributes, imports and definition
bodies are retained. No source-library (`WeilConjectures`) file is changed.

The existence proof of `integralScalarCompletionChain_existsUnique` already constructs
the composite of the termwise ordinary scalar model isomorphism and the canonical
completed scalar chain comparison. Its two-coordinate normalization calculation is
factored verbatim into `integralScalarCompletionChain_model_spec`, a proved private
lemma. The existing theorem reuses that proof; its uniqueness argument is unchanged.
A second proved private lemma `integralScalarCompletionChain_model` identifies the
uniquely selected chain map with that explicit composite.

The assigned module imports the existing module privately with `import all`, and now
uses this formula and the tensor-normalized ordinary transport's inverse formula.
Their cancellation proves the strict comparison equality without elaborating the
large cone-coordinate types again. This is a proof API for an unchanged construction;
it neither introduces a new existence witness nor changes any downstream definition.
No consumer fails or requires adaptation, and no new holes or nodes are added.
Both changed modules are compiled together; delivery checks their public declarations.
