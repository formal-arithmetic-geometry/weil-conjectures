## What changed

The sole hole in Sheaf.RingTheory.CompletionFiniteExtensionDecomposition is replaced by a
complete proof from two new, separate comparison statements. The existing theorem signature
and public imports are unchanged. No other existing module is adapted.

The proof constructs the completion maps g by AdicCompletion.liftRingHom applied to the
quotient maps induced by Localization.localRingHom. The reduction compatibility, the required
levelwise equation, and compatibility with the R-algebra maps are proved. The tensor universal
property constructs the S-algebra map f, and its value on a tensor 1 gives the last equation.
Mathlib's Algebra.QuasiFinite.finite_primesOver proves finiteness directly. The new injectivity
and surjectivity statements then supply the two parts of bijectivity, and AlgEquiv.ofBijective
packages the constructed map as the required equivalence.

Added proof imports: Mathlib.RingTheory.TensorProduct.Maps,
Mathlib.RingTheory.QuasiFinite.Basic, Sheaf.RingTheory.CompletionTensorLocalMapsInjective,
and Sheaf.RingTheory.CompletionTensorLocalMapsSurjective. The two new modules each contain
one public theorem, with a source and a complete four-step natural-language proof.

The unchanged signature has an unused auxiliary let J. The unusedVariables linter is
disabled locally for that theorem only, so its signature can remain verbatim. Helpers and
new modules compile with the normal lint settings.

## Proved and sorry left

Closed in the item's source:
- AdicCompletion.completion_finite_extension_decomposition
  (lem-weil-pbc-completion-finite-extension-decomposition).

Added holes:
- AdicCompletion.completion_tensor_localMaps_injective
  (lem-weil-pbc-completion-tensor-local-maps-injective).
- AdicCompletion.completion_tensor_localMaps_surjective
  (lem-weil-pbc-completion-tensor-local-maps-surjective).

This is a decomposition, not a proof free of sorry: one upper hole is closed and two
strictly smaller lower holes are added. The construction and all compatibility equations
are proved; the two holes separately assert only injectivity and surjectivity of an already
given S-algebra map satisfying the coordinate formula. Neither asserts finiteness, constructs
any maps or equivalence, or by itself gives the original conclusion. The count in these
delivered modules is therefore 1 hole closed, 2 holes added (net -1).

The private helpers mapCompletion and mapCompletion_eval are completely proved. There is no
hole in a definition or private declaration, and no partial theorem proof. The equivalence's
inverse is supplied by bijectivity, which determines it uniquely; no arbitrary data is chosen
from an unproved existence theorem.

All three Lean files compile in import order via lcompile.py without errors or warnings.
The original declaration's text signature is unchanged. Source edge cases checked:
n = 0 gives the zero quotient; an empty Q gives the zero product and the zero localized finite
algebra; S = R gives a single local completion and the tensor unit isomorphism; S a product
of finite algebras gives the expected coordinate factors. Ramified finite extensions need
cofinality of the extended-base and maximal-ideal filtrations, not equality of their powers;
this is included in both lower statements' proof sketches.

## No longer needed

None. No original import or dependency module has been removed. The original node had no
usable proof dependencies: its lone proof step merely said that the theorem packages the
source argument. The detailed source ingredients remain needed in the two lower comparison
statements; they are not claimed as pruned.

Neither Sheaf.RingTheory.CompletionFiniteExtension nor
Sheaf.RingTheory.CompletionFiniteExtensionTensor is imported, avoiding the former's cycle and
the latter's arbitrary-equivalence compatibility problem. They were not original imports
and are not counted as removed or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned node did not have the numbered source plan described in the dispatcher brief:
it had one packaging sentence, no named proof dependencies. Its actual source, Stacks
algebra.tex, lemma-completion-finite-extension (Tag 07N9), was read from the locally available
copy under /home/ubuntu/work-bp/sheaf/literature/stacks-project. The repository's literature
path is absent on this machine.

The existing docstring calls B/m^n B a local algebra. In general it is semilocal, with
several maximal ideals, for example a product of two copies of the base. The unchanged
signature is correct; the new proof sketches use the Artinian quotient and its product
of localizations. The original docstring is kept as existing API.

blueprint_refs.py ancestor on the assigned node printed None because the new node's
blueprint.from lacks a via chain. The parent completion-finite-extension node identifies
thm-weil-pbc-finite-etale-lifting as the blueprint ancestor. The new nodes use that ancestor
and its existing via chain, with the present item and parent prepended. No unit statement
or realized unit step is bypassed.

LeanSearch returned Internal Server Error. Its recorded verdict is unavailable, not
no match. LeanFinder, Loogle, and grep searches ran; they found construction/tensor
ingredients but no theorem supplying the finite-prime product comparison. Searches of the
blueprint for completion and local maps found no duplicate of either new statement.

A transient shell temporary-file failure reported no space left on device while /tmp
was near its inode limit. Direct Python commands wrote only to the allowed sandbox and
resolved the report/record creation without changing project tools or other workers' files.

## New nodes

lem-weil-pbc-completion-tensor-local-maps-injective, in
lean/Sheaf/RingTheory/CompletionTensorLocalMapsInjective.lean, isolates detection of equality
by the local completion factors. Its proof follows the injectivity of the quotient product
maps, completion extensionality, change of ideal, and the finite-module tensor comparison
in Tag 07N9.

lem-weil-pbc-completion-tensor-local-maps-surjective, in
lean/Sheaf/RingTheory/CompletionTensorLocalMapsSurjective.lean, isolates interpolation of
a tuple in the local completion factors. Its proof uses the inverse quotient product maps
and their reduction compatibility, change of ideal, and the finite-module tensor comparison.
The original theorem combines these two independent directions only after constructing
the canonical map and proving all of its compatibility data.

Both records include the actual three search kinds, source place, proof dependencies, unit
and chapter, and verbatim Lean signatures. There are no statement changes or change records.

## Second reading by E3

1. I compared the delivered module with the repository version. The existing theorem
   signature and all existing declarations are unchanged; only proof imports, documentation,
   and the proof body were added. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py`; they compile without errors or
   warnings. The only remaining `sorry`s are the two named split-off comparison theorems, and
   no definition contains a `sorry`, unsafe feature, or forbidden axiom. Verdict: pass.
3. The two split-off statements are strict injectivity and surjectivity components of the
   original equivalence theorem, with source citations, complete proof sketches, and matching
   DAG nodes. Searches found no existing duplicate declaration. Verdict: pass.
4. The proof constructs the completion maps and tensor map directly, uses the finite-prime
   theorem, and retains the unit route through the two comparison statements. No import or
   dependency can be pruned without removing a used declaration. Verdict: pass.
5. The item node and both new nodes record the declarations, proof steps, dependencies, source,
   and origins used by the Lean proof. Verdict: pass.

I changed only this report section during second reading; no Lean code, statements, or DAG
records required repair.
