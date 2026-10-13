## What changed

Replaced the only hole in `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction`
without changing its statement, universes, visibility or public imports. The proof takes the
actual localization preimage of the restricted N, constructs ordinary evaluation with the
existing degree maps and differential identity, proves it is a chain isomorphism using
`isIso_localOrdinaryEvaluation_degree`, and writes the retraction explicitly as
`b.hom ≫ (Q.mapIso (asIso f)).inv ≫ a.inv`. The commuting square and the two inverse identities
prove the required source identity.
The additional elaboration settings are scoped to this theorem; the existing module's
namespace openings and interface commands remain unchanged.

Added `Sheaf.AlgebraicGeometry.StrictlyPerfectLocalHomComputations`, fully proved from existing
named declarations. Its private helpers prove that short exactness descends to a retract and
that internal Hom from a finite free retract is exact. Bounded exact-term Hom then preserves
quasi-isomorphisms. Applying this to `0 → F` for acyclic F proves that Hom(P,F) is acyclic;
ordinary evaluation transports this to the tensor with the ordinary dual. Thus the dual is
K-flat directly, without a second termwise-flatness calculation.

Added `Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons` to isolate the remaining
representative equation. Its assumptions are preservation of quasi-isomorphisms by Hom(P,-)
and K-flatness of the ordinary dual. It assumes no strict perfectness, and concludes a model
square, with no inverse or invertibility assertion. Its docstring and node contain the
resolution, restriction, tensor-model and componentwise uncurrying argument to be formalized.

The source was read at Stacks Tags 08DQ (lemma-dual-perfect-complex), 08DM
(lemma-Rhom-strictly-perfect) and 08DL (lemma-restriction-RHom-to-U), online because the local
literature checkout contains no cohomology.tex. Search logs are in searches.jsonl. LeanSearch
returned Internal Server Error; LeanFinder and Mathlib grep supplied no matching theorem.
Library searches found the usable ordinary evaluation and differential declarations.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_strictlyPerfect_evaluation_local_retraction`
(node `lem-pc-strictly-perfect-evaluation-local-retraction`). No holes remain in the item.

Also proved the new theorem `AlgebraicGeometry.strictlyPerfect_localHom_computations`
(node `lem-pc-strictly-perfect-local-hom-computations`), including both Hom preservation and
K-flatness of the actual ordinary dual. Its two private helpers are proved.

Added exactly one hole:
`AlgebraicGeometry.exists_exactSource_evaluation_local_comparisons`
(node `lem-pc-exact-source-evaluation-local-comparisons`). Its proof is exactly `:= by sorry`.
This is a decomposition: one original hole closed and one new hole added, net zero among the
delivered declarations. Existing imported obligations remain existing items. This delivery
does not claim that the targets now have only standard axioms.

The remaining comparison lemma is strictly a model-computation step: even an infinite free
module over a field can satisfy its Hom-preservation and dual-K-flatness assumptions while
ordinary tensor-to-Hom evaluation need not be invertible. The final proof uses the additional
finite free retract condition separately, through the existing degreewise evaluation theorem.
It therefore does not merely apply a renamed inverse-existence assertion.

Edge cases: the retract proof uses only `i ≫ p = 𝟙`, also for rank zero; empty U and zero P
produce the same zero maps. Bounds with b<a cause no issue for the existing bounded Hom theorem.
The acyclicity argument imposes no bound on F, and the comparison lemma keeps arbitrary F.
The unit record `sk-thm-picard-duality` has empty realized statement/step arrays; the finite
locally free tensor-Hom identification in the ancestor's final paragraph is preserved.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` and pruned
`lem-pc-bounded-above-flat-kflat-site` from this proof route. Ordinary evaluation and exact Hom
prove dual K-flatness directly. The dual-term support, finite-free-dual retraction and
termwise-flatness subargument in the original plan is unnecessary here. No library file is
deleted. The module still occurs transitively through the necessary canonical-family imports
(`CanonicalDerivedTensorHom → KFlatResolution → KFlatTelescopeClosure`), so this removes a direct
proof dependency and a subargument, not a whole module from the targets' import closure.

The other removed direct imports are still needed through the new modules:
`Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact` are used by the proved local
Hom computation; `Sheaf.Paper.DerivedInternalHomRestrictOpen` and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` are dependencies of the remaining model
computation. These are relocated dependencies, not globally pruned modules.

The second reader also removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation` from the item and the new local
Hom module: `OrdinaryEvaluationDifferential` already publicly imports it. Its degreewise
isomorphism theorem remains used; its node is not pruned.

For completeness, the old node's dependencies no longer listed directly in its new
`proof_deps` have the following dispositions:

- `lem-pc-bounded-above-flat-kflat-site`: no longer used by this argument.
- `lem-pc-bounded-exact-term-hom-quasi-iso` and `lem-sc-finite-free-internal-hom-exact`:
  used inside `lem-pc-strictly-perfect-local-hom-computations`.
- `lem-sc-derived-internal-hom-restrict-open`, `prop-pur-kinjective-resolutions-exist`,
  and `def-pc-tensor-complex-sheaves`: used inside
  `lem-pc-exact-source-evaluation-local-comparisons`.
- `def-pc-canonical-derived-tensor-hom-bijection`, `def-pc-scheme-derived-tensor-structure`,
  and `def-pur-derived-internal-hom`: retained in the signature and the new comparison node.
- `def-pc-perfect-complex`: retained in the signature and local Hom computation node.
- `def-pur-hom-complex`: retained in the signatures of the new nodes and their ordinary models.

All other old proof dependencies remain as statement/definition dependencies or inside the
new model computation. The existing upper evaluation model and comparison modules are not
imported; their dependency paths already reach the item and would close a cycle. No UNIT
statement or realized proof step is removed.

## Where the brief, the DAG or earlier work was wrong

The planned ordinary-model comparison is not available from the listed structural statements
alone. In particular, `StrictlyPerfectEvaluationComparisons` imports
`StrictlyPerfectKInjectiveEvaluationComparisons`, whose proof already invokes this local
retraction and the local section. Likewise `StrictlyPerfectEvaluationModel` reaches those
comparisons. `tools/import_direction.py may` confirms that importing the existing comparisons
here closes a cycle. The new comparison obligation therefore uses weaker, independent
Hom-preservation/K-flatness assumptions and follows the source's representative calculation,
without invoking any local inverse theorem. No existing statement is disputed or changed.

The original plan's separate flatness calculation is longer than necessary: the already
proved ordinary evaluation provides a direct acyclicity proof of dual K-flatness. The node
proof and proof_deps now record that route. The existing theorem docstring retains its source
proof sketch; the new theorem docstrings give the proof actually implemented in the new modules.

## New nodes

`lem-pc-strictly-perfect-local-hom-computations`, in
`Sheaf.AlgebraicGeometry.StrictlyPerfectLocalHomComputations`: a proved local computation for
strictly perfect P, combining preservation of quasi-isomorphisms and K-flatness of its actual
ordinary dual. Its proof records the finite free retract exactness argument, the bounded Hom
lemma, the zero-complex product calculation and the ordinary-evaluation acyclicity transport.

`lem-pc-exact-source-evaluation-local-comparisons`, in
`Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons`: the unresolved generalized
representative equation, requiring exact Hom on quasi-isomorphisms and a K-flat ordinary dual,
and asserting compatible object models and equality of the localized maps. Its proof steps
record the canonical-resolution computation from Stacks 08DM/08DL/08DQ and the 08DJ adjunct
component formula, without any ordinary or derived evaluation inverse.

Both nodes inherit the item's chapter and unit and trace to `lem-sc-finite-duality`, final
proof paragraph. Blueprint searches for ordinary evaluation, K-flat dual and Hom
quasi-isomorphisms found no imported blueprint statement for these computations. The Mathlib
searches are actual logged queries, with unavailable LeanSearch recorded as unavailable.
There are no statement changes, changed definitions, forced adaptations or change records.

## Second reading by X2

1. Interface check: diffed the item against the repository. The sole existing theorem's
   complete signature, universes, visibility and docstring are byte for byte unchanged;
   its two public imports remain unchanged. The only new declarations outside it are the
   two reported theorem modules and proved private helpers. No definition changes, forced
   adaptations or change records are needed. Read the landed ordinary-evaluation relocation
   record; these proofs use its unchanged definitions through the current public reexports.
2. Proof check: read the short-complex retraction, finite-free Hom calculation, acyclicity
   transport, and explicit localized inverse calculation. The object preimage comes from
   the existing localization functor, not an unproved existence theorem. No new definitions
   select witnesses. There is exactly one `sorry`, in the named comparison theorem, with
   its source, complete resolution/component proof docstring and matching node. No axiom,
   unsafe/opaque declaration, extern, implemented_by or kernel-check bypass occurs.
3. Split check: read Stacks [08DQ](https://stacks.math.columbia.edu/tag/08DQ),
   [08DM](https://stacks.math.columbia.edu/tag/08DM),
   [08DL](https://stacks.math.columbia.edu/tag/08DL) and
   [08DJ](https://stacks.math.columbia.edu/tag/08DJ). The generalized comparison uses precisely
   Hom preservation to compute both target and dual, and dual K-flatness to compute the
   source tensor; it asserts the representative square and no inverse. The finite-retract
   condition is used separately by the upper proof to invert ordinary evaluation. On a
   one-point space over a field with P an infinite free module in degree zero and F=P,
   Hom(P,-) is exact and its dual is flat, but evaluation has only finite-rank image and
   misses the identity of P. Thus the comparison statement is not a disguised inverse
   assertion. Also checked empty opens, P=0, F=0, rank zero, reversed bounds and unbounded F:
   none needs an additional hypothesis. Repeated LeanFinder, Loogle and Mathlib grep with
   restriction/localization/retract queries different from the first worker's; no matching
   theorem. Library searches found private retract/Hom helpers in the upper comparisons,
   but importing that module would cycle through this item; they are not reusable here.
   The general upstream retract-of-exact-functors theorem requires extra functor/naturality
   setup and does not shorten the direct short-complex argument. The remaining comparison
   requires a substantial representative calculation; it cannot be closed by the available
   object isomorphisms alone in a short repair.
4. Route/pruning check: the target proof starts with the actual ordinary evaluation and
   uses existing degree-map and degreewise-isomorphism declarations. Its only new unresolved
   input is the smaller representative computation. Removed the redundant direct ordinary
   evaluation import from both the item and local Hom module, keeping it publicly available
   through OrdinaryEvaluationDifferential. The No longer needed section now explicitly
   accounts for every removed old direct proof dependency, distinguishing relocated
   dependencies from the flatness argument no longer used. No whole module leaves the
   targets' closure. Read sk-thm-picard-duality.realized (empty statement and step arrays)
   and the finite-duality ancestor: no unit statement, step or finite tensor-Hom route is
   replaced. This is a net-zero decomposition, not a claim of a fully proved target.
5. Node check: the old node differs only in proof, proof_deps and proof_origin. Each node's
   proof_deps is exactly the union of its steps' uses. Both new node Lean signatures match
   their modules verbatim and have the required source, origin, searches, creation,
   blueprint ancestry, chapter/unit and split status. Their statements use the actual Hom
   dual and tensor, not an unspecified object. Added Tag 08DJ to the comparison node's source and proof_origin place so its
   recorded sources include the representative equation used in step 3.

Second-reading changes: removed two redundant direct proof imports and made dependency
accounting explicit in this report, and completed the comparison node's source citation
with Tag 08DJ; theorem proofs and statements are retained.

Validation: compiled all three delivered modules in import order through lcompile.py,
with no errors or warnings. Compiled scratch copies with #print axioms for all three public
theorems and both private helpers. The public theorems use only propext, Classical.choice,
Quot.sound and sorryAx (remaining imported obligations and the recorded split). Both private
helpers use only propext, Classical.choice and Quot.sound. Removed the scratch copies.
