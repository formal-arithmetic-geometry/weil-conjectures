## Worker report

The module `Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient` states
`CategoryTheory.coherent_of_epi_of_quasiCompact_kernelPair` with a postponed `sorry`
proof. It introduces no definitions and no extra nodes. The statement is the node's
coherent quotient criterion: for a category `E` with the recorded coproduct and finite
limit structures, `hE : IsCoherentTopos.{w} E` is the coherent Grothendieck topos
hypothesis; `P` and `A` are objects of `E`; `p : P ⟶ A` is an epimorphism through the
class `[Epi p]`; `hP : IsCoherentObject.{w} P` says that the source is coherent; and
`hR : IsQuasiCompactObject.{w} (pullback p p)` says that the kernel-pair object is
quasi-compact. The conclusion `IsCoherentObject.{w} A` says that the epimorphic quotient
is coherent. `pullback p p` is the categorical pullback of the two copies of `p`, so
its two projections are the kernel-pair projections supplied by the universal
pullback object. No global quasi-compactness, separatedness, regularity, or chosen
site presentation is added to the theorem's hypotheses.

The dependency declaration used in the statement is
`Sheaf.CategoryTheory.Sites.CoherentTopos`, specifically
`CategoryTheory.IsCoherentTopos`, `CategoryTheory.IsCoherentObject`, and
`CategoryTheory.IsQuasiCompactObject`. The module imports, without `public`, the
proof-dependency modules
`Mathlib.CategoryTheory.Sites.Sheafification`,
`Mathlib.CategoryTheory.Sites.LocallySurjective`,
`Mathlib.CategoryTheory.Sites.Limits`, and the recorded proof interface
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` for the stage-3
proof plan; these imports do not alter the statement. The proof plan uses the recorded
Mathlib facts `CategoryTheory.Sheaf.isLocallySurjective_iff_epi` and
`CategoryTheory.Sheaf.createsLimitsOfShape`, the Mathlib sheafification declarations
`CategoryTheory.presheafToSheaf`, `CategoryTheory.toSheafify`, and
`CategoryTheory.sheafificationAdjunction`, and
`CategoryTheory.sheafification_sections_local` from the recorded project module.

I checked edge cases before writing the signature. The source object `P` may be empty
and the kernel pair may be an initial object; the definition of quasi-compactness in
the dependency includes the empty finite subfamily. The identity epimorphism is
covered by the same signature, and no nonemptiness of the generator family is imposed.
The pullback remains well-typed for arbitrary `p`, including `P = A` and zero-like
objects in categories with such objects. Universe levels `u`, `v`, and `w` are bound
explicitly. The containing universe is `w` in all four predicates and in
`HasCoproducts.{w}`; `def-weil-size-convention` is a metatheoretic convention with
no declaration to import. In Sets, coherent objects are finite sets and a
surjection from finite P has finite A. For p = identity, the conclusion is exactly
the assumed coherence; an empty P can only cover an initial A. The option
`set_option autoImplicit false` is enabled.

Searches for an existing declaration were made with the required tools. `msearch.py`
LeanFinder query “In a coherent Grothendieck topos if an epimorphism P to A has
coherent domain P and quasi compact kernel pair P times over A P then A is coherent”
returned only general coherent-topology and compact-space results, with no exact
match. The Loogle query `"coherent", "Epi"` returned effective-epimorphism and
coherent-topology declarations with different hypotheses. The grep query
`coherent.{0,30}(quotient|object)|quasi.?compact|quasi.?separated` in Mathlib's
`CategoryTheory` area found no matching quotient criterion. LeanSearch for “An
epimorphic quotient of a coherent topos object is coherent when its kernel pair is
quasi compact” returned generic `ObjectProperty.prop_of_epi`, `regularEpiOfKernelPair`,
and topological quotient results, not this statement. Direct `rg` over
`WeilConjectures/` and `lean/Sheaf/` found no declaration of this theorem or the
blueprint id. Thus no existing declaration was recorded.

I read the complete recorded dependency signatures and docstrings, including the
convention-only size record. The source of `def-trf-coherent-topos` defines
quasi-compactness by w-indexed families and finite subfamilies, quasi-separatedness
by arbitrary pullback squares of quasi-compact objects, and coherence by their
conjunction. Its topos predicate supplies the Grothendieck presentation and small
coherent generators. These are used without modification. The Mathlib `Epi`
class is precisely cancellation against maps from A to every target object.

I read Stacks `sites.tex` at `lemma-limit-sheaf` (00W2),
`lemma-mono-epi-sheaves` (00WN), `definition-quasi-compact-topos`,
`lemma-image-of-quasi-compact` (0GMP), and `lemma-coproduct-quasi-compact` (0GMQ).
These supply the sheaf ingredients; the quotient criterion is the DAG
agent-formulated auxiliary, not a verbatim theorem attributed to those tags.
The full seven-step proof of the node, including the iterated pullback through
R and empty-family cases, is preserved in the theorem docstring. The upstream
name index and blueprint-id grep also returned no duplicate. Search logs from
the four msearch.py invocations are retained as `searches.jsonl` in the sandbox.

No statement correction or `STATEMENT-DISPUTED` issue was found. The file compiles
cleanly with `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q37
lem-trf-coherent-epimorphic-quotient <file>`; the only postponed proof is the expected
`sorry`.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the
maintainer's independent review is the only review.
