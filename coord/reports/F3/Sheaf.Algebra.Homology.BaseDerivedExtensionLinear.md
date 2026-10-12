## What changed

Kept the signature and docstring of `ModuleCat.exists_baseDerivedExtension_linear`
unchanged. Its proof obtains a triangulated derived extension computed on resolutions,
uses Mathlib's triangulated-functor additivity instance, and applies a proved scalar
transport theorem. The main module privately imports two new modules,
`Sheaf.Algebra.Homology.BaseDerivedExtensionResolution` and
`Sheaf.Algebra.Homology.BaseDerivedExtensionScalar`.

`ModuleCat.baseDerivedExtension_scalar` is proved in full, without assuming additivity
or a derived universal property of its supplied functor. Ordinary extension sends
scalar identity maps to the corresponding B-scalar identity maps by tensor balancing.
`ShortComplex.homologyMap_smul` and naturality of the two homology factorization
isomorphisms give the ordinary homology equation. Counit naturality and cancellation
prove it on a resolution; cancellation of the derived image of its quasi-isomorphism
proves it on the original complex. All helper lemmas are private and proved.

The source proof was read at `more-algebra.tex`, lemma-derived-base-change (Tag 06Y6),
including its preceding construction. The new nodes preserve that K-flat resolving
class route. No unit statement or realized proof step changes. All three modules
compile together with lcompile.py without warnings.

## Proved and sorry left

Closed the original hole in `ModuleCat.exists_baseDerivedExtension_linear`
(node `lem-pc-base-derived-extension-linear`). Proved the new theorem
`ModuleCat.baseDerivedExtension_scalar` (node `lem-pc-base-derived-extension-scalar`),
along with private ordinary scalar extension and complex homology scalar lemmas.

Added exactly one hole: `ModuleCat.exists_baseDerivedExtension_resolution`
(node `lem-pc-base-derived-extension-resolution`), in its own module. Its proof is
exactly `by sorry`, with a complete proof plan in its docstring. It asserts the
triangulated universal pair and a resolution where the counit is invertible; it asserts
no scalar identity. This is a decomposition with one original hole closed and one
lower hole added, net zero holes. The entire scalar transport and the deduction of
additivity are formalized; no claim is made that the derived existence is sorry-free.

Edge cases checked mathematically: zero coefficient rings, zero complexes, scalars
zero and one, unbounded complexes, and non-flat B over R. The proof never assumes
that ordinary extension preserves the augmentation quasi-isomorphism. No data
is defined by choosing from an unproved mere existence statement.

## No longer needed

Removed the three direct proof imports from the main module:
`Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`,
`Sheaf.Algebra.Homology.KFlatResolution`, and
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
Their respective nodes `lem-pc-derived-tensor-second-factor-functor`,
`lem-pc-kflat-resolution`, and `lem-pur-left-derived-from-kflat-class` are no longer
direct dependencies of `lem-pc-base-derived-extension-linear`; they remain the
proof plan of the new resolution node. They are not declared globally unnecessary.
The original definition dependencies remain statement dependencies. No mathematical
node is globally pruned, and no existing public import was removed or privatized.
The three original proof imports now occur on the remaining resolution theorem,
so its planned dependencies stay reachable. Removed the unnecessary public
`Mathlib.CategoryTheory.Functor.Derived.LeftDerived` import from the new scalar module.

The scalar proof needs none of the K-flat or total tensor infrastructure: only
ordinary tensor balancing, Mathlib homology naturality, and the supplied resolution
comparison property. No separate scalar-linearity existence lemma remains holed.

## Where the brief, the DAG or earlier work was wrong

The named existing declarations do not immediately instantiate the first step of the
plan. Fixed-second-factor derived tensor uses total tensor of complexes and a counit
along Q on complexes; the requested theorem uses termwise extension and a counit along
Qh. Its coefficient rings also have independent universes, while the existing mixed
tensor theorem uses equal ring and module universes. The new resolution node isolates
these construction and transport obligations rather than restating the scalar claim.

The plan's instruction to transport linearity along resolution comparisons can be
implemented without constructing a linear derived category structure or proving
linearity of the resolution functor. The proved scalar theorem uses only counit
naturality and cancellation. Additivity follows directly from triangulatedness.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and local
grep were tried. No existing declaration matching the full resolution-counit
statement was found.

## New nodes

`lem-pc-base-derived-extension-resolution`, realized by
`ModuleCat.exists_baseDerivedExtension_resolution` in
`lean/Sheaf/Algebra/Homology/BaseDerivedExtensionResolution.lean`, is the remaining
construction obligation. It preserves the K-flat existence route and contains no
scalar compatibility assertion.

`lem-pc-base-derived-extension-scalar`, realized by
`ModuleCat.baseDerivedExtension_scalar` in
`lean/Sheaf/Algebra/Homology/BaseDerivedExtensionScalar.lean`, is fully proved. It
extracts scalar transport from the resolution comparison hypothesis, independently
of the existence or derived universal property of the supplied functor.

No change record is needed: no existing signature, definition, visibility or public
import changes; no module outside the item is adapted.

## Second reading by F3

1. **Visible interface: pass.** Compared the delivered main module with the repository
   using diff and a byte comparison of its theorem signature. The original signature,
   docstring, section variables, visibility and public imports are unchanged. No existing
   definition is edited. The other two modules and their declarations are new. No forced
   adaptation or change record is required.
2. **Proof and axioms: pass.** Independently compiled all three modules in import order,
   without errors or warnings. Read every proof, including both private helpers. Scratch
   copies with `#print axioms` show exactly `propext`, `Classical.choice`, `Quot.sound` for
   `ModuleCat.baseDerivedExtension_scalar`; the main and resolution theorems additionally
   use `sorryAx`, accounted for by the sole named resolution hole. No forbidden declaration,
   hollow definition or arbitrary data choice occurs. Resolution witnesses are eliminated
   only within theorem proofs.
3. **Split statements: pass as a decomposition.** Checked the construction theorem against
   [Stacks 06Y6](https://stacks.math.columbia.edu/tag/06Y6) and the dual resolution criterion
   [Stacks 06XN](https://stacks.math.columbia.edu/tag/06XN). It isolates existence,
   triangulatedness and computation on resolutions, and has no scalar assertion. The scalar
   theorem proves that separate obligation for any supplied functor and counit. Together
   these are a real reduction, with one hole closed and one added, net zero. Checked zero
   rings/complexes, scalar zero/one, unbounded complexes and non-flat coefficient extension:
   none requires tensoring the augmentation to preserve quasi-isomorphisms. The remaining
   hole has its own source, proof docstring and node. Independent LeanFinder query on
   transport of scalars through a resolution counit returned exact-derived-functor and
   linear-localization infrastructure, not this non-flat unbounded existence theorem.
   Loogle could not resolve the queried declaration names in its index. Local searches
   confirmed tensor balancing, `ShortComplex.homologyMap_smul`, the triangulated additivity
   instance, and the upstream flat-resolution infrastructure; no duplicate of either new
   public statement was found. Closing the construction would require the total/termwise
   tensor comparison and universe transport, not a short application of an existing lemma.
4. **Route and pruning: pass.** Read all three old dependency modules and their statements.
   The shortest available scalar route uses ordinary tensor balancing, homology naturality
   and cancellation, as submitted. Additivity is an existing Mathlib triangulated-functor
   instance. Every old direct proof dependency is named under No longer needed and retained
   on the construction node. Its proof imports retain their reachability; no module is
   globally pruned. The unit `sk-thm-picard-duality` and its `realized` record are unchanged;
   this work stays below the unit route.
5. **DAG: pass.** The existing node changes only `proof`, `proof_deps` and `proof_origin`.
   The two new nodes have the required source, searches, provenance, blueprint ancestry,
   chapter, unit and verbatim Lean statement records. The union of step `uses` agrees with
   `proof_deps` for all three nodes. The scalar node describes the checked Lean proof; the
   resolution node records the still-open construction plan, matching its named hole.

Second reading changed: restored byte-identical spacing in the existing signature;
removed an unnecessary public derived-functor import from the new scalar module;
restored the three construction-plan proof imports on the remaining resolution module;
removed an extra blank line and clarified the import/pruning report. No mathematical
statement or proof argument was changed. No additional hole was closed or added.
