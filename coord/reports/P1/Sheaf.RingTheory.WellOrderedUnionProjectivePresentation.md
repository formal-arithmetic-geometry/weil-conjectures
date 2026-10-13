## What changed

The signature and visibility of
`ModuleCat.exists_shortExact_projective_middle_of_wellOrderedUnion_succ` are unchanged.
Its proof now chooses the bounded resolutions supplied by `hquot`, obtains a projective
presentation with an exhaustive kernel filtration, bounds each kernel quotient, and applies
`hIH` to that filtration. Two proof-only imports were added:
`Sheaf.RingTheory.WellOrderedPresentationKernelFiltration` and
`Sheaf.RingTheory.ProjectiveResolutionAugmentationKernel`.

The latter module contains a complete proof that truncating a supplied length-`n+1`
projective resolution resolves its augmentation kernel in length `n`. It factors the
first differential through the kernel, proves that factor is epi using `P.exact₀`, checks
exactness through the monic kernel inclusion, and verifies the quasi-isomorphism and
vanishing bound degree by degree. Private proved helpers in the item transport bounded
resolutions through isomorphisms and resolve zero objects. No library data or definition
is chosen from an unproved existence assertion.

The remaining transfinite construction is isolated in the former module. It assumes a
family of supplied quotient resolutions, with neither a dimension bound nor `hIH`.
It supplies a projective presentation and kernel filtration whose quotients are zero or
isomorphic to the augmentation kernels of those particular resolutions. This preserves
the resolution needed by the truncation proof, rather than using Schanuel to compare
an unrelated projective presentation. The item's copied node records this proof route.

All three modules compile together with `lcompile.py --all` without warnings. The new
statements were checked at a least index, a single stage, repeated stages, a zero module,
and `n = 0`: predecessor sums start at zero, repeated stages contribute zero quotients,
a zero module can use the zero presentation, and truncation at bound one gives a
length-zero resolution. An empty index type is impossible by covering zero. The shrinking
argument applies only to nonzero stage quotients: their chosen representatives inject
into `M`. Arbitrary nonzero degree-zero terms of resolutions of zero stage quotients are
ignored, so a large set of repeated stages does not invalidate the universe bound.

## Proved and sorry left

Closed the item's original hole in
`ModuleCat.exists_shortExact_projective_middle_of_wellOrderedUnion_succ`
(node `lem-weil-pbc-well-ordered-union-succ-data`). There are no `sorry`s in the item.

Also proved
`ModuleCat.hasProjectiveResolutionLE_augmentation_kernel`
(node `lem-weil-pbc-projective-resolution-augmentation-kernel`). Its proof uses only
Mathlib and the actual bounded-resolution definition. The two private helpers
`resolution_bound_of_isZero` and `resolution_bound_of_iso` are proved.

Added and left exactly one hole:
`ModuleCat.exists_projective_presentation_kernel_filtration`
(node `lem-weil-pbc-well-ordered-presentation-kernel-filtration`), in the new module
`Sheaf.RingTheory.WellOrderedPresentationKernelFiltration`.
This is a decomposition: one upper hole closed and one strictly simpler construction
hole added, with the dimension-shifting and induction glue proved. The net hole change
is zero; this does not claim an axiom-free proof of the original theorem.

## No longer needed

No existing imports were removed: the original four public imports supply its statement.
The second reading replaced the new kernel-filtration module's public import of
`Sheaf.RingTheory.GlobalDimension` by
`Mathlib.CategoryTheory.Preadditive.Projective.Resolution`: its statement uses
`ProjectiveResolution`, not the custom bounded-resolution predicate. This removes
an unnecessary import of the upstream projectivity comparison infrastructure.
No unit-level route was changed; neither the item nor its new lemmas replaces a realized
unit statement or step of `sk-thm-p1`.

The copied item node no longer has proof edges to:

- `lem-weil-pbc-projective-dimension-ses-kernel`, whose module is
  `Sheaf.RingTheory.ProjectiveDimensionSESKernel`;
- `lem-weil-pbc-projective-direct-sum-family` (Mathlib's unrestricted module-projectivity
  result is replaced in the construction's proof by categorical componentwise lifting);
- `lem-weil-pbc-ses-projective-quotient-splits` (source-projectivity lifts augmentations
  through quotient epis; splitting a projective quotient is unnecessary).

Three further old direct proof edges are now delegated to the kernel-filtration node:
`def-weil-pbc-direct-sum-modules`, `def-weil-pbc-exact-sequence`, and
`def-weil-pbc-quotient-module`. They remain transitive construction dependencies;
the exact-sequence and quotient notions also remain in the item's unchanged signature.
Together these six names are every old `proof_deps` entry absent from the new list.

Schanuel, resolution Ext characterization, and the enough-projectives-based SES kernel
bound are not imported. The direct-sum, quotient, and exact-sequence definition nodes
remain needed by the construction and are not globally pruned. The finite-global-dimension
node remains needed by all the bounded-resolution proofs. The three removed proof edges
are route pruning; no claim is made that their modules are now absent from every target's
closure, since other items may still use them.

## Where the brief, the DAG or earlier work was wrong

The old Step 3 called for a Schanuel comparison. That comparison is unnecessary because
the filtration construction can retain the degree-zero augmentations of the chosen
quotient resolutions: its kernel quotients identify with their augmentation kernels.
Truncation then gives the bound directly. The old SES-kernel Lean interface is restricted
to module universe `max u v`, so it cannot be applied to the unchanged signature here;
the new proved truncation lemma preserves independent universes and requires no
enough-projectives instance.

The local literature checkout has no `literature/stacks-project/algebra.tex`; I read the
source proofs at the public Stacks pages for tags 0D1U and 065S. The source's free-module
construction is replaced by the supplied projective presentations as already specified
in this item's docstring. LeanSearch returned Internal Server Error; its recorded
searches are unavailable, not negative search results. LeanFinder/Loogle and the Mathlib
source searches found infrastructure, but no theorem giving the required construction.

`blueprint_refs.py ancestor` cannot trace this item's `created.item`, which is a module
name from an earlier stage-3 delivery. The new nodes use the documented blueprint ancestor
of `lem-weil-pbc-well-ordered-union-projective-dimension`,
`thm-weil-pbc-finite-etale-lifting`, with the intervening nodes included in `via`.

The nested names `hF`, `hcover`, and `hquot` inside the type of `hIH` trigger Lean's
unused-variable linter once the original hole is closed. A declaration-local linter
option, as in the already proved successor module, preserves these existing binder names
and the entire signature. It does not suppress warnings elsewhere.

## New nodes

`lem-weil-pbc-projective-resolution-augmentation-kernel` records the completely proved
truncation lemma, with its exact Lean signature, source, proof steps, and three recorded
search kinds. Its module is `Sheaf.RingTheory.ProjectiveResolutionAugmentationKernel`.

`lem-weil-pbc-well-ordered-presentation-kernel-filtration` records the remaining
construction independently of all dimension bounds and the induction hypothesis.
Its source, complete natural-language construction (including shrinking, finite support,
and the quotient-kernel identification), exact Lean signature, and three recorded search
kinds are in its new module and node. Its module is
`Sheaf.RingTheory.WellOrderedPresentationKernelFiltration`.

No existing statements or definitions were changed, no adaptations were required, and
there are no change records.

## Second reading by P1

1. **Interfaces: pass.** Read all three delivered modules and diffed the item against
   the repository. The entire signature of
   `exists_shortExact_projective_middle_of_wellOrderedUnion_succ`, including the
   universes, all binders in `hIH`, and the equality `S.X₃ = M`, is byte-for-byte
   identical. The only existing node fields changed are `proof`, `proof_deps`, and
   `proof_origin`. No definitions, target statements, or other modules were adapted.

2. **Proof and trust: pass as a decomposition.** Compiled the three modules in import
   order without warnings, and compiled scratch copies with `#print axioms` for all
   five declarations, including both private helpers. The truncation theorem and
   private helpers use only `propext`, `Classical.choice`, and `Quot.sound`.
   The item and kernel-filtration theorem additionally use `sorryAx`, exactly as
   expected from the single named construction hole. There is no forbidden construct
   or definition containing a hole. The chosen resolutions come from the local
   hypothesis `hquot`; the short exact complex is used only inside a proposition's
   proof, not to define arbitrary library data. In the truncation proof, checked
   the monic kernel inclusion in `hw`, the identity/identity/monic short-complex
   comparison in `hex`, both quasi-isomorphism cases, and the shifted vanishing bound.

3. **New statements: pass.** Read the successor construction of
   [Stacks 0D1U](https://stacks.math.columbia.edu/tag/0D1U) and clause (1) of
   [Stacks 065S](https://stacks.math.columbia.edu/tag/065S). The new construction
   isolates the presentation and its kernel filtration; it contains neither `n`
   nor `hIH` and does not assert a kernel dimension bound. The separate, fully proved
   truncation theorem supplies that bound. This is a real reduction rather than a
   renamed copy of the item. Independently checked a least stage, one stage, repeated
   stages with arbitrary resolutions of zero quotients, a zero module, `n = 0`, and
   an empty index type. Skipping zero quotient stages is essential: otherwise an
   arbitrarily large family of nonzero degree-zero terms would defeat shrinking.
   Active stages inject into `M`; finite supports put every kernel vector in a
   partial sum, and subtracting a predecessor lift makes the projection onto an
   active summand surjective onto its augmentation kernel. These verify all clauses
   of the construction under the stated hypotheses, including independent universes.
   Its docstring gives the full argument and its node supplies the source.
   New independent LeanFinder search for "Eklof lemma transfinite extension
   projective modules kernel of coproduct presentation" returned projectivity,
   enough-projectives and finite-presentation infrastructure, not this theorem.
   Loogle `"ProjectiveResolution", "kernel"` returned only the cokernel cofork and
   its colimit theorem. Searches of the whole upstream source, `lean/Sheaf`, and
   Mathlib's projective-resolution sources found no existing matching construction
   or bounded augmentation-kernel theorem. The open construction is not something
   that can be closed by a short application of the found declarations.

4. **Route and pruning: pass after repair.** The item chooses the supplied resolutions,
   applies the construction, handles zero quotients by the identity resolution,
   transports truncated resolutions through the supplied isomorphisms, and applies
   exactly the given `hIH` to the resulting exhaustive filtration. The unit
   `sk-thm-p1`'s `realized` statement and every step were read and are unchanged;
   these subsidiary lemmas bypass none of them. All six removed direct proof edges
   are now listed above; the three definition edges remain transitive dependencies.
   Replaced the construction's unnecessary `GlobalDimension` import by the Mathlib
   resolution module. Kept public `ModuleCat.Abelian`: the signature needs its
   registered kernel instance (the concrete `Kernels` module alone does not supply
   a global instance). The item's added imports and the truncation's augmentation
   and abelian-resolution imports remain proof-only. No whole module is claimed
   pruned from the targets' closure. Net holes closed minus added remains zero.

5. **DAG: pass.** Checked each node's stored Lean signature against its declaration
   verbatim, and each `proof_deps` against the union of its proof steps' `uses`.
   The item cites the construction and truncation it actually applies; the new
   nodes record the presentation, exactness, quotient, direct-sum, and bounded
   resolution notions used in their arguments. Their source, proof, origin,
   searches (including the unavailable LeanSearch service), blueprint ancestor,
   chapter, unit, creation and Lean records are present. The construction's
   natural-language proof agrees with its zero-or-isomorphism conclusion.

Second reading changed only the new construction module's unnecessary import and
the report's incomplete list of removed direct proof edges. No proof body or
statement needed repair. One original hole is closed, one strictly smaller hole
is added, and the auxiliary truncation theorem is independently axiom-clean.
