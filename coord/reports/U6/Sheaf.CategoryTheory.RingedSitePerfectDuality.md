## What changed

Proved `CategoryTheory.ringedSitePerfectDuality` from the ordinary bounded-complex
calculation `CategoryTheory.ringedSiteStrictPerfectHom`. The public statement,
its definitions, universes and public imports are unchanged.

The item contains complete proofs of isomorphism transport, actual chain-map
representatives into K-injectives, the local-model characterization of perfectness,
cover-local detection of quasi-isomorphisms and derived isomorphisms, K-flatness of
bounded finite-free retract complexes at independent universes, and assembly of the
canonical bidual and evaluation comparisons. The dual is represented by the actual
Hom complex. A private record bundles the normalized slice comparisons to avoid
expanding a large dependent choice term during elaboration. The identity scalar
restriction comparison is constructed on module sheaves before lifting to complexes;
explicit isomorphism composition avoids unfolding the coefficient presentations.
The restriction comparison is an explicit parameter of each private local-model
lemma. Single-file compilation with hidden-hole warnings enabled passed; the
item contains no written or elaborator-generated holes. Production compilation of
both modules passed (item 20.5 seconds, ordinary-calculation module 0.2 seconds).

Repair of returned head `9f5a5a6b895`: removed the diagnostic option command
`set_option warn.sorry true`. The returned position (line 41, character 1876)
was the `sorry` component of that option name, which the hole ledger treated
as an unattributed marker. It was not an anonymous proof hole. No proof or
statement was changed by this repair; the module compiles after removal.

The ordinary bounded-complex calculation has its own module and node. It asserts
boundedness and finite-free retract splittings for the ordinary dual, the two actual
augmentation comparisons, and invertibility of the actual ordinary signed bidual
and unsigned evaluation maps. It does not assert the global local-perfect theorem
under a new name: the cover descent, passage from derived local models to actual
quasi-isomorphisms, K-flatness, canonical normalization, and natural-transformation
assembly are proved in the item.

## Proved and sorry left

Closed the original hole in `CategoryTheory.ringedSitePerfectDuality`.
Added one hole: `CategoryTheory.ringedSiteStrictPerfectHom`, node
`lem-sfb-ringed-site-strict-perfect-hom`.
The item has zero remaining holes; the new module has one. This is a decomposition
(one closed, one added; net zero), not a claim of an axiom-free target proof.
The new statement is the strictly perfect ordinary calculation of Stacks 08JH and
08JJ. Its docstring and node give the finite dual-basis and signed-complex proof.
Zero ranks, the zero ring, empty support intervals, odd shifts, characteristic two,
and arbitrary unbounded second complexes were checked against those formulas.

## No longer needed

Removed the following direct proof imports:

- `WeilConjectures.Algebra.Homology.HomComplex`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`

No source-library declarations are withdrawn. Some removed imports remain
transitive prerequisites of the canonical-map infrastructure or of the remaining
ordinary calculation; their removal here does not claim whole-library withdrawal.

The item no longer uses `lem-weil-pbc-ringed-internal-hom-exact-restriction`:
the canonical-map restriction theorem already gives the required Hom comparison.
It no longer uses `lem-pur-kinjective-restrict-localized` as a separate theorem:
the exact extension/restriction adjunction and Mathlib prove preservation of
K-injectives directly. The independent-universe bounded-flat theorem replaces
`lem-pc-bounded-above-flat-kflat-site`. Tensor descent is supplied by the normalized
model comparisons, so `lem-weil-pbc-site-derived-tensor-descent` is not applied
separately. Removed those four obsolete entries from the item's `tool_uses`.
The finite-free internal-Hom and bounded exact-source Hom calculations remain
in the new ordinary calculation's proof plan, rather than being asserted pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier diagnostic option triggered the source hole scanner: it matches
the last component of the option name as a hole token. Removing that optional
command repairs the returned packet without changing the proof or hiding a
remaining theorem hole. The one genuine remaining hole is listed above.

The planned ordinary calculation was described as elementary but did not have a
single declaration at the independent site/coefficient universes of the item.
The existing finite-free and bounded exact-source helpers fix their universes
together, so they cannot simply be specialized to this statement. The new node
records precisely the remaining ordinary calculation without changing the item.

The old bounded-flat tool also fixed the universes together. The already proved
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients` supplies the needed
independent-universe criterion; finite-free retractions imply its flatness
hypothesis by dualizability. No mathematical target or public definition changed.

## New nodes

`lem-sfb-ringed-site-strict-perfect-hom`, module
`Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom`, is the bounded strictly perfect
ordinary Hom calculation of Stacks 08JH and 08JJ, originating in the item's proof
steps 2-7. Its proof plan retains the finite-free and bounded-Hom tools and leaves
the global descent in the item. The unit route is preserved. No existing statement
or definition changes. Preflight requires a record for the
private proof context: `coord/changes/ringed-site-perfect-duality-proof-context.md`.
It documents the added local context and elaboration settings; the 338 downstream
modules have no use of the theorem name and require no adaptation.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
