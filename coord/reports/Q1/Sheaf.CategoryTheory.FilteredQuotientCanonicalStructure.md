## What changed

Proved `CategoryTheory.filteredQuotient_canonical_structure` with its existing
signature, visibility and public imports. Applied the existing first-connecting
comparison, then transported the existing derived quotient-page comparisons
through `eZ` inverse. Added one proof-only import and one separate theorem giving
only the concrete couple's D comparisons and inclusion/quotient map equations.
Updated the item's proof plan to name that normalization lemma.

## Proved and sorry left

Closed: `CategoryTheory.filteredQuotient_canonical_structure`
(node `lem-sp-filtered-quotient-canonical-structure`), the item's sole hole.
Added and currently left: `CategoryTheory.filteredHomologyCouple_normalization`
(node `lem-sp-filtered-homology-couple-normalization`). This is a decomposition,
not a net hole closure. The main theorem's proof from this smaller statement and
the two existing comparison theorems is complete. No sorry remains in the item.

The new theorem only needs the concrete definition's explicit D terms, alpha map,
and quotient map, followed by composition of equality morphisms. It contains no
spectral sequence, quotient-page comparison, or differential comparison. Its full
natural-language proof and source are in its docstring and node. The zero complex,
zero filtration, and constant filtration all satisfy its equations; no finiteness
hypothesis is needed. F8 holds the concrete-definition repair, so this delivery
does not change that held module. A provisional explicit construction used during
proof development is excluded from the delivery.

## No longer needed

No existing imports or lower modules are pruned. The new normalization lemma
encapsulates the existing concrete-couple definition used by the old proof plan;
this does not prune that definition or its data/exactness dependencies. No unit
statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The upstream-sync return reset this theorem's proof after a type mismatch. The
page-one cancellation across `↑0 + 1` and `1` needs `erw`, followed by the explicit
isomorphism cancellations in this proof. The concrete couple and its base E
isomorphism were also reset to `sorry`, so their documented construction is not
available by unfolding on the published build. An attempt to prove normalization
there fails at `Iso.refl`: Lean expects an isomorphism from the unknown
`(filteredHomologyExactCouple K F).D P Q` to filtration-step homology.
The assigned theorem's entire spectral-sequence argument compiles from the
smaller normalization statement. The main theorem also compiled without warnings
against a provisional explicit construction of the documented couple; that
construction and its compiled artifacts are excluded from this delivery. A separate
standalone explicit assembly and its normalization also compile against the
published data and exactness API with no holes. Replacing X locally by that
assembly is insufficient: the existing eQ comparisons still have the named
canonical couple as their source, and Lean rejects that source mismatch.

## New nodes

`lem-sp-filtered-homology-couple-normalization`, in
`Sheaf.CategoryTheory.FilteredHomologyCoupleNormalization`, isolates only the
filtration-step homology comparison and the two original homology-map equations.
It uses the existing concrete-couple and homology-data definitions and the
initialG definition. Its remaining work is to unfold F8's repaired concrete
construction and compose the integer equality morphisms. No change record is
needed: no existing definition, signature, visibility or public import changes.

The tested normalization calculation for the explicit assembly is:

```lean
  refine ⟨(fun P Q ↦ Iso.refl _), ?_, ?_⟩
  · intro P Q
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · intro P Q
    simp only [filteredHomologyExactCouple, BigradedExactCouple.initialG,
      filteredHomologyG, filteredHomologyEIso, eqToIso.hom, Iso.refl_hom,
      Category.id_comp, eqToHom_trans, eqToHom_refl, Category.comp_id]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
```

This is a repair guide, not the delivered proof of the still-open theorem:
its first identity isomorphism does not typecheck against the published hollow
definition. The concrete assembly must be repaired first.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
