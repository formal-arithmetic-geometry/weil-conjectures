## What changed

Proved the element-restriction comparison using explicit sectionwise Hom maps,
product projections for the Hom complexes, and canonical K-injective replacements.
For a map of sheaves, flatten the element site of its fibre sheaf and transport
through the resulting ringed module equivalence. For a site object, compare its
over site with the element site of the sheafified representable through the two
existing fibre equivalences. The regular-module comparison of actual further
restriction is the identity.

The generic projection comparison and the site-equivalence module interface avoid
repeated unfolding of concrete constructions. All new helpers are private and proved. The published theorem statement and
public imports are unchanged. No source-library module is changed.

The public signature was checked verbatim against the repository version; the
updated node changes only `proof`, `proof_deps` and `proof_origin`.
The complete module compiled through `lcompile.py` in 43.4 seconds without
warnings or errors. The delivery compile and declaration-axiom probe also passed
before static preflight requested a record for the private proof commands.
`coord/changes/E2-element-restriction-private-proof-commands.md` documents those
commands, the unchanged signature and public import, and all 313 downstream
modules. No consumer adaptation is required.

## Proved and sorry left

Closed: `CategoryTheory.element_restriction_hom` (one original hole).
Added: none. Remaining holes in this module: zero.

The proof uses the existing named theorem
`CategoryTheory.ringed_equivalence_module_hom`, which retains its own existing
hole in its separate module. This delivery does not split off any new obligation.
Its module equivalence is fixed up to natural isomorphism by the specified inverse
module functor and the equivalence adjunction.

## No longer needed

No existing nodes or modules are pruned. Replaced the direct
`HomComplex` import with its projection API `HomComplexComponents`, which still
imports the original construction. Removed redundant direct imports of
`Mathlib.CategoryTheory.Sites.Equivalence`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` and
`Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`; all three remain
available through unchanged public dependencies. No existing declarations or modules are
withdrawn. The previously stated sheaf-Hom, Hom-complex, derived-Hom, element
adjunction and representable-fibre dependencies remain used, directly or through
the proved restriction API.

## Where the brief, the DAG or earlier work was wrong

No disputed statement. Preflight requires a change record even for the added
private proof-scoping commands; the record above supplies the complete consumer
review without altering the proof or public interface. The proof makes the planned repetition on the element site
explicit through the fibre sheaf and its flattening equivalence. It uses the
existing ringed-equivalence module-Hom declaration to transport module operations
and the derived comparison. The node records these dependencies and the canonical
K-injective localization argument.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
