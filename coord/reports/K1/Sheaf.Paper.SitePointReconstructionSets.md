## What changed

Replaced the hole in `CategoryTheory.site_point_reconstruction_sets` by a complete
Lean proof combining terminal and binary-product preservation, equalizer
preservation, Mathlib's cofiltered-elements theorem, cover surjectivity, a constructed colimiting cocone,
and naturality of the section maps. Its signature and all four public definitions
are unchanged.

The cocone has vertex `p.inverse.obj F`. Its descent map is constructed by currying
the legs into a morphism `F ⟶ p.direct.obj c.pt` and applying the given adjunction.
Both factorization and uniqueness are proved, including the required generator
formula. Thus there is no ambient large-index colimit-existence assumption.

For covering surjectivity, transpose two Boolean-valued characteristic functions
into sections of the existing direct-image sheaf and apply separatedness. This
avoids the local-representatives theorem entirely, including its larger value
universe requirement. Terminal preservation follows from the fact that the
representable terminal presheaf is already a sheaf, so its weak-reflection unit is
an isomorphism.

Binary-product preservation is also fully proved, with no universe restriction.
For any presheaf `P` and small set `E`, the composite adjunction identifies the
internal Hom from `P` to `p.direct.obj E`, evaluated at `U`, with functions from
the small set `p.inverse.obj (S.obj (yoneda.obj U × P))` to `E`. Thus its values
can be shrunk into `Type v`. The shrunk internal Hom remains a sheaf. Explicit
curry/uncurry equivalences show that product with `P` preserves weak equivalences
after applying `S ⋙ p.inverse`. Apply this to the two sheafification units and
factor the product comparison through the invertible reflection counit;
left-exactness of `p.inverse` finishes the comparison. All these helpers are
proved private declarations.

Added `Sheaf.CategoryTheory.Sites.SitePointRepresentableEqualizers` for the separate
equalizer step of Stacks 00YA (2). The main proof derives finite-limit preservation
from this step and the proved terminal and binary-product cases. The other
reconstruction clauses are proved independently of this hole. Updated the existing node's proof route and
added the new node. No adopted source-library file or public import was changed.

Validation: `lcompile.py --all` compiles both modules; the main module takes about
10.9 seconds. All Lean lines have at most 100 characters. Separate kernel axiom
checks for `pointed_cover_surjective`, `pointCocone_isColimit`,
`point_preservesTerminal`, `BinaryProductProof.relative_preservesBinaryProducts`
and `sectionHom_post` show exactly `propext`,
`Classical.choice` and `Quot.sound`. The final reconstruction theorem additionally
has `sorryAx` through the one explicitly reported equalizer lemma. Diagnostic
commands were removed from the delivered files. Unmodified copies of all three
direct consumers (`SitePointFibre`, `FpStalkRealization`, and
`OrientedPointNormalizedStratum`) also compile against the sandbox overlay.

## Proved and sorry left

Closed the original body of `CategoryTheory.site_point_reconstruction_sets`
(node `lem-trf-site-point-reconstruction-sets`), from the new equalizer lemma.
The main module now contains zero `sorry` occurrences. Cover surjectivity,
terminal and binary-product preservation, the canonical cocone's universal
property and section-map naturality are proved without new holed dependencies.

Added one hole: `CategoryTheory.sitePoint_representable_preservesEqualizers`, node
`lem-trf-site-point-representable-equalizers`. It asserts only equalizer preservation
for inverse images of sheafified representables, the specific separate source
step of 00YA (2). It has no covering, cofilteredness, cocone or naturality clauses.
Its proof is exactly `by sorry`; its docstring and node record the source argument.
Unlike the already-proved product step, this is the local-equality part of exact
sheafification. No terminal or product preservation is assumed in this new lemma.

This is a decomposition: one original hole closed and one lower hole added, net
zero. It is not a claim that the complete reconstruction theorem is axiom-free.
The unresolved issue is the arbitrary-universe sheafification comparison described
below, rather than any of the other reconstruction steps.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.
The proof no longer uses node
`lem-weil-pbc-site-sheafification-sections-local`: the covering assertion is proved
directly by separatedness of `p.direct.obj (ULift Bool)`.

The existing node's direct proof dependency
`lem-weil-pbc-sheafification-sets-exact` is replaced by the narrower equalizer source
step; that exactness node remains a dependency of the new equalizer node, so it is
not globally pruned. The explicit smallness argument through
`def-weil-size-convention` is unnecessary for the main proof: cofilteredness is
Mathlib's `Functor.isCofiltered_elements`, and the small colimit vertex is
constructed directly. All original statement dependencies are retained.

No module was withdrawn. No source-library declaration was removed. The unit's
route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The first step's claimed one-line exactness application does not elaborate with
the existing signature. The module assumes only
`HasWeakSheafify J.toGrothendieck (Type v)` with independent object universe `u`.
Mathlib's preservation instance requires `HasSheafify`, and its general set-valued
instance is for `Type (max u v)`, not `Type v`. The existing exactness leaf's match
explicitly documents this restriction. Neither a larger value universe nor an
additional `HasSheafify` hypothesis was silently introduced here.

The product step initially had the same universe obstacle, now resolved by the
relative internal-Hom construction above. The remaining equalizer source step
retains exactly the relevant original hypotheses. Formalizing the associated-sheaf comparison in these universes remains
unresolved. Its validity in that generality needs particular attention in the
independent reading; no counterexample was found. The standard small-site and
`HasSheafify` cases follow immediately from Mathlib. The old stage-2 review had
already noticed the analogous universe issue for colimit existence; that separate
issue is fully resolved here by constructing the cocone and its universal property.

Edge cases checked in the proofs: the empty covering gives the Boolean
contradiction; the terminal-object argument provides a nonempty pointed category;
the cocone construction works for every sheaf without a size hypothesis on its
index category. The new equalizer statement specializes correctly to the trivial
topology, subcanonical sites and the common-universe small-site case.

## New nodes

`lem-trf-site-point-representable-equalizers`:
`lean/Sheaf/CategoryTheory/Sites/SitePointRepresentableEqualizers.lean`, declaration
`CategoryTheory.sitePoint_representable_preservesEqualizers`. This is the equalizer
component of Stacks 00YA (2), strictly a part of the original argument. Its node
records three new searches for this equalizer step and the lack of a matching
arbitrary-universe instance, and the inherited blueprint ancestry. Change record:
`coord/changes/site-point-reconstruction-proof-scope.md` documents the conservative
interface classification of the added scoped `open` and `variable` commands.
Existing signatures, definitions and public imports are unchanged. All 34
transitive importers and their claims are listed; no adaptation is necessary.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
