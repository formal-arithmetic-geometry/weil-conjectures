## What changed

Replaced the body of
`CategoryTheory.ConstantModuleDerivedProjection.constant_module_tensor_square_descent`
with a construction of the ordinary ringed monoidal structure and both normalized derived
monoidal structures, followed by a reduction to two compatibility statements. The existing
public signature, statement imports and definitions are unchanged. All added imports of the
item are private proof imports.

Added the proved module `Sheaf.CategoryTheory.ExactDerivedMonoidalConstruction` to
separate the general localization construction from its application after local instance
selection and abstraction improved the slow flatness transport. This keeps each file
within the compile limit. Its proved private helper `monoidal_localization` derives two
tensor bifunctors through a resolving subcategory and applies `OplaxMonoidal.ofLaxSquare` to transfer coherence. The
proved public theorem `exact_monoidal_normalization` applies it to functorial flat resolutions,
using source K-flat complexes whose images are K-flat. The construction works with the four
chosen localization instances and does not specialize their universes. The ringed flatness
and fixed-scalar flatness transport are proved separately. The scalar normalization
helper and ordinary square use the same cached canonical braided structure as the scalar
comparison data. A generic proved bridge converts the independent-coefficient K-flat
normalization to `TensorNormalization`, so the conversion is checked with abstract tensor
structures instead of repeatedly expanding the sheaf constructions during kernel checking. The canonical ordinary ringed
structure reuses the already proved `ringMonoidal_exists` of ordinary realization.

Added `Sheaf.CategoryTheory.ConstantModuleOrdinaryTensorSquare` for ordinary mate tensor
compatibility, and `Sheaf.CategoryTheory.NormalizedExactTensorSquare` for the compatibility
of already constructed and normalized derived structures. Both retain the ordinary and
localized isomorphisms supplied by the caller.

## Proved and sorry left

Original holes: 1, in
`CategoryTheory.ConstantModuleDerivedProjection.constant_module_tensor_square_descent`.
Its body is now complete from the stated intermediate declarations. The item has zero
remaining holes. Two new holes are added:

- `CategoryTheory.ConstantModuleDerivedProjection.constant_module_ordinary_tensor_square`,
  node `lem-sfb-constant-module-ordinary-tensor-square`.
- `CategoryTheory.ConstantModuleDerivedProjection.normalized_exact_tensor_square`,
  node `lem-sfb-normalized-exact-tensor-square`.

This is a decomposition, not a completed axiom-free proof of the original obligation:
one upper hole closed, two strictly smaller compatibility holes added, net -1 hole.
The new theorem
`CategoryTheory.ConstantModuleDerivedProjection.exact_monoidal_normalization`
is fully proved without a new hole. The construction of the two derived monoidal structures
and their normalizations is proved; no new existence theorem is assumed and no data definition contains a hole.

## No longer needed

No original import was removed: the item's sole original import supplies its public signature.
The old proof dependencies below are not directly needed by the new proof:

- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: replaced by the canonical ordinary
  ringed monoidal helper and the explicit generic localization construction.
- `lem-pur-cochain-pullback-tensor-coherence`: the construction uses the source library's
  general `mapCochainComplexMonoidal`; square compatibility uses signed totals in the new
  generic intermediate statement.
- `lem-pc-kflat-resolution`: replaced here by native functorial flat resolutions and their
  proved image K-flatness API.
- `lem-weil-pbc-site-derived-tensor-descent` and
  `lem-sfb-ringed-equivalence-resolving-tensor-descent`: replaced by the explicit two-variable
  resolving construction and the generic compatibility step, which accepts chosen universes.
- `lem-sfb-exact-tensor-functor-derived-normalization`: its statement normalizes given
  representative tensor maps; the private localization proof constructs the maps and their
  coherence together.
- `def-weil-pbc-ringed-tensor-section-calculus` is used by the new ordinary compatibility
  obligation, rather than directly in the item proof.

These are changes in proof dependencies only. Existing statement dependencies are preserved;
no module is withdrawn and no declaration from the adopted source tree is removed. Some of
these nodes remain reachable through statement dependencies or other consumers. This delivery
does not claim a whole-library module pruning count for them.

## Where the brief, the DAG or earlier work was wrong

The planned exact-derived normalization theorem does not by itself construct a derived
monoidal structure: it takes the representative tensor transformation as input. The proof
therefore constructs that transformation using left-derived bifunctors. The preexisting
`exactDerivedSquare_monoidal` theorem fixes Hom/localization universes and canonical
transported structures, whereas the present statement has arbitrary supplied localization
instances and scalar comparisons. It cannot directly discharge the required square.

Only flat-term K-flat resolutions and their images are needed. The proof avoids relying on
an unproved assertion that every exact flat-preserving strong monoidal functor preserves
all K-flat complexes. The ringed flatness theorem needs explicit coefficient and site
universes in this application.

Edge cases checked in the statements: no nonzero-ring assumption, enough-points assumption,
boundedness or Tor-amplitude assumption is introduced. The generic compatibility lemma
assumes all four existing normalizations and the full localization equation, so there is
no unconstrained choice of a derived tensorator or isomorphism. No target statement changes.

## New nodes

`lem-sfb-constant-module-ordinary-tensor-square` records original proof step 1, the tensor
compatibility of the mate on ordinary sheaves. Its conclusion contains no derived categories
and no existence of structures. The supplied `FixedTensorData` pins the geometric insertion
by its mate equation and its tensorator by its generalized pure-tensor equation.

`lem-sfb-normalized-exact-tensor-square` records the compatibility portion of original proof
steps 2–3. It starts with four ordinary and four derived strong monoidal structures, their
four representative normalizations, an ordinary commuting square, and the specified
localization equation. It only proves the derived square; it constructs none of the
structures required by the original theorem. Its model proof uses common flat-term K-flat
resolutions, signed totals, and cancellation of localization isomorphisms.

`lem-sfb-exact-derived-monoidal-construction` records the proved construction portion of
original step 2. It applies to arbitrary exact flat-preserving strong monoidal functors and
chosen localization universes. The module contains a complete localization proof, with no
new hole. Its representative equation is precisely the existing `TensorNormalization`.

The four modules passed their individual `lcompile.py` checks: the final item in 10.0 s,
ordinary square in 8.2 s, normalized derived square in 4.8 s, and proved monoidal
construction in 2.0 s (18.4 s on its first full check). The first delivery recheck timed out on the ordinary square, so it now uses the same
local irreducibility and additive-instance selection as the item; the revised file checked
in 3.6 s with no expensive declaration reported by the profiler. Profiling options have
been removed. No original signature
changes are involved. The original theorem signature is preserved verbatim;
node proof dependencies were checked for consistency and cycles.

No change record is required: no existing public interface or definition was changed.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
