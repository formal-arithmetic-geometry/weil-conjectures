## What changed

Proved `AlgebraicGeometry.Scheme.Modules.elementary_devissage_finite_presentation`
in `Sheaf.TraceFormula.ElementaryDevissageFinitePresentation`, with its original
signature unchanged. Added a fully proved private helper
`finitePresentation_stalk_iff_flat_pullback`: identify a tensor-pullback stalk
with extension of scalars, ascend finite presentation by tensor base change,
and descend along the faithfully flat local ring map.

The main proof obtains local finite presentation of f' and π by cancellation,
uses the existing finite-pushforward comparison twice (for i and π), and
transports the comparisons through the given sheaf isomorphism. Finite
presentation is transported on neighbourhoods by restriction of that
isomorphism, and on stalks by its image under moduleStalkFunctor.

Added proof imports of
`WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
Updated the item's DAG proof and dependencies to the actual argument. No
public signatures, definitions, public imports, or other modules changed.

Read Stacks flat.tex, Tag 057T, including its neighbourhood and separate
stalkwise assertions. The proof preserves that distinction; it never infers
finite presentation on a neighbourhood from finite presentation at a stalk.
The existing cancellation lemma (lem-a1-map-over-base-finite-presentation) is
used as a proved tool, and the existing pullback-stalk node is used for its
canonical scalar-extension isomorphism. The unit route is unchanged.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.Modules.elementary_devissage_finite_presentation`
(node `lem-trf-elementary-devissage-finite-presentation`).

Added 0 holes. There are 0 remaining sorry declarations in this delivery.
No split-off theorems or new modules were added. The main theorem uses the
already stated etale-local and finite-pushforward comparison theorems, whose
existing proofs are outside this delivery.

Validation: lcompile.py compiled the module in 28.3 seconds with no errors
or warnings. A source comparison confirms the main theorem signature is
unchanged, every Lean line is at most 100 characters, and no sorry tokens remain.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyOfFinitePresentation`
  and direct proof dependency `lem-trf-finite-morphism-finite-presentation`:
  Mathlib instances immediately supply quasi-compactness and
  quasi-separatedness of a finite morphism after local finite presentation
  has been established.
- `Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation` and direct proof
  dependency `lem-trf-finite-extension-module-finite-presentation`: the
  existing finite-pushforward theorem already includes the stalk comparison
  for both i and π. This ring-theoretic dependency remains needed by that
  theorem; no global withdrawal is claimed.

No Lean files or DAG attachments are withdrawn. No additional dependencies
of the chosen argument have been pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan's direct use of the
finite-extension comparison on stalk rings is unnecessary at this level,
because the declared singleton-fibre pushforward theorem already supplies
both the neighbourhood and stalk assertions. The canonical tensor-pullback
stalk isomorphism and the proved finite-presentation cancellation theorem
make the previously implicit glue explicit in the updated DAG.

Edge-case checks: the private flat-pullback comparison needs no
quasi-coherence or finite-type assumption, and works for the zero module.
The main singleton-fibre hypothesis for i follows from closed-immersion
injectivity, rather than an unjustified condition on a fibre ring. The
marked points already exclude empty pointed schemes. No arbitrary data is
chosen from a mere unproved existence assertion.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
