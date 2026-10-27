## What changed

Proved the three theorems of `Sheaf.AlgebraicGeometry.ProperHenselianDerivedRestriction`.
All public signatures and the three existing constructions are unchanged.

The main proof applies the bounded-below heart test twice: first to restriction on Y,
then to affine henselian restriction on the derived direct image of a torsion sheaf in
degree zero. Only higher images of such sheaves need torsion preservation. Gabber,
the Ext/derived-global comparison and proper base change supply the isomorphisms.
Private proved helpers verify the exact derived square compositor, restriction
composition, and the unit/Leray/counit identity that identifies the resulting arrow
with the published canonical restriction. Naturality is naturality of its defining
right-derived descent. The pairs identity follows from composition and coefficient
naturality, without geometric restrictions on the intervening map.

Updated the node's proof, proof dependencies and proof origin to match this route.
No other module is changed and no definition or statement repair is involved.
The two derived/classical comparison imports are private. Proper base change publicly
exports the adjunction coherence and cohomology-map isomorphism invariance APIs;
redundant direct imports of those modules were removed.

## Proved and sorry left

Closed all three original holes, each attached to
`lem-per-proper-henselian-derived-restriction`:

- `AlgebraicGeometry.Etale.proper_henselian_derived_restriction`.
- `AlgebraicGeometry.Etale.proper_henselian_derived_restriction_naturality`.
- `AlgebraicGeometry.Etale.proper_henselian_derived_restriction_pairs`.

No holes added or split off. No `sorry` remains in the delivery. Every private helper
is proved. Validation: the final single-file compile completed without warnings or
errors (56.7 seconds). All three original definitions, public theorem signatures and
public imports were compared byte-for-byte with the source and are unchanged.
The required delivery command runs the final server compile and preflight.

## No longer needed

Removed direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`.
- `Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows`.
- `Sheaf.CategoryTheory.Sites.DerivedSectionsUnitPasting`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
- `WeilConjectures.SixFunctors.Etale.Gabber`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `WeilConjectures.SixFunctors.BaseChange.Derived`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`.

The proof no longer needs the general truncation hypercohomology spectral sequence:
the outer heart reduction makes torsion preservation for a general derived complex
unnecessary. It also does not need the generic module-site unit-pasting interface:
the bounded-below etale adjunction and derived composition APIs prove the exact
composition and mate identities directly. Standard proper-morphism instances supply
qcqs, so the separate affine-scheme argument is unnecessary. No upstream declaration
is removed or replaced, and no claim of pruning a still-used transitive import is made.

Removed node proof dependencies:

- `def-weil-finite-type-morphism`.
- `def-weil-quasi-separated-morphism`.
- `def-weil-closed-immersion`.
- `lem-weil-pbc-affine-scheme-qcqs`.
- `lem-weil-pbc-abelian-etale-sheaves-grothendieck`.
- `thm-sp-truncation-e2`.
- `prop-weil-pbc-geometric-stalks-exact`.
- `lem-pur-site-derived-sections-unit-pasting`.
- `lem-weil-pbc-derived-direct-image-triangulated`.
- `lem-weil-pbc-cohomology-pullback-functorial`.

Removed the matching obsolete top-level tool approvals; retained entries keep their
original order. Other nodes' uses of these modules are unaffected.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned general spectral-sequence torsion argument
was stronger than necessary. The two existing heart tests give a shorter route using
only the torsion theorem for higher direct images of sheaves. The unit-pasting node is
not necessary for these etale canonical maps because the concrete bounded-below
adjunction, composition and localization APIs already provide the required equations.
The unit route is unchanged.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
