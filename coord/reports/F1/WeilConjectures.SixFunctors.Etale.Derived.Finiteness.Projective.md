## What changed

Proved both open theorems in
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective` without changing any
existing signature, definition, public import, universe, or visibility.

`hasConstructibleDirectImages_projectiveLine` reuses the existing declaration
`isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine` from
`Sheaf.AlgebraicGeometry.ProjectiveLineConstructible`. The proof obtains an actual
annihilating exponent from `HasInvertibleExponent`, supplies the finite-type structure-map
instances, converts constructibility with `Scheme.isConstructibleEtaleModuleSheaf_iff`,
and transports homology along `Functor.rightDerivedFunctorPlusCompatibility`.
This is reuse of an already stated theorem, not a new renamed obligation.

`HasConstructibleDirectImages.of_projectiveLine` implements the existing tower / symmetric
product / finite-surjection cancellation argument. Induction proves properness and C for
`ProjectiveSpace.projectiveLinePowProj`. The existing source theorem
`ProjectiveSpace.exists_isFinite_surjective_projectiveLinePow` supplies a finite surjective
map over S, including projective dimension zero. Cancellation and composition use the
already proved source declarations in `FiniteCancellation` and `ConstructibleDirectImage`.
A proved private helper handles closed immersions by their exact constructible-preserving
direct image. It also handles the identity and empty-coordinate projective space.

Four proof-only imports were added: ProjectiveLineConstructible,
ConstructibleEtaleModuleSheafComparison, ProjectiveSpace.SymmetricProduct, and
ConstructibleSheaf.ExtensionByZero. Import-direction checks permit each import.
The copied reduction node's proof and dependency list now describe these constructions;
its existing Lean attachment and statement are unchanged. The project's unit record has
no realized statement or steps for this unit, and the mathematical reduction is retained.

Search: launcher leanfinder query for constructible projective-line direct images;
launcher loogle query `"constructible", "Sheaf"` (zero hits); launcher grep query
`HasConstructibleDirectImages|projectiveLinePow`; direct rg searches found the exact
projective-line statement, the proved comparison, and the proved source symmetric cover.
The Lean server compiled the complete module. Delivery preflight checks compilation and
axioms again. No data is chosen from an unproved existence statement in this delivery.

## Proved and sorry left

Original holes: 2. Holes closed: 2. Holes added: 0. Split-offs: 0.

- `AlgebraicGeometry.Etale.hasConstructibleDirectImages_projectiveLine` is proved from
  the existing named projective-line theorem and proved comparison APIs.
- `AlgebraicGeometry.Etale.HasConstructibleDirectImages.of_projectiveLine` is proved
  by tower induction, the existing symmetric cover, cancellation, and composition.
- The private `constructibleDirectImages_closedImmersion` helper is completely proved.
- No `sorry` remains anywhere in the delivered Lean module. No new Lean module is added.

The imported existing theorem
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine`
(node `thm-fin-projective-line-constructible`) remains an existing dependency with `sorry`;
this delivery proves the source-library wrapper from it and does not claim to prove that
underlying geometric theorem. No dependency theorem or node is duplicated or reattached.

## No longer needed

No original public or proof import was removed from the item. The experimental proof
import `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible` was
removed: the private helper uses the proved closed-immersion API directly rather than
finite-pushforward constructibility for arbitrary finite maps.

The reduction node no longer needs `lem-fin-symmetric-product-finite` or its module
`Sheaf.AlgebraicGeometry.NoetherianSymmetricProductFiniteSurjective`: the proved
source-library symmetric cover already gives precisely the finite surjective morphism
and its compatibility with the projection, for every finite nonempty coordinate type.
It also no longer needs `def-nagata-relative-projective-space` and `def-pc-fibre-product`
as proof dependencies: no chart computation or conversion of products in Over S is needed.
These are local dependency removals; no claim is made that the modules become globally
unreachable from all targets.

The modules `Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine`,
`Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp`, and
`Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation` are not imported:
the existing source C-predicate APIs prove the same steps directly and avoid coefficient
hypotheses absent from the source reduction theorem. The projective-line module's own
geometric proof dependencies remain needed by its existing unresolved theorem.

## Where the brief, the DAG or earlier work was wrong

The module's two blueprint labels have primary Lean records on equivalent Sheaf modules,
not on the assigned source-library declarations; searching only exact `lean.module`
attachments finds no assigned node. Its docstrings identify the relevant nodes.

The recorded Sheaf projective-from-line theorem fixes a positive invertible annihilator.
The assigned source theorem has no such hypothesis, so applying that recorded theorem
would silently strengthen its hypotheses. The source composition and cancellation APIs
already support the required finite-ring generality, and the supplied universal
projective-line hypothesis proves the tower argument with its exact original signature.

The empty-coordinate case is present in the assigned signature although the prose speaks
of projective spaces of nonnegative dimension. It is proved using empty projective space,
without adding a nonempty-index assumption. The proof also covers empty S and a
one-element coordinate type without imposing a nonempty-scheme hypothesis.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
