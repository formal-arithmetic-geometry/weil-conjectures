## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition` states
`AlgebraicGeometry.IsHProjective.comp`, with its sole proof `by sorry`.
It introduces no definition. Only the item's `lean` field is changed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Arbitrary schemes X, Y, S are `{X Y S : Scheme.{u}}`, with `universe u` explicitly bound.
- The morphisms g:X→Y and h:Y→S are `(g : X ⟶ Y) (h : Y ⟶ S)`.
- H-projectivity of g is `[IsHProjective g]`; H-projectivity of h is `[IsHProjective h]`.
  These use exactly the declaration recorded by `def-kun-projective`, rather than a
  projectivity predicate with a different meaning.
- The composite h∘g is `g ≫ h`, with the same source X and target S.
- The conclusion that it is H-projective is `IsHProjective (g ≫ h)`.
  There are no other assumptions or conclusions.

Dependency declarations read and used:

- Statement dependency `def-kun-projective`: `AlgebraicGeometry.IsHProjective`, in
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, publicly imported.
  Read the current published source using `scompile.py --source`, including its
  docstring and full class: a finite homogeneous coordinate type and a closed immersion
  whose composite with the structural projection equals the given morphism.
  This is the repaired canonical interface already recorded by the dependency.
- Proof dependency `lemma-nagata-projective-space-base-change-pullback`:
  `AlgebraicGeometry.ProjectiveSpace.isPullback_map`, in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`; read its full signature/docstring.
  It gives the cartesian square for any coordinate type and any base morphism.
- Proof dependencies `lem-weil-pbc-closed-immersion-base-change` and
  `lem-weil-pbc-closed-immersion-comp`: the recorded Mathlib declarations
  `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange` and
  `AlgebraicGeometry.IsClosedImmersion.comp`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; full declarations read.
- Proof dependency `lem-chow-segre`: read its main-20261015 blueprint_update and the
  recorded `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_pi` and
  `AlgebraicGeometry.ProjectiveSpace.isProper_pi_hom`, in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product`, plus its recorded binary
  `AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_segre`, in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre`.
  Both recorded modules are proof imports; the binary case supplies the final arrow.

The theorem docstring reproduces all four DAG proof steps: choose the embeddings;
base-change the second closed immersion; identify the iterated projective space with
its fibre product and compose closed immersions; finally use the Segre embedding.
The local Stacks source `morphisms.tex`, lemma-H-projective-composition (Tag 01WE),
was read with its entire proof diagram. It agrees exactly with the node and signature.

Edge cases checked mathematically before writing:

- No nonemptiness, field, Noetherian, separated-base, or characteristic hypothesis
  occurs. All base schemes allowed by the source remain covered.
- Projective dimension zero in either embedding uses one homogeneous coordinate;
  the Segre dimension N*M+N+M still gives the required nonnegative dimension.
- Empty source, intermediate scheme, or base is not excluded. The finite-coordinate
  predicate permits an empty coordinate type, whose projective space is empty. A
  source with a closed immersion there is empty and also embeds into P^0, so this
  canonical encoding does not change the finite-dimensional convention of the node.
- The universe u is arbitrary and is the standard universe of schemes and coordinate
  types in the recorded dependency, without additional size assumptions.

Searches for an existing statement:

- `msearch.py ... leanfinder "The composite of two H-projective morphisms of schemes is
  H-projective"`: eight hits, about composition of proper, finite, universally closed,
  or universally open morphisms; none states this projectivity assertion.
- `msearch.py ... loogle "AlgebraicGeometry.IsHProjective,
  AlgebraicGeometry.IsHProjective.comp"`: zero hits, unknown IsHProjective in Mathlib.
- `msearch.py ... grep "IsHProjective|H.projective.composition" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for IsHProjective,
  HProjective, H-projective, and composition-name variants found uses of the canonical
  class, base-change and properness statements, but no composition statement.
  The upstream-name index also has no `IsHProjective.comp`.
- `grep -rn "lem-trf-h-projective-composition"` over upstream `WeilConjectures`:
  no declaration tagged with this node.
- Reading the current published Projective module confirms it has the class,
  projectivity/properness interfaces, and no composition theorem.

The previous worker's unchanged-delivery failure confused the existing NG/L stage-1
split with a stage-2 statement: the shared node has a reviewed proof plan but no `lean`
record. This delivery supplies that missing record and its new module.

No statement correction, dependency repair, new node, or disputed statement is needed.
No independent worker review is claimed; the maintainer performs the independent review
under the direct-delivery instructions. Compilation and delivery preflight use only the
prescribed wrappers.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
