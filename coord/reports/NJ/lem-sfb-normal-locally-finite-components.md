## Worker report

The module `Sheaf.AlgebraicGeometry.NormalLocallyFiniteComponents` states
`AlgebraicGeometry.Scheme.normal_locally_finite_components`. Its only theorem has
proof `sorry`; there are no new definitions, dependency repairs, or statement corrections.
The node is unchanged outside `lean`.

Source checked: `literature/stacks-project/properties.tex`,
`lemma-normal-locally-finite-nr-irreducibles` (Tag 0357), implication (1) to (2)
and the final paragraph. The reduced closed structure uses Schemes Tags 01J3/01J4
and the recorded reduced-induced-closed-subscheme theorem. The declaration docstring
contains all eight steps of the DAG proof, including the empty-product affine case,
component restriction and closure, and the inverse constructed by disjoint open gluing.

Hypothesis and conclusion correspondence:

- An arbitrary scheme is `(X : Scheme.{u})`, with `u` explicitly declared. There is
  no Noetherian or global compactness hypothesis.
- Every quasi-compact open has finitely many irreducible components is
  `hfinite : ∀ U : X.Opens, CompactSpace U → (irreducibleComponents U).Finite`.
  Here `U` as a type has its subspace topology, so `CompactSpace U` is exactly
  quasi-compactness of that open, without separation; components are those of U.
- Every ambient local ring is an integrally closed domain is
  `hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)`.
- The indexing set is exactly `irreducibleComponents X`. The witness
  `U : irreducibleComponents X → X.Opens` has
  `(∀ i, (U i : Set X) = i.val)`, so it cannot select a different decomposition
  or repeat components. This equality identifies each open subscheme with its
  specified actual irreducible component.
- Openness and closedness are `(∀ i, IsClopen (U i : Set X))`; pairwise
  disjointness is `Pairwise (fun i j ↦ Disjoint (U i) (U j))`;
  covering X is `(⨆ i, U i) = ⊤`.
- The induced open scheme structure is Mathlib's `(U i).toScheme`, with
  inclusion `(U i).ι`. Each is integral by `IsIntegral (U i).toScheme`, and
  its local rings satisfy the displayed `IsDomain` and `IsIntegrallyClosed`
  conjunction for every `x : (U i).toScheme`.
- Agreement with the reduced induced closed structure is an isomorphism `e`
  from `(U i).toScheme` to
  `(IdealSheafData.vanishingIdeal ⟨i.val, isClosed_of_mem_irreducibleComponents
  i.val i.property⟩).subscheme`, satisfying
  `e.hom ≫ ...subschemeι = (U i).ι`. This is equality of the structures as
  subschemes over X, not merely an abstract isomorphism. The target is the
  canonical reduced induced closed construction from the dependency. Its
  inclusion is a closed immersion; the isomorphism also makes the open
  component inclusion a closed immersion. Uniqueness over X is automatic
  since the reduced closed inclusion is a monomorphism.
- The canonical coproduct-to-X map is exactly
  `Sigma.desc (fun i ↦ (U i).ι)`, with the actual component inclusions as its
  summand restrictions. `IsIso` asserts the requested isomorphism. A different
  coproduct object gives the same assertion by the unique coproduct isomorphism.
- Infinite I is allowed: the index is a set in the same universe as X and has
  no finiteness constraint. When X is empty, no subset is nonempty irreducible,
  so `irreducibleComponents X` is empty; thus the statement specializes to the
  empty coproduct and the empty open cover without requiring a chosen component.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff condition).
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, defined by maximal
  nonempty irreducible subsets, and `isClosed_of_mem_irreducibleComponents`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  normal domains use this together with Mathlib's `IsDomain`, exactly as the
  normal-ring node prescribes for domain stalks.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` and `IsReduced` (the
  latter follows for each integral open component and the canonical closed structure).
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme` and `Scheme.Opens.ι`.
- `Mathlib.AlgebraicGeometry.Limits`: the small discrete coproduct instance,
  `sigmaOpenCover`, and `disjoint_opensRange_sigmaι`; the map uses the recorded
  categorical coproduct interface `CategoryTheory.Limits.Sigma.desc`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  with Mathlib's `vanishingIdeal`, `subscheme`, and `subschemeι` constructions.
  Its signature and docstring were read in full; clause (3) supplies precisely
  the uniqueness of the reduced structure over X. The upstream module in its
  current record is imported; no retired Sheaf duplicate is imported.

Proof-only imports include the recorded
`WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`
(the complete signature/docstring read), plus Mathlib's affine-open/quasi-separated,
prime-spectrum topology, irreducible-closed correspondence, and scheme-gluing APIs.
All recorded statement dependencies are usable without repairs. The other Mathlib
proof dependencies are supplied by these modules and their imports.

Edge checks: the empty scheme (empty I, empty coproduct), empty quasi-compact opens,
a single normal integral component, and an infinite disjoint union of normal integral
schemes. A quasi-compact open in the latter meets only finitely many open components,
while X and I can remain infinite. No positive-characteristic or dimension restriction
appears. A union with intersecting distinct components fails the domain-stalk condition;
normal non-Noetherian integral schemes remain included. Indexing by subsets of X stays
in universe u, so the existing scheme-coproduct instance applies without a size hypothesis.

Searches made through the prescribed `msearch.py NJ <item>` wrapper:

- LeanFinder: “A scheme with integrally closed domain stalks and finitely many
  irreducible components on each quasi compact open is the coproduct of its clopen
  normal integral irreducible components”. Eight hits, including binary relative
  `Scheme.Hom.normalizationCoprodIso` and `IsIntegral`; no matching decomposition.
- Loogle: `"irreducibleComponents", "IsIntegrallyClosed"`. Zero hits.
- Mathlib grep: `irreducibleComponents|IsIntegrallyClosed` in `AlgebraicGeometry`.
  Twenty-five displayed hits: noetherian finiteness, generic-point stalks,
  geometrically irreducible maps, and ideal-sheaf components; none is the statement.
- LeanSearch: “A normal scheme with locally finitely many irreducible components
  is a coproduct of clopen normal integral schemes”. Eight hits on general coproduct
  existence/disjointness and Noetherian component finiteness, none the assertion.
- Project rg: `normal-locally-finite-components|normal.*components|components.*normal`
  in both `lean/WeilConjectures` and `lean/Sheaf`; and the exact expected declaration
  names `normal_locally_finite_components|normalLocallyFiniteComponents` in Mathlib,
  upstream, and Sheaf. Exact declaration search had no matches. Related upstream
  `Scheme.exists_isClopen_isIntegral_of_isIntegrallyClosed_stalk` in
  `NoetherianComponents.lean` requires Noetherianity and returns a finite indexed
  family: it is not the arbitrary locally finite theorem here. Other hits only cite
  Tag 0357 or the item, or prove stronger-hypothesis special cases.
- Exact blueprint-id grep in `lean/WeilConjectures` found no existing declaration
  for this item. No new notion or definition node is needed.

Validation: `scompile.py NJ lem-sfb-normal-locally-finite-components` compiled both
its sandbox and final module paths successfully, with no errors or unexpected warnings.
`set_option autoImplicit false` enforces explicit variable binding. The declaration
is the only postponed proof. No disputed statement or node fault was found.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
