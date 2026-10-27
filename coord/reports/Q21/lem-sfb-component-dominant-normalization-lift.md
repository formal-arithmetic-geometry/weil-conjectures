## Worker report

The new module `Sheaf.AlgebraicGeometry.ComponentDominantNormalizationLift` states
`AlgebraicGeometry.Scheme.existsUnique_lift_reducedNormalization_of_component_dominant`.
Its sole proof is `sorry`; it introduces no definitions. The node is unchanged except for
its `lean` attachment. Read the complete node, all statement dependencies and their recorded
interfaces, and Stacks `morphisms.tex`, lemma-normalization-normal (Tag 035Q), including its
proof of (4), and lemma-normalization-in-terms-of-components (Tag 0CDV).

Hypothesis and conclusion correspondence:

- `X` and `Y` are arbitrary `Scheme.{u}` and `g : Y ⟶ X` is an arbitrary morphism.
- Every quasi-compact open of X has finitely many irreducible components:
  `hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite`.
  Here `U` denotes the open subspace, so these are its own irreducible components.
  `IsCompact` is topological quasi-compactness and does not assume Hausdorffness.
- Every local ring of Y is an integrally closed domain:
  `hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
  IsIntegrallyClosed (Y.presheaf.stalk y)`. These are the actual structure-sheaf stalks,
  not the ring of global functions and not an integrally closed ring without the domain clause.
- Every source component dominates a target component:
  `hdominant : ∀ (C : Set Y), C ∈ irreducibleComponents Y →
  ∃ (D : Set X), D ∈ irreducibleComponents X ∧ closure (g '' C) = D`.
  This is the stated closure-of-image equality in X, with every C and some D. It permits
  multiple source components over a single target component and does not require hitting all
  target components.
- The normalization object is exactly the recorded `X.reducedNormalization`, the coproduct
  of function-field normalizations of the reduced induced component schemes. The canonical
  map is exactly `X.fromReducedNormalization`.
- Existence and uniqueness are `∃! h : Y ⟶ X.reducedNormalization,
  h ≫ X.fromReducedNormalization = g`; the composition has the same order as ν_X ∘ h = g.
- No integral, birational, component-bijection, generic-field-isomorphism, quasi-compact,
  Noetherian, reduced-target, or nonempty-source hypothesis is introduced.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (locally affine locally ringed spaces and their actual morphisms).
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, defined as maximal
  `IsIrreducible` subsets; its domain is the underlying space, including the open subspaces.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, the
  recorded fraction-ring integrally closed predicate, together with `IsDomain`.
  The dependency explicitly records this inline conjunction for a normal domain.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization` and
  `Scheme.fromReducedNormalization`; also read `reducedNormalizationComponent` and its
  integrality theorem. No duplicate normalization or new normality predicate is defined.

Proof dependencies with usable recorded modules are imported privately, including Mathlib's
scheme properties, reduction subscheme, closed immersion and proper-monomorphism criterion,
affine stalks, spectrum component/minimal-prime correspondence, localization and integral
closure, and gluing. The recorded upstream closed-immersion factorization and
`integral_totalFraction_mem_range_of_normal` are imported from their upstream modules.
`lem-sfb-normalization-affine-total-fractions` has no Lean declaration or Mathlib match on
this base and is needed only for the future proof, so there is no module to import yet.
It is retained in the node's proof plan and the seven-step declaration docstring.

Edge cases checked against the literal statement and Stacks:

- Empty Y: both universal hypotheses on its points/components are vacuous, and the conclusion
  asks for the unique morphism from the empty scheme. There is no nonemptiness binder.
- Empty X: a morphism g then forces an empty source; the empty coproduct normalization is
  already provided by the recorded definition. The empty open has zero components.
- A single branch of Spec(k[x,y]/(xy)) is allowed to dominate its one target component;
  dominance is not accidentally made surjective on components.
- A point mapped to the crossing of the two branches fails the component-dominance
  hypothesis, as required to exclude its two lifts.
- A nonreduced target such as Spec(k[ε]/(ε²)) is allowed: no reducedness was added.
- A disjoint union with arbitrarily many normal source components, and a non-Noetherian
  normal source such as the spectrum of a polynomial ring in infinitely many variables,
  are not excluded by any size, compactness or Noetherian assumption.

Searches actually run (2026-10-24):

- `msearch.py`, LeanFinder query: “A normal scheme mapping each irreducible component
  dominantly onto a component factors uniquely through the componentwise normalization”.
  Eight hits, headed by `Scheme.Hom.normalizationDesc`, `toNormalization`, and
  `normalization.hom_ext`. These concern the relative normalization of a supplied qcqs
  morphism. Read its declaration/docstring in Mathlib `AlgebraicGeometry/Normalization.lean`;
  its universal property is different, so none is an exact match.
- `msearch.py`, Loogle query: `"normalization", "Desc"`. Eight hits on the same relative
  normalization family, including `normalizationDesc_comp`; none gives this theorem.
- `msearch.py`, grep query: `normalizationDesc|fromReducedNormalization|reducedNormalization`
  in `AlgebraicGeometry`. Five hits in Mathlib's relative normalization module; no match.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for normalization lifts,
  `fromReducedNormalization`, component dominance, and finite irreducible components.
  The upstream normalization module deals with integral/relative normalization. The project's
  `ComponentwiseNormalizationProperties` uses locally Noetherian targets and its recognition
  clause requires an integral source morphism and generic bijection; `NormalizedBlowupCalculus`
  has only a private characteristic-zero finite-type specialization. Neither is this theorem.
  Other hits are downstream uses or proof docstrings. The exact new declaration name has no
  hit in Mathlib, upstream, Sheaf, or `dag/lean_names_upstream.json`.
- Direct search for the item id in `lean/WeilConjectures`: no hits.

No statement correction, missing statement notion, dependency repair, or disputed assertion.
The module's docstring includes the node's complete seven-step proof route, with the affine
fraction-map and denominator-cancellation uniqueness argument made explicit.

Validation: `scompile.py Q21 lem-sfb-component-dominant-normalization-lift` compiled the
file both as a sandbox module and under its library module name, in 2.0 and 2.2 seconds,
respectively, with no reported errors or unexpected warnings. All universe and object
variables are explicitly bound. All lines are at most 100 characters.

## Second reading by Q21

Author self-check, not an independent review: reread the node and the completed signature.
The target finiteness condition quantifies over all compact opens, not only affine opens or
X itself. Normality requires both domain and integral-closure predicates at every stalk.
The dominance binder is over irreducible subsets maximal in the entire source, and the
closure is taken in X. The conclusion uses the recorded coproduct normalization and its
canonical map, with `∃!` over morphisms. No forbidden extra assumptions or excluded empty
case were found. No change to the natural-language statement was necessary. The independent
mathematical review is the maintainer's review after direct delivery.
