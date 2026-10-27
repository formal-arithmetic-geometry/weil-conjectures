## Worker report

The delivery restores the statement of `lem-per-excellent-normalization-preparation` in
`Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation`, declaration
`AlgebraicGeometry.excellent_normalization_preparation`. Its sole theorem has proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The node copy changes only `lean`; the prior `lean_removed` history is preserved.

I read the current node, all eight proof steps, all nine statement-dependency records,
and the definitions and docstrings they name. I checked Stacks `morphisms.tex`,
`lemma-nagata-normalization` (035S), `lemma-normalization-normal` (035Q), and
`lemma-birational-isomorphism-over-dense-open` (0BAJ), together with
`more-algebra.tex`, `lemma-quasi-excellent-nagata` (07QV) and
`lemma-finite-type-over-excellent` (07QU). The theorem docstring gives the node's eight
proof steps, including the empty case, finite module argument, lying over, normal stalks,
excellence and finite affine cover, component generic neighborhoods, clearing denominators,
and gluing the inverse maps.

Hypotheses and objects, matched to the node:

- A scheme X: `(X : Scheme.{u})`, with `universe u` explicitly declared.
- Reduced: `[IsReduced X]`.
- Noetherian in the stated convention: `[IsLocallyNoetherian X] [CompactSpace X]`.
- Excellent on every affine open: `(hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))`.
  The type `X.affineOpens` packages an open and its affineness, so this quantifies over
  exactly all affine opens, without choosing an affine cover or assuming affineness of X.
- The componentwise normalization is the recorded `X.reducedNormalization` with its
  canonical map `X.fromReducedNormalization`, not a freely chosen morphism.

Every conclusion clause, in order:

- Finite: `IsFinite X.fromReducedNormalization`.
- Surjective: `Surjective X.fromReducedNormalization`, the scheme-morphism class whose
  field is surjectivity of the underlying map.
- Noetherian source: `IsLocallyNoetherian X.reducedNormalization` and
  `CompactSpace X.reducedNormalization` as two conjuncts.
- Excellent source: `∀ V : X.reducedNormalization.affineOpens,
  IsExcellent Γ(X.reducedNormalization, V)`.
- Every local ring is an integrally closed domain: `∀ x : X.reducedNormalization,
  IsDomain (X.reducedNormalization.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.reducedNormalization.presheaf.stalk x)`.
  The stalk is the scheme local ring, and `IsIntegrallyClosed` is integral closure
  in its fraction ring; the accompanying `IsDomain` supplies exactly the domain clause.
- Open subscheme U: `∃ U : X.Opens`. Density: `Dense (U : Set X)`.
- All component generic points belong to U:
  `∀ Z ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η Z → η ∈ U`.
  This quantifies over every generic point, rather than a chosen representative.
- Isomorphism over U: `IsIso (X.fromReducedNormalization ∣_ U)`.
  Mathlib's `morphismRestrict` has source `(ν ⁻¹ᵁ U).toScheme` and target `U.toScheme`,
  so it is exactly the map in the node, with the inherited structure sheaves.
- The empty scheme is allowed: no nonempty, integral, irreducible, or separated hypothesis
  occurs. Its sole open U is empty, which is dense in the empty space, the generic-point
  condition is vacuous, and the restriction is the empty-scheme isomorphism.

Recorded dependency declarations used:

| Node | Module | Declaration or encoding |
| --- | --- | --- |
| def-pc-reduced-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsReduced |
| def-exc-excellent-ring | Sheaf.RingTheory.ExcellentRing | IsExcellent |
| def-weil-pbc-reduced-normalization | Sheaf.AlgebraicGeometry.ReducedNormalization | AlgebraicGeometry.Scheme.reducedNormalization; AlgebraicGeometry.Scheme.fromReducedNormalization |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite | AlgebraicGeometry.IsFinite |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed | IsDomain and IsIntegrallyClosed, the record's normal-domain conjunction |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion | AlgebraicGeometry.IsOpenImmersion; open subschemes and the canonical restriction via Mathlib.AlgebraicGeometry.Restrict |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-pbc-quasi-compact-scheme | Mathlib.Topology.Defs.Filter | CompactSpace |
| def-sc-generic-point | Mathlib.Topology.Sober | IsGenericPoint |

The statement imports these interfaces publicly. Already stated proof dependencies are
plain imports, including the affine-chart theorem, quasi-excellent implies Nagata,
finite-type/localization excellence, affine-cover excellence, the Nagata and Japanese-domain
definitions, and the Mathlib modules for lying over, integral closure/localization,
affine stalks/function fields, affine quasi-compactness, and Noetherian components.
There are no imports of downstream consumers and no private notation or instances.

Edge cases checked mathematically before writing: empty X and empty component family;
a field; a normal affine domain (identity normalization and U = X are possible);
the reduced crossing Spec k[x,y]/(xy) (the two normalized components are retained);
the cusp Spec k[t²,t³] (finite birational map with smaller isomorphism open);
and reducible schemes whose components intersect (generic neighborhoods need not cover X).
No characteristic or dimension condition has been introduced. No statement dispute found.

Searches run on 2026-10-24:

- `msearch.py ... leanfinder "The componentwise normalization of a reduced Noetherian
  excellent scheme is finite surjective excellent normal and an isomorphism on a dense open"`:
  eight hits, all Mathlib relative-normalization interfaces; none assert the theorem.
- `msearch.py ... loogle '"normalization", AlgebraicGeometry.IsFinite'`: zero hits.
- `msearch.py ... leansearch "Excellent scheme finite normalization isomorphism over dense
  open"`: eight hits about relative normalization; none gives excellence or this theorem.
- `msearch.py ... grep 'excellent_normalization_preparation|fromReducedNormalization|IsExcellent'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg -n 'excellent_normalization_preparation|lem-per-excellent-normalization-preparation|
  fromReducedNormalization|reducedNormalization' lean/WeilConjectures`: no hits.
- `rg` for the item id and the proposed declaration in `lean/Sheaf`: no hits. Further `rg`
  for normalization and excellence found consumers and componentwise normalization results,
  but no theorem with the full conclusion. The existing componentwise construction is used.
- The node's historical `lean_removed` record names this former module; I verified that the
  declaration is absent from the current library instead of treating that record as a binding.

Validation: the prescribed `scompile.py NB lem-per-excellent-normalization-preparation`
compiled the sandbox and library module successfully (1.6 s and 1.5 s respectively).
Final validation after explicitly adding the public dependency imports is recorded below.

## Second reading by NB

I performed a separate second pass with the node and final Lean file open. This is the
assigned worker's second pass; no additional agent was started, in accordance with the
dispatcher's instruction. The maintainer supplies the independent delivery review.

I checked all hypotheses and all seven conclusion groups against the table above:
reduced; locally Noetherian plus quasi-compact; all-affine excellence; the exact componentwise
normalization; finite and surjective; locally Noetherian and quasi-compact source;
all-affine excellence of the source; domain and integrally closed at every stalk;
and a dense open containing every component generic point with the canonical restricted
map an isomorphism. None is omitted or replaced by an assumption about another scheme.
In particular, `IsIso` concerns the actual map, not mere existence of an isomorphism.
The domain conjunct is present, and the open quantifier does not require nonemptiness.
No mathematical mismatch was found. I added direct public imports of Properties and
Topology.Defs.Filter so the recorded reducedness and quasi-compactness interfaces are
explicit. No node statement, proof, or dependency list changed.

Final import-complete `scompile.py` validation: exit 0, sandbox compile 2.1 s,
library module compile 3.5 s, with no errors or non-sorry warnings.
Source comparison confirms that `lean` is the only changed field of the node.
