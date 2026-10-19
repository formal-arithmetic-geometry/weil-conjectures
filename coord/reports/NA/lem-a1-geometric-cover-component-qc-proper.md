## Worker report

The delivery adds the statement `AlgebraicGeometry.geometricCoverComponentQcProper` in
`Sheaf.AlgebraicGeometry.GeometricCoverComponentQcProper`. Its sole proof is `sorry`.
There are no definitions, helper theorems, new nodes, dependency replacements, or statement
corrections. The node copy changes only `lean`. Its signature is copied verbatim from the file,
with UTC date 2026-10-18 and branch `newtargets-dag`.

The existing NB merge and `reviewed` record concern stage 1 (the split); the assigned node has
neither `lean` nor `reviewed_lean`. They therefore do not duplicate this stage-2 statement.
The complete standing brief, stage document, delivery-errors H, worker role, setup, goal,
state, tools README, example CompactObject module/node, assigned node, and every statement
dependency and its recorded declaration were read. No repair note exists for this item.

The source is Bhatt--Scholze, *The pro-étale topology for schemes*, the proof of Lemma 7.4.10,
printed p. 71, read from the local PDF with `pdftotext -f 71 -l 73 -layout`. It proves the
quasi-compactness of connected geometric covers over a quasi-compact base, then their
properness and finite étaleness. The node asks for just the quasi-compactness/properness and
finite-fibre intermediate statement. Its stronger normality assumption is retained verbatim.
The module docstring gives all twelve proof steps, including the canonical-normalization
comparison repaired in the stage-1 review; no part of this proof is formalized at stage 2.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes X and Z, morphism q: Z → X | `{X Z : Scheme.{u}}`, `(q : Z ⟶ X)` |
| Connected X, including nonemptiness | `[ConnectedSpace X]`; its `toNonempty` field excludes the empty space |
| Quasi-compact X, with no Hausdorff assumption | `[CompactSpace X]` |
| Locally Noetherian X | `[IsLocallyNoetherian X]` |
| Every local ring is an integrally closed domain | `hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)` |
| q is étale | `[Etale q]` |
| For every valuation ring R with fraction field K, every compatible a and b have a unique lift | `hval : ValuativeCriterion q` |
| C is an open connected component, a maximal nonempty connected subset | `(C : Z.Opens)` and `hC : ∃ z : Z, (C : Set Z) = connectedComponent z` |
| Induced open subscheme and restricted map | `C.toScheme`, implicit in the domain of `C.ι`, and `C.ι ≫ q` |
| Restricted map is quasi-compact | `QuasiCompact (C.ι ≫ q)` |
| Restricted map is proper | `IsProper (C.ι ≫ q)` |
| For every x, q⁻¹({x}) ∩ C is finite | `Scheme.Hom.HasFiniteFibres (C.ι ≫ q)` |

The last line uses exactly the dependency's finite-fibres predicate: for every `x : X`, the
preimage of `{x}` in `C.toScheme` is finite. The inclusion `C.ι` is subtype inclusion
(`Scheme.Opens.ι_apply`), hence identifies this set bijectively with `q ⁻¹' {x} ∩ (C : Set Z)`.
This neither weakens nor strengthens the requested assertion.

The component hypothesis is likewise exact. `connectedComponent z` is Mathlib's maximal
connected subset containing z. It contains z and is connected by
`isConnected_connectedComponent`; every maximal nonempty connected set equals such a
component by choosing any of its points. The existential does not add a chosen basepoint
or exclude any component. Membership in `Z.Opens` supplies precisely the openness already
assumed by the node. No closedness, irreducibility, or compactness of C is assumed.

`ValuativeCommSq q` has fields `R : Type u`, `CommRing R`, `IsDomain R`, `ValuationRing R`,
`K : Type u`, `Field K`, `Algebra R K`, `IsFractionRing R K`, the top map a and bottom map b,
and their commutative square. `ValuativeCriterion q` quantifies over every such square and
asserts `Nonempty (Unique sq.LiftStruct)`. The lift structure supplies the actual scheme
morphism and both triangle equalities, so the lift is over X and restricts to a. Its
uniqueness is uniqueness of that morphism (triangle witnesses are propositions). This uses
the standard Mathlib valuative criterion already used by the recorded parent theorem
`normalGeometricCoverComponents`; no new geometric-cover predicate is introduced.

All universes and object variables are explicitly bound. `universe u` and `Scheme.{u}`
use the usual Mathlib scheme category and its `ValuativeCommSq` test rings at that same
universe. No independent test-ring universe below the scheme universe is quantified over,
and no additional universe equality is imposed. There is no hidden `let` or `show` in the
statement.

Dependency declarations used (the recorded source signatures/docstrings were opened):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and its
  `Hom`; open restriction uses the same scheme's `Scheme.Opens.toScheme` and `.ι` from
  `Mathlib.AlgebraicGeometry.Restrict`.
- `def-weil-connected-scheme`: `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`;
  the same module's `connectedComponent` and maximality/connectedness lemmas encode C.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (all affine rings Noetherian, equivalent to the
  node's affine-cover definition).
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, paired with `IsDomain` on the stalk, exactly the recorded inline form
  for a normal domain; the general normal-ring localization condition is not substituted
  for the requested local-domain assumption.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-trf-valuation-ring`: `Mathlib.RingTheory.Valuation.ValuationRing`, `ValuationRing`
  and its `TFAE` (fraction-field characterization), used inside `ValuativeCommSq` from
  `Mathlib.AlgebraicGeometry.ValuativeCriterion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  and its imported `AlgebraicGeometry.QuasiCompact`; only the quasi-compact clause is a
  requested conclusion here, so no separate finite-type conclusion is added.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; universal closedness supplies quasi-compactness, so the
  class's local finite type is equivalent to the node's finite type in this conjunction.
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.HasFiniteFibres`. Its source was additionally confirmed with
  `scompile.py --source Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` against current sources.

The statement-dependency modules are public imports. The modules of stated proof dependencies
are ordinary imports, including `WeilConjectures.Compactification.ValuativeCriterion` for the
closed upstream dense-source criterion (whose audit has no separate `lean` record),
`WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`,
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`, the existing étale-normal-ring
and unramified modules, and Mathlib's function-field, normalization, Zariski Main, affine-Hom,
finite-integral-closure and Noetherian tools. Duplicate module paths already needed publicly
are imported once. The only proof dependency without a declaration is
`lem-a1-normal-etale-components-clopen`, so it has no import yet; it is not a prerequisite
for stating this theorem and no theorem about it is invented. No import cycle was identified.

Edge cases checked before writing:

- Empty X is already excluded by connectedness, as the node requires. Empty Z is allowed:
  there is then no nonempty connected component, so no `(C, hC)` and no spurious conclusion.
- Empty C is excluded by `hC` because `connectedComponent z` contains z. An arbitrary
  connected open subset is insufficient: maximality is retained by equality with a component.
- Infinitely many disjoint copies of X are allowed for Z; only each component's restriction
  is concluded quasi-compact. Neither compactness of Z nor finiteness of its component set
  is assumed or asserted.
- Over a field, a nonempty connected étale component is a finite separable point. The
  identity cover is included. There is no characteristic restriction.
- A proper open subset of an integral base can fail valuative existence; doubled-origin
  covers can fail uniqueness. The complete `ValuativeCriterion` assumption retains both,
  rather than using just separatedness or existence to infer the conclusion.
- The finite-fibres conclusion concerns sets of points; it makes no unsupported assertion
  about lengths, constant fibre degree, or a uniform finite bound.

Searches for an existing statement (all commands used the prescribed msearch wrapper):

1. LeanFinder: `An open connected component of an etale geometric covering of a connected
   quasi compact locally Noetherian normal scheme is quasi compact proper and has finite
   fibres`. Eight hits: quasi-compact-cover notions, normalization open covers/maps,
   `IsFinite`, `LocallyQuasiFinite`, finite fibres of an already finite map, and
   `quasiCompact_of_noetherianSpace_source`. None establishes compactness of the component
   from the given assumptions; no exact match.
2. Loogle: `"ValuativeCriterion", "IsProper"`. Two hits:
   `AlgebraicGeometry.IsProper.of_valuativeCriterion` and `.eq_valuativeCriterion`.
   Both require the missing quasi-compactness as input; neither states this node.
3. Mathlib grep, AlgebraicGeometry:
   `geometric.?cover|connected.*[Ee]tale.*[Qq]uasi[Cc]ompact`. Zero hits.
4. LeanSearch: `A connected component of an etale geometric covering of a connected normal
   Noetherian scheme is quasi compact and proper`. Eight hits concerning quasi-compact
   covers, already Noetherian sources, open immersions, universal closedness and compactness
   of Noetherian schemes. None supplies the component conclusion for this étale map.
5. `rg -n` on the read-only upstream `WeilConjectures` and the side project's `lean/Sheaf`
   for `geometric.?[Cc]over`: no upstream exact theorem; side hits include the parent
   `normalGeometricCoverComponents`, a stronger coproduct/classification statement with
   additional finite-étale and surjectivity conclusions, and unrelated geometric-cover
   model/descent modules. The parent's docstring explicitly assigns this node as an input;
   importing it to restate this input would introduce a proof-dependency cycle.
6. Exact item-id search in upstream `WeilConjectures`: no hits. Name searches for
   `geometricCoverComponentQcProper|geometricCoverComponent|geometric_cover_component` in
   upstream declarations, `dag/lean_names_upstream.json`, and `lean/Sheaf`: no collision.
   The wrapper retains the four service search outputs in this sandbox's `searches.jsonl`.

No statement dispute or node fault was found. No hypothesis, conclusion, source field,
statement dependency, or proof step of the node is changed. The prior retry's stage-1 PASS
is preserved and does not serve as a stage-2 completion marker.

Validation: the prescribed `scompile.py NA lem-a1-geometric-cover-component-qc-proper
<module>` compiled both the sandbox probe and library-path module cleanly (1.8 s and 2.1 s),
with no errors or warnings. There are no auto-bound variables, and every source line is at
most 100 characters. The required delivery dry run and push follow; their printed output is
the authoritative preflight/delivery result.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
