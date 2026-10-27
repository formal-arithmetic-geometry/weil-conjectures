## Worker report

The module Sheaf.AlgebraicGeometry.BirationalCommonDenseOpens states
AlgebraicGeometry.exists_common_dense_opens_isIso_of_birational, with its proof
postponed by sorry. It states Stacks 0BAC, alternative (2), using the definition
of birational morphism in Stacks 01RO. Both passages were read in the local
Stacks source morphisms.tex (definition-birational and lemma-birational-birational).
No definition, auxiliary theorem, or statement correction is needed.

Hypothesis and conclusion correspondence:

- Schemes X and Y and their morphism f:Y→X are `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
- Local finite presentation is `[LocallyOfFinitePresentation f]`.
- Finitely many components of X and Y are respectively
  `hX : (irreducibleComponents X).Finite` and the analogous `hY`.
- The bijection on component generic points is
  `Set.BijOn f (genericPoints Y) (genericPoints X)`. Mathlib defines
  `genericPoints T = {x | closure {x} ∈ irreducibleComponents T}`; by the
  recorded `IsGenericPoint` definition this is exactly the node's set of
  generic points. `BijOn` includes mapping into, injectivity, and surjectivity.
- Isomorphisms on all generic local rings are
  `∀ η : Y, η ∈ genericPoints Y → IsIso (f.stalkMap η)`.
  The recorded locally ringed space interface supplies precisely the canonical
  map from the target stalk at f(η) to the source stalk at η.
- Open subschemes are `U : Y.Opens` and `V : X.Opens`, with Mathlib's canonical
  schemes `U.toScheme` and `V.toScheme` and their open immersions.
- Density of both is `Dense (U : Set Y) ∧ Dense (V : Set X)`.
- The clause f(U)⊆V is `∃ hUV : U ≤ f ⁻¹ᵁ V`.
- The specified restriction being an isomorphism is
  `IsIso (f.resLE V U hUV)`, where `resLE` is Mathlib's restriction on source
  and target opens. Its domain and codomain are U.toScheme and V.toScheme.

Dependency declarations and their modules, read at their definitions:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and
  AlgebraicGeometry.Scheme.Hom.
- def-sbc-locally-finite-presentation:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  AlgebraicGeometry.LocallyOfFinitePresentation.
- def-weil-irreducible-components: Mathlib.Topology.Irreducible,
  irreducibleComponents (the exact mathlib_match, no lean record needed).
- def-sc-generic-point: Mathlib.Topology.Sober, IsGenericPoint; its existing
  genericPoints predicate packages the component specialization exactly.
- def-weil-locally-ringed-space-morphism:
  Mathlib.Geometry.RingedSpace.LocallyRingedSpace,
  AlgebraicGeometry.LocallyRingedSpace.Hom; the inherited stalk map is exposed
  for schemes as Scheme.Hom.stalkMap in Mathlib.AlgebraicGeometry.Scheme.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  AlgebraicGeometry.IsOpenImmersion. Open subschemes and the restricted morphism
  use Mathlib.AlgebraicGeometry.Restrict (Scheme.Hom.resLE).

All currently stated proof dependencies have their recorded modules imported
(either publicly when also a statement dependency, or as ordinary proof imports).
The proof-only node lem-sfb-birational-generic-localization has no Lean record or
Mathlib match in the read snapshot and is not imported. It is not needed to type
this statement. Its future landing can add the proof import. The docstring
reproduces all seven proof steps, including that input and its application.

Edge cases checked before writing:

- Empty schemes are allowed. If either is empty, the bijection of generic
  points forces both to be empty (schemes are sober and components cover).
  The full opens give the unique isomorphism. No nonempty binder is imposed.
- Reducible schemes with finitely many components are retained; no
  irreducibility or integrality instance is assumed.
- Nilpotents are allowed: no reducedness condition occurs. Finite presentation
  is the precise alternative (2) allowing the finite kernel argument.
- Nonseparated morphisms are retained. For the doubled-origin affine line
  mapping to the affine line, deleting one origin gives a dense open source
  isomorphic to the whole target. The assertion permits such a source open.
- In particular the source open is not forced to equal the full inverse image
  of the target open; only the stated inclusion is requested.
- Universe u is explicit, with every variable bound and no auto implicits.

Searches for reuse (2026-10-22):

- msearch.py leanfinder: “A locally finitely presented morphism inducing a
  bijection on generic points and isomorphisms on their local rings is an
  isomorphism on common dense opens”. Eight related stalkwise/local-isomorphism
  results, headed by isomorphisms_eq_stalkwise; none has these hypotheses.
- msearch.py loogle: “AlgebraicGeometry.Scheme.PartialIso,
  AlgebraicGeometry.LocallyOfFinitePresentation”. Zero results.
- msearch.py grep: “0BAC|0BAB|generic.*stalk|stalk.*generic”, AlgebraicGeometry.
  Eleven related smoothness/function-field/reducedness hits; no exact theorem.
- msearch.py leansearch: “locally finitely presented birational morphism
  isomorphism dense opens”. Eight local-finite-presentation/local-isomorphism
  declarations; no exact theorem.
- rg of lean/WeilConjectures and lean/Sheaf for genericPoints, common dense
  opens, birational open statements, the node id, and the proposed declaration.
  The existing BirationalIsomorphismDenseOpen module is the separated stronger
  target-inverse-image conclusion and cites this prerequisite; its separation
  hypothesis prevents its use as this statement. No duplicate declaration.
- Read Mathlib.Topology.Sober genericPoints and IsGenericPoint, and the existing
  resLE definition. They supply the exact notions without a new definition.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The earlier
preflight report concerned a stage-1 acceptance, not a Lean statement. This
packet supplies only the item's lean field, module, and report.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
