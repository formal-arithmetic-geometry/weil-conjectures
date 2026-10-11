## Worker report

The module Sheaf.AlgebraicGeometry.FinalNoetherianBaseSystemProperties states
AlgebraicGeometry.Scheme.NoetherianApproximation.finalBaseSystem_properties, with proof `sorry`.
No definition, dependency module, or statement correction is needed.

The node's source blueprint was read on the server: sec-nagata-compactification,
sk-cor-nagata-sketch-fp/lemma-nagata-final-noetherian-base-system.md, order 372.
It states precisely the same four properties as the node.

Hypotheses and clauses:

- The system of def-nagata-final-noetherian-base-system is the supplied
  `N : S.NoetherianApproximation`, exactly the representation in that dependency's lean record.
  `S : Scheme.{u}` binds the base explicitly. The approximation already includes its index,
  cofiltered structure, stages, transitions, compatible projections and limit cone. The qcqs
  assumption in the section is needed to construct such an N, not as additional data for its
  properties; this lemma takes the constructed system itself, as the dependency record says.
- Every stage S_lambda is Noetherian: `∀ i : N.I, IsNoetherian (N.D.obj i)` in the first conjunct.
- Every stage is of finite type over Z: the same universally quantified conjunct contains
  `LocallyOfFiniteType (specULiftZIsTerminal.from (N.D.obj i))` and
  `QuasiCompact (specULiftZIsTerminal.from (N.D.obj i))`. Mathlib's FiniteType.lean explicitly
  defines finite type as these two properties. Its target is Spec of universe-lifted Z, the
  project's terminal scheme, so this is the canonical integer structure morphism.
- Every transition is affine: `∀ (i j : N.I) (f : i ⟶ j), IsAffineHom (N.D.map f)`.
- Kappa_S is an isomorphism: `IsIso N.gluedLimitComparison`.
  `[HasLimit N.D]` only chooses the limit appearing in the recorded comparison declaration;
  it is obtainable from N.isLimit and imposes no mathematical existence restriction.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.GluedLimitComparison:
  AlgebraicGeometry.Scheme.NoetherianApproximation.gluedLimitComparison. Its body is
  `limit.lift N.D (Cone.mk S N.π)`, retaining precisely the constructed comparison.
- WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit (imported by that module):
  AlgebraicGeometry.Scheme.NoetherianApproximation, including all its fields and docstring;
  AlgebraicGeometry.Scheme.NoetherianApproximation.isNoetherian_obj. This structure is also
  listed among the dependency's declarations. Finite-type stages and affine transitions are
  recorded fields. The Noetherian instance uses finite type over the Noetherian integers.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.AlgebraicGeometry.Noetherian: IsNoetherian;
  and Mathlib's IsAffineHom and CategoryTheory.IsIso, available through the dependency import.

Edge cases checked: no stage is assumed nonempty or integral; the empty scheme and zero rings
are allowed. N.I is cofiltered, hence nonempty as the approximation construction requires;
no new restriction on the index is introduced. The index and schemes have the same universe u,
as in the recorded structure. All morphisms, including identity transitions, are quantified.
An arbitrary choice of limit is allowed; uniqueness of limits gives the comparison isomorphism.
There is no characteristic assumption. No statement fault or dispute was found.

Searches for existing statements:

- msearch.py leansearch, query "Noetherian approximation scheme finite type over integers affine
  transition maps limit comparison isomorphism": service unavailable (Internal Server Error).
- msearch.py leanfinder, the same query: eight hits, including IsNoetherian and finite affine
  cover criteria; none states the four properties of this recorded system and comparison.
- msearch.py loogle, "AlgebraicGeometry.IsNoetherian, AlgebraicGeometry.IsAffineHom": zero hits.
- msearch.py grep, "NoetherianApproximation|gluedLimitComparison", AlgebraicGeometry: zero hits.
- rg over WeilConjectures for NoetherianApproximation and its structure source: the approximation
  structure and its Noetherian instance exist, but no conjunction using gluedLimitComparison.
  Search for the item id and gluedLimitComparison in WeilConjectures: no hits.
- rg over lean/Sheaf for NoetherianApproximation and gluedLimitComparison: the recorded comparison
  definition and related approximation applications exist; no theorem states this conjunction.
- rg over dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf for final_noetherian,
  finalNoetherian and gluedLimitComparison: only the existing comparison module matched.

Validation: server single-file compilation and deliver2.py --no-push dry run are run before READY.
The independent second reading is left to the second reader as instructed.

## Second reading by J1

I independently read the item node, its source blueprint node (order 372), the
final-system definition (order 371), and the unit's `_section.md` on the server.
The unit assumes a qcqs base S; its separated finitely presented X -> S belongs
to the compactification corollary, not to this base-system property lemma.
I also read Stacks `limits.tex`, proposition-approximate (Tag 01ZA), lines
1254-1270: qcqs S admits a directed inverse system with affine transitions,
finite-type-over-Z stages, and S as its limit. The item asserts the properties
of the supplied system, not the existence proposition.

The object's, hypothesis's, and conclusion's checklist, with verdicts:

- Base S: `{S : Scheme.{u}}`. Correct. No field, characteristic, integrality,
  or Noetherian assumption on S is introduced.
- Selected system N_f = N(S): `(N : S.NoetherianApproximation)`. Correct against
  the recorded dependency: def-nagata-final-noetherian-base-system explicitly
  aliases the supplied N, rather than choosing another system. I opened its
  full node and lean record and the underlying structure in
  WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit, lines 189-224.
  The index is `N.I : Type u`, the diagram is `N.D`, its stages are `N.D.obj i`,
  transitions are `N.D.map f`, and its compatible projections are `N.π`.
- The source's qcqs assumption: no separate binder is needed for this property
  statement on a supplied approximation. N includes a limit cone over a
  cofiltered finite-type-over-Z diagram with affine transitions; its existence
  already entails qcqs S (affine projections to qcqs stages, and stability of
  qcqs under affine morphisms). It is not an arbitrary unconstrained diagram.
  The existence theorem needs qcqs to supply N, as the source and node say.
- Retained comparison kappa_S: `N.gluedLimitComparison`. Correct: I opened
  Sheaf.AlgebraicGeometry.GluedLimitComparison; this is exactly
  `limit.lift N.D (Cone.mk S N.π)`, with the original base and projections.
  `[HasLimit N.D]` merely selects the limit used by this recorded declaration;
  N.isLimit supplies existence, so it adds no mathematical restriction.
- Every stage Noetherian: `∀ i : N.I, IsNoetherian (N.D.obj i)` in the first
  conjunct. Correct: this is the scheme property, not merely local
  Noetherianity. I read `NoetherianApproximation.isNoetherian_obj`, lines
  230-237, which uses the finite-type stages over Noetherian integers.
- Every stage of finite type over Z: the same universal quantifier followed
  by `LocallyOfFiniteType (specULiftZIsTerminal.from (N.D.obj i)) ∧
  QuasiCompact (specULiftZIsTerminal.from (N.D.obj i))`. Correct: Mathlib's
  Morphisms/FiniteType.lean explicitly defines finite type as locally finite
  type plus quasi-compact. The terminal integer scheme uses ULift to preserve
  universe u; its unique map is the integer structure morphism. There is no
  accidental finite-presentation or affine-stage requirement.
- Every transition affine: `∀ (i j : N.I) (f : i ⟶ j),
  IsAffineHom (N.D.map f)`. Correct: both endpoints and every index morphism
  are quantified, including identities, with the diagram's direction.
- Comparison an isomorphism: `IsIso N.gluedLimitComparison`. Correct: it is
  the retained map, not an unrelated existential isomorphism. No conclusion
  clause is missing or added; quantification is over one supplied system
  followed by all its stages and transitions.

Edge cases: the empty scheme and zero chart rings are permitted; there is no
nonempty-stage assumption. An empty indexing category is excluded by N's
recorded IsCofiltered structure, exactly as the approximation notion requires,
not by an added binder. Identity transitions and one-object systems are
included. Universes are explicitly bound by `universe u`, with schemes and
index in the same universe; no independent lower test universe appears.
No n or characteristic parameter occurs, so n = 0 is inapplicable and all
characteristics are allowed. No variable or universe is left unbound.

Independent searches used different descriptions from the first reading:

- LeanFinder via msearch.py: "inverse limit of finite type integer schemes
  affine bonding morphisms isomorphism". Eight hits; the relevant
  `isAffineHom_π_app` gives affineness of projections, not this four-clause
  theorem. Others concern affine spaces, finite-type morphisms, or sigmaSpec.
- Loogle via msearch.py: "AlgebraicGeometry.IsNoetherian, CategoryTheory.IsIso".
  One irreducible-component inclusion theorem, not this statement.
- LeanSearch via msearch.py: "A scheme expressed as a cofiltered limit of
  schemes of finite type over the integers with affine transition maps has
  an invertible canonical limit comparison". Service unavailable (Internal
  Server Error); recorded as unavailable, not as a negative search verdict.
- rg in Mathlib/AlgebraicGeometry, WeilConjectures, lean/Sheaf, and
  dag/lean_names_upstream.json for `noetherian.*approximation`,
  `approximation.*noetherian`, `finalBaseSystem`, and `gluedLimitComparison`.
  The existing approximation structure, construction, Noetherian instance,
  and retained comparison were found and read; no existing statement of
  this conjunction was found. Other approximation results are ring,
  complex, tensor-data, or compactification results on different objects.

No mathematical mismatch was found, so the Lean and node signature are kept
verbatim. No new definition node or dependency module is present or needed;
there is no statement_change to review. The only theorem has proof `by sorry`,
with the source and blueprint id in its docstring, and its proof narrative
names every node in the DAG proof step. There is no new definition, private
notion, local notation, or file-local instance. The single dependency import
provides all objects used. Changes in this reading: appended this independent
checklist, source checks, edge cases, and searches to the report only.
