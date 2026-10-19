## Worker report

The module `Sheaf.AlgebraicTopology.JoyalWalkingIsomorphismFibrationTest` states
`SSet.joyal_walking_isomorphism_fibration_test`. It uses the fixed-universe model
parameter `M` and its cofibration and weak-equivalence identifications from the
Joyal model-structure dependency. The left side is the model-structure fibration
predicate, i.e. “`p` is a Joyal fibration”.

The Lean rendering of each hypothesis is as follows. `M` is
`HomotopicalAlgebra.ModelCategory SSet.{u}`. `hcof` identifies the model
cofibrations with maps whose component functions are injective at every opposite
simplex. `hweak` identifies model weak equivalences with the homotopy-category
equivalence tests in every testing universe `SSet.{max u v}`. `Q` and `Q'` are
simplicial sets in the same universe, and their typeclass binders are the two
quasicategory hypotheses. `p : Q ⟶ Q'` is the simplicial map under test.

The conclusion is an iff. Its left clause is
`M.categoryWithFibrations.fibrations p`. The first right-hand clause,
`innerHornInclusions.rlp p`, is the right lifting property against every inner
horn inclusion. The second right-hand clause is
`HasLiftingProperty (SSet.const (X := SSet.stdSimplex.obj ⦋0⦌)
SSet.coherentIso.x₀) p`; this is the right lifting property against the map
`u₀ : Δ⁰ → N(Codiscrete (ULift Bool))` selecting the zero object. Mathlib's
`SSet.coherentIso` is exactly the full nerve of the walking isomorphism: its
objects are `WalkingIso.zero` and `WalkingIso.one`, with one morphism in every
ordered hom-set. No vertex-surjectivity condition is included.

The two statement-dependency modules were read in full at the relevant declarations.
`Sheaf.CategoryTheory.EnhancedDiagramsCones` (recorded main declaration
`SSet.Enhanced.coneCategory`) supplies Mathlib's simplicial primitives and the
equivalence-edge/core definitions used by the proof; the cone construction itself
is not needed by this particular signature. The model parameter and its two
normalizations are exactly those of `SSet.exists_joyal_model_structure` from
`Sheaf.AlgebraicTopology.JoyalModelStructure`; the model existence theorem provides
them, and the present theorem does not choose any data from that existence.
The walking-isomorphism nerve and
its selected zero vertex are Mathlib declarations `SSet.coherentIso` and
`SSet.coherentIso.x₀` from
`Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso`; the lifting-property
predicate is Mathlib's `CategoryTheory.HasLiftingProperty`, and the inner-horn
family is `SSet.innerHornInclusions` from
`Mathlib.AlgebraicTopology.Quasicategory.InnerFibration`.

`HasLiftingProperty.sq_hasLift` quantifies over every `CommSq` with the specified
left and right maps and requires `sq.HasLift`; its lift carries both triangle
equations. The existing `MorphismProperty.rlp` quantifies this predicate over the
whole given arrow family. Thus the last sentence specifying diagonal fillers is
retained, rather than replacing strict lifting by lifting up to homotopy.

All stated proof dependencies are imported with ordinary imports:
`SSet.Enhanced.simplicial_homotopy_equivalence_weak` from
`Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`,
`SSet.KanQuillen.right_proper_kan_quillen` from
`Sheaf.AlgebraicTopology.KanQuillenRightProper`,
`SSet.Enhanced.core_kan_fibration` from `Sheaf.CategoryTheory.CoreKanFibration`,
`SSet.Enhanced.isofibration_exponentiation` (including `IsIsofibration`) from
`Sheaf.CategoryTheory.IsofibrationExponentiation`, and
`SSet.joyal_quasicategory_characterizations` from
`Sheaf.AlgebraicTopology.JoyalQuasicategoryCharacterizations`. No import cycle
is introduced. The docstring carries all four DAG proof steps and their citations.

Edge cases checked mathematically before writing the signature:

- `Q` empty: both right-hand tests are vacuous because each test domain has a
  vertex; the empty map is indeed a Joyal fibration.
- `Q'` empty: existence of `p` forces `Q` empty, with no extra inhabitance binder.
- A point included in a discrete two-point nerve is a Joyal fibration: all
  walking-isomorphism diagrams based there remain in that component. It is not
  vertex-surjective, so no surjectivity condition can be added.
- A point selecting zero in the walking-isomorphism nerve fails the endpoint
  test (use the identity map of the full nerve downstairs) and is not a Joyal
  fibration, although it is an inner fibration.
- For `Q'` a point and `Q` any quasicategory, the endpoint diagrams lift by
  constant diagrams and the inner horn tests are the quasicategory axioms.
- The inner-horn family starts at dimension two, exactly all possible inner
  indices; dimensions zero and one supply no extra conditions. The universe `u`
  is arbitrary, and both the test interval and `p` inhabit that same universe.

Searches for an existing project declaration or duplicate notion were made with:

- `msearch.py ... leanfinder "A map between quasicategories is a Joyal fibration
  if and only if it lifts inner horns and the endpoint inclusion into the nerve
  of the walking isomorphism"`: eight hits, all about Kan horn fibrations or
  standard boundaries (`modelCategoryQuillen.J`, `.I`, `.fibration_iff`, etc.);
  no exact characterization.
- `msearch.py ... loogle '"InnerFibration", "HasLiftingProperty"'`: zero hits.
- `msearch.py ... leansearch "Joyal fibration between quasicategories has the
  right lifting property against the walking isomorphism endpoint"`: eight hits,
  including the generic `trivialCofibrations_rlp` and Joyal's trick, and Kan
  fibration results; no exact characterization.
- `msearch.py ... grep 'WalkingIso|coherentIso|Joyal.*fibration'
  AlgebraicTopology`: eight hits, finding `CoherentIso.lean` and `JoyalTrick.lean`.
  Read `WalkingIso`, `coherentIso`, `x₀`, `hom`, `inv`, and their inverse triangles
  in the Mathlib source. The existing full nerve is reused directly.
- `rg -n 'coherentIso|WalkingIso|Joyal.*fibration|innerHornInclusions.rlp'`
  over `lean/Sheaf` and `WeilConjectures`: found the Mathlib `coherentIso`
  construction and the distinct general characterization node, but no exact
  walking-isomorphism iff theorem;
- `rg -n 'lem-coef-joyal-walking-isomorphism-fibration-test|joyal_walking_isomorphism_fibration_test'`
  over `WeilConjectures`, `dag/lean_names_upstream.json`, and `lean/Sheaf`: zero hits.

Read [Joyal--Tierney Proposition 1.13](https://arxiv.org/html/math/0607820)
online: it states that a mid fibration between quasicategories is a quasi-fibration
iff it lifts `{0} ⊂ J`; the preceding sentence says every quasi-fibration is mid.
This is precisely the conjunction and iff in the Lean. WANTED archive: the
source's local archive is not supplied by this delivery; the node already records
the online source. No blueprint unit statement is altered.

No statement correction or `STATEMENT-DISPUTED` flag is needed. The theorem body
is intentionally `sorry` for stage 2.

Validation: the final module compiled cleanly with all five proof-dependency
imports using `scompile.py NN lem-coef-joyal-walking-isomorphism-fibration-test`.

## Second reading by NN

I read the node statement, its source place (Joyal--Tierney, arXiv:math/0607820,
Proposition 1.13), the copied Lean module, and the recorded statement dependencies.
The source first defines a quasi-fibration of categories by lifting an isomorphism
whose source is prescribed, identifies this with RLP against `{0} ⊂ J`, and then
states that a map between quasicategories is a quasi-fibration exactly when it is a
mid fibration (RLP against every inner horn) and has this `{0} ⊂ J` lifting property.
The node's `J` is the full nerve of the groupoid with objects `0,1` and one morphism
in every ordered hom-set, and its `u₀` selects `0`.

The Lean rendering matches each item as follows.

* The fixed simplicial-set universe is `SSet.{u}`.  The model-structure object is
  `M : HomotopicalAlgebra.ModelCategory SSet.{u}`.  `hcof` states, for every
  `i : A ⟶ B`, that the chosen cofibrations are exactly the maps whose every
  `i.app n` is injective.  `hweak` states, for every such `i`, that the chosen weak
  equivalences are exactly the maps inducing equivalences of `hoFunctor` after
  exponentiation into every quasicategory `C : SSet.{max u v}`.  These are the two
  normalizations supplied by `SSet.exists_joyal_model_structure`; the explicit
  parameters do not add a mathematical assumption beyond choosing that recorded
  Joyal model structure.
* `Q Q' : SSet.{u}` carry `[Quasicategory Q]` and `[Quasicategory Q']`, and
  `p : Q ⟶ Q'` is the map under test.  Thus both quasicategories are in one fixed
  universe, as in Proposition 1.13; no extra nonemptiness, finiteness, or size
  hypothesis is present.
* The left conclusion is exactly
  `M.categoryWithFibrations.fibrations p`, the fibration predicate of the normalized
  Joyal model structure.  The right conclusion is the conjunction
  `innerHornInclusions.rlp p` and
  `HasLiftingProperty (SSet.const (X := SSet.stdSimplex.obj ⦋0⦌)
  SSet.coherentIso.x₀) p`.  Mathlib's `coherentIso` is the nerve of
  `WalkingIso := Codiscrete (ULift Bool)`, and `coherentIso.x₀` is precisely the
  selected zero vertex, so this map is the node's `u₀ : Δ⁰ ↪ J`.  `HasLiftingProperty`
  is the strict commutative-square diagonal filler predicate, retaining both
  triangle equalities.  No vertex-surjectivity clause occurs.

The statement dependencies were checked at their declarations.  `SSet.Enhanced`
from `Sheaf.CategoryTheory.EnhancedDiagramsCones` supplies the simplicial and
quasicategory conventions used by the signature.  `SSet.exists_joyal_model_structure`
from `Sheaf.AlgebraicTopology.JoyalModelStructure` supplies exactly the model object
and the two displayed normalizations.  The walking-isomorphism nerve and endpoint
are Mathlib's `SSet.coherentIso` and `SSet.coherentIso.x₀`; no private copy is made.
The additional proof imports are present as ordinary imports and do not alter the
statement.  Their declarations and the proof-dependency list agree.

Edge cases were checked.  If `Q` is empty, both lifting predicates are vacuous and
the empty map is a Joyal fibration, as the source quasi-fibration condition is also
vacuous.  If `Q'` is empty, a map `Q ⟶ Q'` forces `Q` empty.  A map from a point into
a discrete two-point quasicategory is allowed and need not be vertex-surjective.
The map selecting zero into `coherentIso` fails the endpoint test, as expected.
For a point target, inner-horn lifting is exactly the quasicategory condition on the
source and the endpoint tests are constant-diagram lifts.  There are no inner horns
in dimensions zero or one; the indexed family therefore adds no unintended cases.
The universe `u` is arbitrary, and no characteristic, ring, zero-object, or
Noetherian assumption is involved.

I repeated the duplicate searches.  `msearch.py ... leanfinder "Joyal fibration
quasicategory RLP walking isomorphism endpoint"` returned only generic horn,
quasicategory, and model-category declarations.  `msearch.py ... leansearch
"Joyal fibration RLP coherentIso x₀"` likewise returned only generic lifting and
Quillen/Joyal-trick declarations.  The Loogle query using `HasLiftingProperty` had
no hits (the tool reported that identifier as unavailable), and a second Loogle
query using the known Mathlib names also found no exact theorem.  Grep over Mathlib,
`WeilConjectures`, and `lean/Sheaf` found only the Mathlib `CoherentIso` construction,
the distinct finite-interval theorem, and the generic characterization node; no
duplicate walking-isomorphism fibration theorem exists.  The exact node id and
declaration name are absent from the source and upstream-name index.

No mismatch was found, so no Lean or node statement was changed.  The module
recompiled with the required `scompile.py` command; its only postponed proof is the
named theorem `SSet.joyal_walking_isomorphism_fibration_test` with `sorry`.
