## Worker report

The module `lean/Sheaf/AlgebraicTopology/SegalDkTwoOutOfSix.lean` defines
`SSet.Segal.IsDwyerKanEquivalence` and states
`SSet.Segal.dk_two_out_of_six` with proof `sorry`. The definition renders the
node's two defining conditions: `(homotopyFunctor f).IsEquivalence` is the
ordinary homotopy-category equivalence, and the universal quantifier over
`x y : (A.obj (op ⦋0⦌)) _⦋0⦌` requires the specified strict mapping-fiber map to
be `Enhanced.IsWeakHomotopyEquivalence`.

The theorem has four Segal-space hypotheses `hA₀`, `hA₁`, `hA₂`, and `hA₃`, then
three composable maps `a : A₀ ⟶ A₁`, `b : A₁ ⟶ A₂`, and `c : A₂ ⟶ A₃`.
Its first conjunct says that DK equivalences `a` and `b` compose to a DK
equivalence `a ≫ b`. Its second conjunct says that if `a ≫ b` and `b ≫ c`
are DK equivalences, then each of `a`, `b`, and `c` is one. No completeness
hypothesis is present. The explicit theorem signature in the node's `lean`
record is verbatim from the declaration up to (excluding) `:=`, as the preflight extracts it.

The statement dependency declarations used are:

* `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.IsWeakHomotopyEquivalence`,
  module `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
* `lem-coef-kan-quillen-right-proper`: `SSet.KanQuillen.right_proper_kan_quillen`,
  module `Sheaf.AlgebraicTopology.KanQuillenRightProper` (used by the proof plan
  for Kan weak-equivalence cancellation).
* `lem-coef-reedy-model-structure`: `HomotopicalAlgebra.Reedy.model_structure`,
  module `Sheaf.CategoryTheory.ReedyModelStructure` (used by the proof plan for
  model-category two-out-of-three).

The module also imports the stated proof-support modules
`Sheaf.AlgebraicTopology.RealizationCylinder` and
`Sheaf.Topology.HomotopyGroupsBasepointChange`, and the stated proof dependency
`Sheaf.AlgebraicTopology.KanWhiteheadInverse` (`SSet.Enhanced.kan_whitehead_inverse`;
import added by the maintainer's reviewer, see below).

Edge cases checked against the node proof and source: empty Segal spaces make
all vertex-pair conditions vacuous; empty mapping fibers are allowed; identity
maps satisfy both clauses; discrete nerves and nerves of one-object groupoids
illustrate the definition without completeness; the two-out-of-six statement
has no nonemptiness or connectedness assumption. The four Segal-space binders
are explicit, so no universe or auto-implicit case is omitted.

Searches for an existing declaration: `msearch.py ... leanfinder` with query
`Dwyer Kan equivalences of Segal spaces satisfy two out of six and composition`
returned only strict Segal/nerve declarations (`SSet.StrictSegal` and related),
not maps of Segal spaces. `msearch.py ... loogle` with query `"Segal",
"Equivalence"` returned zero hits. `msearch.py ... grep` with regular
expression `Dwyer.?Kan|[Ss]egal.*[Ee]quival|twoOutOfSix|two_out_of_six`
found only Mathlib's strict Segal file. Repository `rg` for
`Dwyer|Segal|two.out.of.six` found no upstream declaration of this theorem;
the existing project module `SegalCategoricalEquivalence.lean` supplies the
Segal-space and strict mapping-fiber constructions but does not state the
composition/cancellation theorem. Thus no existing exact declaration applies.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Author self-check and handoff

This is the author's self-check; the independent second reader has not run yet.
The second reader should check the two clauses against Rezk Section 7.4 and
Lemma 7.5 and then write the independent second-reading section.

The definitions `SSet.Segal.Space`, `IsSegal`, `mappingFiber`,
`mappingFiberMap`, `homotopyCategory`, and `homotopyFunctor` are reused from
`Sheaf.AlgebraicTopology.SegalCategoricalEquivalence`. That node is a proof
consumer of this item, so adding it as a DAG dependency or adding the reverse
proof import there would close a cycle. Only its explicit constructions are
used here; `categorical_equivalence_dk` is not assumed. The reverse proof
import must remain omitted under stages/2-statements.md section 3 rule 7.
No new definition node or dependency repair is needed: the DK predicate
renders the definition introduced in this item's own statement.

The introductory clauses were checked against those declarations in full:
`Space.{u}` is `SimplexCategoryᵒᵖ ⥤ SSet.{u}`; `IsSegal` combines the
recorded Reedy matching-fibration predicate with weak equivalences of the
consecutive-edge `segalMap` for every `n ≥ 2`. `mappingFiberSubcomplex`
imposes the constant source and target equations in every inner degree,
and `mappingFiberMap` restricts the actual degree-one component of the
simplicial-space map. `homotopyCategory` uses the edge-path and triangle
presentation, with degeneracies as identities and degree-two triangles as
composition relations; the recorded `homotopyCategory_homs` clause
identifies its hom sets with components of the strict fibers.
`homotopyFunctor` is induced by the actual map on the outer zero-inner-degree
row. Consequently the DK predicate uses the node's specified category and
fiber maps. The imported module's final theorem is not used as a premise.

Continuation audit (2026-10-17): reran all three `msearch.py` queries above;
LeanFinder returned eight strict-Segal/nerve hits, Loogle zero hits, and
grep two `StrictSegal.lean` hits. Read its `IsStrictSegal` and `spineEquiv`
signatures: they concern bijections of simplices of one simplicial set.
Also read `CategoryTheory.DwyerKanEquivalence` in
`Sheaf.CategoryTheory.CoherentNerveComparison`: its inputs are enriched
functors between simplicial categories, not maps of simplicial spaces.
Neither is this theorem or this predicate. Direct `rg` searches for the item
id and `Dwyer|Segal|two.out.of.six` in upstream `WeilConjectures` returned no
hits; the proposed full declaration names are absent from
`dag/lean_names_upstream.json`. Project searches found the reused
Segal-space constructions and the enriched-category predicate, but no
existing exact composition/two-out-of-six theorem. No repair note exists
for this item. Comparing the sandbox node with the shared node confirms
that only `lean` changes.

Source verification: fetched the node's Rezk PDF into this sandbox's
scratchpad and read the text of Section 7.4 and Lemma 7.5, printed p. 16.
The source has exactly the two DK conditions and both conclusions, without
completeness. The full nine-step natural-language proof is retained in the
module docstring. The web reader returned HTTP 429; direct retrieval of the
same primary-source PDF succeeded.

Validation: `scompile.py` compiled the module cleanly. The first dry run
reported the signature delimiter and a split blueprint tag; both are repaired.
The continuation reran `scompile.py`: both its sandbox-name and library-name
compilations passed cleanly (1.2 seconds each).

## Earlier second reading (a previous round; superseded)

I read the copied node `lem-coef-segal-dk-two-out-of-six.json`, its three
statement dependencies, the declaration sources, and Rezk Section 7.4/Lemma
7.5 (printed p. 16). The node's objects and clauses, matched to Lean, are:

* The ambient object is a small simplicial space
  `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. Lean renders this as
  `SSet.Segal.Space.{u}` and binds `A₀ A₁ A₂ A₃ : Space.{u}`.
* A Segal-space hypothesis for each object is rendered by
  `hA₀ : IsSegal A₀`, `hA₁ : IsSegal A₁`, `hA₂ : IsSegal A₂`, and
  `hA₃ : IsSegal A₃`. The imported `IsSegal` is Rezk Reedy fibrancy plus
  weak equivalences of all consecutive-edge Segal maps for `n ≥ 2`.
* For `f : A ⟶ B`, Lean's `IsDwyerKanEquivalence f` is the conjunction that
  `homotopyFunctor f` is an ordinary categorical equivalence and that, for
  every pair of vertices `x y` of `A₀`,
  `Enhanced.IsWeakHomotopyEquivalence (mappingFiberMap f x y)` holds. The
  imported `mappingFiber` is the strict `(d₁,d₀)` fiber with constant endpoint
  simplices, and `homotopyCategory` has those vertices and `π₀` of these fibers,
  with degeneracy identities and degree-two Segal composition.
* The composable maps are exactly `a : A₀ ⟶ A₁`, `b : A₁ ⟶ A₂`, and
  `c : A₂ ⟶ A₃`. The first conclusion conjunct is precisely DK(a) → DK(b) →
  DK(a ≫ b). The second is precisely DK(a ≫ b) ∧ DK(b ≫ c) →
  DK(a) ∧ DK(b) ∧ DK(c). There is no completeness, nonemptiness,
  connectedness, or characteristic hypothesis.

The source says exactly these two clauses: composition of two DK equivalences,
then two-out-of-six for three composable maps. It does not assume completeness.
The Lean composition order `a ≫ b` is the categorical notation for the source's
`b ∘ a`, so no order is reversed.

I checked edge cases explicitly. Empty simplicial spaces and empty strict
mapping fibers are admitted; the universal vertex-pair condition is then
vacuous. Identity maps satisfy both clauses. Discrete nerves and nerves of
one-object groupoids fit the same definition without completeness. `u` is the
single explicit universe used by the whole simplicial-space and simplicial-set
data, so no smaller independent test universe is introduced.

For the three dependency declarations I read the full signatures and sources:
`SSet.Enhanced.IsWeakHomotopyEquivalence`, the Kan model witness and
right-properness declaration, and the Reedy model-structure declaration. The
module imports the first three as public statement dependencies and imports the
two stated support modules needed by its proof plan. The Whitehead inverse is
only a proof dependency with no recorded declaration, so it is not imported.

I repeated the existing-declaration searches with LeanFinder, Loogle, and grep:
LeanFinder returned only strict-Segal/nerve declarations, Loogle returned no
match, and grep found only Mathlib's strict-Segal file. Searches of the upstream
`WeilConjectures` tree and the project found no exact theorem. A sibling project
module has a same-named predicate under `SSet.SegalSpace`, but it belongs to the
separate `SSet.SegalSpace.IsSegal`/cartesian-exponent interface; importing that
proof-consumer module here would create the reverse import cycle recorded in the
node's route. This module therefore keeps the node's recorded
`SSet.Segal` interface and its explicit mapping-fiber constructions, with no
additional hypothesis or private replacement of any dependency declaration.

No mismatch with the node or source was found, so no statement, dependency, or
definition was changed. The module and node copy agree verbatim on the theorem
signature. `scompile.py Q125 lem-coef-segal-dk-two-out-of-six` compiled both the
sandbox and library-name forms cleanly, with only the permitted `sorry` warning.

## Second reading by Q125

I independently opened the copied node, its Rezk source text, the module, and all
three statement-dependency declarations. The node's objects and hypotheses match the
Lean as follows:

* A simplicial space is `SimplexCategoryᵒᵖ ⥤ SSet.{u}`, rendered by
  `SSet.Segal.Space.{u}`. The four objects are exactly
  `A₀ A₁ A₂ A₃ : Space.{u}`.
* The source's Segal-space condition (Reedy fibrant and consecutive-edge Segal maps
  weak equivalences for every `n ≥ 2`) is supplied four times as
  `hA₀ : IsSegal A₀`, `hA₁ : IsSegal A₁`, `hA₂ : IsSegal A₂`, and
  `hA₃ : IsSegal A₃`. No completeness, connectedness, or nonemptiness premise is
  added.
* The source's strict fiber of `(d₁,d₀)` is the imported `mappingFiber`; its
  homotopy category has the imported edge-path/triangle presentation. The local
  `IsDwyerKanEquivalence f` is exactly ordinary equivalence of
  `homotopyFunctor f` together with
  `Enhanced.IsWeakHomotopyEquivalence (mappingFiberMap f x y)` for every pair of
  vertices `x y : (A.obj (op ⦋0⦌)) _⦋0⦌`.
* The maps are exactly `a : A₀ ⟶ A₁`, `b : A₁ ⟶ A₂`, and
  `c : A₂ ⟶ A₃`. The first conclusion is DK(a) and DK(b) implying DK(a ≫ b).
  The second is DK(a ≫ b) and DK(b ≫ c) implying DK(a), DK(b), and DK(c), in
  that order. Since categorical composition is written `a ≫ b`, this is the
  source's `b ∘ a` order.

I checked the source's Section 7.4 definition and Lemma 7.5 on printed page 16:
it states precisely composition and the two-out-of-six cancellation, with no
completeness assumption. Empty spaces and empty mapping fibers make the vertex
quantifier vacuous; identity maps reduce both clauses to identity maps; discrete
nerves and one-object groupoid nerves are admitted. The one explicit universe `u`
is shared by the entire simplicial-space and simplicial-set data, so no test
universe is inadvertently restricted. The `n ≥ 2` condition is inside the
imported `IsSegal` definition and includes all required edge cases.

The three dependency records were opened in full. `SSet.Enhanced.IsWeakHomotopyEquivalence`
is the recorded Kan-space weak-equivalence predicate; the Kan node supplies the stated
model structure, fibrant/Kan characterization, two-out-of-three and right properness;
the Reedy node supplies the Reedy model structure and its matching-map clauses. The
module imports exactly those public statement interfaces and the two proof-support
modules named by its proof plan. The Whitehead inverse is proof-only and has no Lean
declaration to import.

I reran the three required search kinds. LeanFinder returned only strict-Segal/nerve
declarations; Loogle returned no Segal-equivalence result; grep over Mathlib and the
upstream `WeilConjectures` tree found no exact theorem or predicate in the required
`SSet.Segal` interface. The project contains a semantically equivalent predicate
`SSet.SegalSpace.IsDwyerKanEquivalence` in the downstream cotensor-evaluation module,
but that module is a proof consumer of this item. Reusing it would introduce the
reverse import/dependency cycle; it also belongs to the distinct `SegalSpace`
cartesian-exponent interface. The current declaration therefore uses the recorded
`SSet.Segal` constructions and does not create a private replacement for any
statement dependency. No exact existing declaration applies.

No mismatch was found and no file or node field was changed. The module has only the
single postponed theorem proof (`sorry`), carries source and blueprint docstrings,
and has no line over 100 characters. `scompile.py Q125 lem-coef-segal-dk-two-out-of-six
lean/Sheaf/AlgebraicTopology/SegalDkTwoOutOfSix.lean` passed for both sandbox and
library-name compilations.

## Maintainer review correction (2026-10-17)

At the delivery base the proof dependency `lem-cbc-kan-whitehead-inverse` was already
stated, with module `Sheaf.AlgebraicTopology.KanWhiteheadInverse` and declaration
`SSet.Enhanced.kan_whitehead_inverse`. Under stages/2-statements.md §3 rule 7 the module
now imports it privately (`import`, not `public import`). The statements in the earlier
sections that the Whitehead inverse has no Lean declaration are superseded. Nothing else
changed; the signature and the node's `lean.statement` are unchanged.

Import cycle left out and listed (rule 7): `Sheaf.AlgebraicTopology.SegalCategoricalEquivalence`
(node `lem-coef-segal-categorical-equivalence-dk`) lists this item as a proof dependency, but
this module imports it for `Space`, `IsSegal`, `mappingFiberMap` and `homotopyFunctor`, so the
reverse import is omitted.
