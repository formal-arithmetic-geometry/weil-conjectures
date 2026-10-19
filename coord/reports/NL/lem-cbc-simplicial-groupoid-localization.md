## Worker report

The module `Sheaf.CategoryTheory.SimplicialGroupoidLocalization` states
`SSet.Enhanced.simplicial_groupoid_localization`.  It imports the landed
definition module `Sheaf.CategoryTheory.EnhancedDiagramsCones` and leaves exactly
the theorem proof as `sorry`.

The Lean statement is:

```lean
theorem simplicial_groupoid_localization {K S : SSet.{u}} (q : K ⟶ S)
    [SSet.KanComplex S] (hq : IsWeakHomotopyEquivalence q) :
    ∀ (C : SSet.{u}), C.Quasicategory →
      ∃ e : (ihom S).obj C ⟶ (equivalenceDiagrams K C).toSSet,
        e ≫ (equivalenceDiagrams K C).ι = (MonoidalClosed.pre q).app C ∧
          IsFunctorEquivalence e ∧ IsFullyFaithful e ∧
          (∀ (L : SSet.{u}) (p : L ⟶ K),
            (MonoidalClosed.pre (p ≫ q)).app C =
              e ≫ (equivalenceDiagrams K C).ι ≫ (MonoidalClosed.pre p).app C) ∧
          (∀ (D : SSet.{u}), D.Quasicategory → ∀ f : C ⟶ D,
            e ≫ (equivalenceDiagrams K C).ι ≫ (ihom K).map f =
              (ihom S).map f ≫ (MonoidalClosed.pre q).app D) := by
  sorry
```

The binders render the source hypotheses as follows: `q : K ⟶ S` is the map of
small simplicial sets; `[SSet.KanComplex S]` is the assertion that `S` is a Kan
complex; and `hq : IsWeakHomotopyEquivalence q` is the specified weak homotopy
equivalence.  The universal quantifier ranges over every `C : SSet.{u}` and the
following implication requires `C.Quasicategory`.  For each such `C`, the
existential `e` is a simplicial functor from the internal functor simplicial set
`Fun(S,C)` to the full subcomplex `Fun_eq(K,C)`, represented by the existing
`equivalenceDiagrams K C`.  The displayed equality says that composing `e` with
the full-subcomplex inclusion is restriction (precomposition by `q`).
`IsFunctorEquivalence e` requires a simplicial quasi-inverse and coherent natural
inverse equivalences. `IsFullyFaithful e` explicitly says that every induced
right-pinched mapping-space map is a weak homotopy equivalence. The final two
conjuncts render the last sentence of the node: for every shape map `p : L ⟶ K`,
restriction along `p ≫ q` equals successive restriction, and for every enhanced
functor `f : C ⟶ D`, restriction commutes with postcomposition. These are equalities
of simplicial maps, so they hold on transformations and all higher simplices.
They are written after the full-subcomplex inclusion, which is monic and therefore
reflects the corresponding equality inside the full subcategory. Iterating these
strict equalities gives the usual coherent composition compatibility, including
identities. No arbitrary choice of inverse is claimed to be strictly natural.

Dependency used: `def-cbc-enhanced-diagrams-cones`, declaration
`SSet.Enhanced.equivalenceDiagrams` (with its supporting declarations
`IsWeakHomotopyEquivalence`, `IsFunctorEquivalence`, and `IsFullyFaithful`) from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`.

Edge cases checked: the statement allows arbitrary `K`, including the empty
simplicial set; `S` is required only to be Kan and may be empty (Kan filling has
no dimension-zero nonemptiness condition); `q` may be an identity or any weak
equivalence; and no invertibility condition is imposed on coherent natural
transformations, since `IsFunctorEquivalence` is an equivalence of the full
enhanced categories rather than of their cores.

The universe `u` is an arbitrary common universe containing the two shapes and
the target. It follows the landed dependency's uniform `SSet.{u}` interface and
can be chosen as large as necessary; no finite-size or nonemptiness restriction
is imposed. The theorem quantifies over all targets in that universe.

Source verification: read the historical blueprint's opening compactification
choice and the corresponding current `main-20261015` proof. The localization
foundation is the agent-formulated tool recorded in this node, rather than a
claim that the proper-base-change blueprint itself states this general theorem.
Checked [Kerodon 01MY](https://kerodon.net/tag/01MY),
[01MS](https://kerodon.net/tag/01MS), and
[01MP](https://kerodon.net/tag/01MP) online. Proposition the project server supplies the
all-edges localization, and Proposition the project server includes the full functor-category
formulation. The node still requests an archived copy; none was found locally,
so the module does not claim that these Kerodon references are archived.

Searches made: `msearch.py ... leanfinder` for “simplicial groupoid localization
restriction equivalence edge inverting quasicategory” (ordinary localization and
model-category hits only); `msearch.py ... loogle` for `"Localization",
"KanComplex"` (0 hits); `msearch.py ... grep` for
`groupoid.completion|KanComplex.*[Ll]ocaliz|[Ll]ocaliz.*KanComplex|[Ss]implicial.*[Ll]ocaliz`
(0 hits); `msearch.py ... leansearch` for “A weak homotopy equivalence of simplicial
sets to a Kan complex is a localization at all edges, inducing equivalences of
full quasicategorical functor categories” (8 ordinary localization/model-category
hits, no exact match); and `rg` over `WeilConjectures`, `lean/Sheaf`, and `dag/nodes` for
groupoid-localization and equivalence-diagram declarations.  The existing
`CategoryTheory.FreeGroupoid` and `CategoryTheory.Localization` declarations
were inspected and rejected because they only give ordinary categories/groupoids,
not the higher coherent functor-category equivalence.  The existing
`HomotopicalAlgebra.FiniteReedy.IsLocalization` interface was also inspected; it
states the enhanced localization property for the nerve of a relative ordinary
category. It does not assert this simplicial-set weak-equivalence theorem.

Compilation with `scompile.py NL lem-cbc-simplicial-groupoid-localization` passed
for both the isolated sandbox module and its library-path compile, with no errors
or warnings. Earlier failures from private imports were corrected by using a
single `public import` of the statement dependency. No Lean definition was added,
no other DAG node was stated, and no statement correction was required.

The node copy differs from the read-only base only in `lean`. Its signature was
extracted verbatim from the final Lean file; every variable and universe is
explicit. The only postponed theorem is the main declaration, with the source
and step-by-step proof in its docstring. No `STATEMENT-DISPUTED` issue was found.

## Second reading by NL

I independently opened the node, the complete Lean module, and the declaration
module and node for `def-cbc-enhanced-diagrams-cones`. No repair note is present.
I read the ancestor's opening compactification step in both the historical
`master` blueprint and the current `main-20261015` proof. This is an
agent-formulated localization tool serving that step, rather than a Stacks
localization theorem. I opened [Kerodon 01MY](https://kerodon.net/tag/01MY),
[01MS](https://kerodon.net/tag/01MS), and [01MP](https://kerodon.net/tag/01MP).
Proposition the project server, implication (2) to (1), followed by condition (2) of
Proposition the project server, gives precisely the full-functor-category assertion.
There is no additional implicit assumption on the source simplicial set.

My checklist of objects, hypotheses and conclusions:

| Node item | Lean rendering and verdict |
| --- | --- |
| Small simplicial shapes and a specified map | `{K S : SSet.{u}} (q : K ⟶ S)`; exact. No Kan or quasicategory assumption on `K`. |
| Kan target shape | `[SSet.KanComplex S]`; exact. I read Mathlib's fibrancy definition and positive-dimensional horn-filling signature. |
| Weak homotopy equivalence | `hq : IsWeakHomotopyEquivalence q`; exact. The dependency tests realization on path components and on all positive based cube homotopy classes at every source base point. |
| Every enhanced target category | `∀ (C : SSet.{u}), C.Quasicategory →`; exact. Mathlib's quasicategory condition is inner-horn filling. No further target hypothesis is present. |
| Functors out of the Kan shape | `(ihom S).obj C`; exact simplicial internal hom. I read the presheaf closed-structure implementation, not just its name. |
| Full category of edge-inverting diagrams | `(equivalenceDiagrams K C).toSSet`; exact. Its definition applies `fullSubcomplex` to exactly the vertices whose diagrams send every edge of `K` to `IsEquivalenceEdge C`. |
| The equivalence is induced by restriction along this map | `∃ e`, with `e ≫ (equivalenceDiagrams K C).ι = (MonoidalClosed.pre q).app C`; exact. This specifies the actual restriction factorization, not an unrelated equivalence. |
| Equivalence of enhanced categories | `IsFunctorEquivalence e`; exact. I opened its definition: a simplicial quasi-inverse with natural equivalences from both composites to the identities. `AreNaturallyEquivalent` uses equivalence edges with both inverse-triangle witnesses. |
| Equivalence on entire mapping spaces | `IsFullyFaithful e`; exact. Every ordered pair of source vertices is tested by weak equivalence of `mappingSpaceMap`. The dependency's right-pinched `mappingSpace` fixes the whole initial face and final vertex as its node requires. |
| Noninvertible coherent transformations retained | The codomain is a full subcomplex of an internal hom, not its core; exact. Natural equivalences certify invertibility of the functor without requiring every transformation between diagram objects to be invertible. |
| Shape-composition compatibility | `∀ (L : SSet.{u}) (p : L ⟶ K)`, restriction along `p ≫ q` equals `e ≫ ι ≫ pre p`; exact equality of simplicial maps, including higher simplices. |
| Postcomposition compatibility | `∀ (D : SSet.{u}), D.Quasicategory → ∀ f : C ⟶ D`, the displayed equality with `(ihom S).map f ≫ pre q`; exact, for every enhanced functor. |

The subtype inclusion is degreewise injective, so the restriction factorization
is unique and expressing the compatibilities after inclusion loses no equality
inside the full subcategory. Iterating the strict simplicial-map equalities
gives the usual composition coherence, including identities. The assertion does
not demand a strictly natural choice of quasi-inverse. Explicit full faithfulness
is the mapping-space clause the node spells out, not an extra assumption.

Edge cases: both shapes may be empty; the Kan condition does not impose a
zero-dimensional filler. The component condition in `hq` prevents an empty
source/nonempty target from passing vacuously on homotopy groups. For empty
shapes the functor categories are terminal. Empty quasicategories are allowed;
for nonempty shapes their functor categories are empty. Discrete shapes,
identity `q`, the point shape, and a target with a noninvertible arrow are
covered. There are no characteristic, scheme, ring or finiteness parameters.
The arbitrary `u` is the ambient universe containing shapes and target, following
the recorded dependency; it is not fixed to the minimal size of a shape.
I checked that every variable and universe is bound, with `autoImplicit false`.

Independent searches actually run in this reading:

- `msearch.py ... leanfinder`: “A Kan replacement presents the localization of a
  simplicial set at every edge, with equivalence of full functor quasicategories”.
  Eight hits: primitive quasicategory/nerve declarations, `QCat.bicategory`,
  and truncated homotopy-category constructions; no matching theorem.
- `msearch.py ... loogle`: `"Quasicategory", "Localization"`; zero hits.
- `msearch.py ... grep`:
  `localization.*Kan|Kan.*localization|groupoid[Cc]ompletion|groupoid_completion|[Ff]unctor.*[Qq]uasicat`;
  twelve displayed hits on ordinary derived functors and Kan extensions.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`,
  and `dag/lean_names_upstream.json`, using `groupoidCompletion`,
  `groupoid_completion`, `localization.*Quasi`, `Quasi.*localization`,
  `Kan.*localization`, and the proposed name: no exact existing statement or
  declaration-name collision. I opened ordinary `FreeGroupoid.of` and `lift`
  and `Functor.IsLocalization`; these concern ordinary categories. I also
  read `HomotopicalAlgebra.FiniteReedy.IsLocalization` in
  `Sheaf.CategoryTheory.FiniteReedyLocalization`: it defines a localization
  property for a lifted nerve of an ordinary relative category and does not
  assert this theorem for an arbitrary simplicial source and Kan replacement.

No statement mismatch was found; I left the signature and node record unchanged. The
single public import uses the owning dependency's concrete definitions, with
no private copy, hollow data, or extra instance assumption. There are no new
nodes or dependency modules in this delivery. No statement correction is needed.
The dry run revealed a newer server-side stage-1 split, whose statement and
statement dependencies are unchanged. I read its seven proof steps and both
proof-dependency nodes directly from the server. I expanded the theorem's
docstring to match those steps individually: quasicategory closure and Kan
inverse triangles; the mixed-edge core identity; parameterized currying;
homotopy invariance against the Kan core; the two-test-object construction of
the inverse; full faithfulness; and strict simplicial compatibilities. This
repairs documentation drift against the current node without changing Lean's
statement. Neither `lem-cbc-enhanced-functor-cone-calculus` nor
`lem-cbc-kan-mapping-homotopy-invariance` has a recorded Lean module on the
server, so there is no additional proof-module import to add. The updated
proof and maintainer fields remain server-owned and are preserved by delivery.
The sole theorem proof remains `sorry`; no theorem was proved in this reading.

Verification: `scompile.py NL lem-cbc-simplicial-groupoid-localization
lean/Sheaf/CategoryTheory/SimplicialGroupoidLocalization.lean`, run from the
sandbox, passed both its sandbox and library-path compiles (35.8 s and 30.7 s),
with no errors or warnings. I checked that `lean.statement` equals the source
signature verbatim and that all Lean lines satisfy the 100-character limit.
