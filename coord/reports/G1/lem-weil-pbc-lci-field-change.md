## Worker report

The module `Sheaf.RingTheory.LocalCompleteIntersectionFieldChange` states
`Algebra.isLocalCompleteIntersection_fieldChange`, with its sole proof `sorry`.
It states both finite type of the scalar extension and equivalence of the two local
complete-intersection conditions. No new definitions, dependency modules, or statement
corrections are needed.

Hypotheses and clauses matched to Lean:
- Fields k and K: `(k : Type u) (K : Type v) [Field k] [Field K]`.
- Ring homomorphism iota making K a k-algebra: `[Algebra k K]`; its ring homomorphism
  is `algebraMap k K`. Every unital ring homomorphism between the fields determines
  such an algebra structure, so this is the same data and imposes no extra condition.
- Commutative k-algebra S: `(S : Type w) [CommRing S] [Algebra k S]`.
- S finite type over k: `[Algebra.FiniteType k S]`.
- The specified tensor product is `S ⊗[k] K`, without swapping its factors.
- Its K-algebra structure through lambda ↦ 1 ⊗ lambda is explicitly installed by
  `letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := S) (B := K)`.
  Read Basic.lean lines 485–510: `right_algebraMap_apply` gives precisely this map.
- Finite type over K: `∃ h : Algebra.FiniteType K (S ⊗[k] K), ...`.
  The witness is installed as an instance by `letI := h`, because the recorded local
  complete-intersection definition takes finite type as an instance parameter.
  FiniteType is Prop-valued; this existential packaging is equivalent to the finite-type
  clause conjoined with the subsequent equivalence, with no choice of extra data.
- Both directions: `IsLocalCompleteIntersection k S ↔
  IsLocalCompleteIntersection K (S ⊗[k] K)` under that same K-algebra structure.

Dependency declarations read and used:
- `def-weil-pbc-finite-type-algebra`: Mathlib leaf `Algebra.FiniteType`,
  `Mathlib.RingTheory.FiniteType`, class signature and docstring at lines 36–40.
- `def-weil-pbc-complete-intersection-over-field`:
  `Sheaf.RingTheory.CompleteIntersectionOverField`,
  `Algebra.IsLocalCompleteIntersection` (full definition and docstring read, lines 39–48),
  built from its companion `Algebra.IsGlobalCompleteIntersection` (lines 26–38).
  The former is exactly the principal-open cover definition with global complete
  intersections in the localizations, and requires the finite-type instance.

Source check: local literature/stacks-project/algebra.tex is absent on this machine.
Read the full statement and proof at https://stacks.math.columbia.edu/tag/00SJ,
Lemma 10.135.11, instead. The node agrees with the source; the additional explicit
finite-type conclusion follows from the base-changed presentation. The module docstring
carries all five steps of the node's proof, including the conormal identification,
localization and fibre dimensions, ascent, and descent by Nakayama.

Edge cases checked: S may be the zero ring; its spectrum is empty, and the existing
LCI definition admits the empty principal-open cover. The tensor product is then the
zero ring too. No Nontrivial S assumption is imposed. Identity field extensions,
algebraic and transcendental extensions, inseparable extensions, and all characteristics
are allowed. No finite-dimensional or separability assumption occurs. Empty polynomial
variable/equation families are allowed by the dependency definition. The three universe
parameters are explicit and independent; there is no quantification over test objects
in a smaller universe that could make the statement vacuous.

Searches made for an existing statement (actual calls recorded in searches.jsonl):
- LeanFinder through msearch.py: "a finite type algebra over a field is a local complete
  intersection if and only if its scalar extension to an extension field is".
  Eight hits, concerning smoothness, standard smoothness, and unramified algebras;
  none states this LCI equivalence.
- Loogle through msearch.py: "Algebra.IsLocalCompleteIntersection".
  Zero hits; identifier unknown to the Mathlib search service.
- Mathlib grep through msearch.py: `CompleteIntersection|lci_field_change|lciFieldChange`
  under RingTheory. Zero hits.
- LeanSearch through msearch.py: "local complete intersection algebra invariant under
  field extension". Service unavailable (Internal Server Error); no verdict from it.
- rg of the source repository WeilConjectures and dag/lean_names_upstream.json for
  `CompleteIntersection`, `IsLocalCompleteIntersection`, and the proposed theorem name:
  no hits. rg for the item's id in WeilConjectures: no hits.
- rg of lean/Sheaf for complete-intersection declarations: the existing dependency
  definitions plus fraction-field models, subalgebras, and relative-global-intersection
  modules; no declaration of field-change invariance. Those definitions are reused.

Server single-file compilation via scompile.py: exit code 0, compiled in 1.4 seconds,
without errors or warnings. All variables and universes are explicitly bound.
No statement fault or disputed statement found.

## Second reading by G1

Independent reading of the node, the delivered module, both statement-dependency nodes,
and the declarations they record. Verdict: the Lean says exactly what the node says.
No mathematical or signature mismatch was found; the module and node record are unchanged.
This section is the only delivery content added by the second reader.

Source checked directly in Stacks `algebra.tex`, fetched into the item's scratchpad from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex:
section `section-lci`, lines 35804–35831 (standing conventions and Definition 00S9),
and `lemma-lci-field-change`, lines 36262–36353 (Lemma 00SJ and its full proof).
Also read the preceding local version, lines 36204–36259. The source assumes fields
and a finite type algebra; Noetherianity in the proof is a consequence, not an additional
hypothesis. The extra finite-type conclusion of the node follows from the induced
polynomial presentation in the source. The online tag pages 00SJ and 00S9 agree.

Object/hypothesis/conclusion checklist, written from the node before matching:

- Fields k and K: `(k : Type u) (K : Type v) [Field k] [Field K]`. Exact.
- Ring homomorphism iota from k to K: `[Algebra k K]`, whose map is `algebraMap k K`.
  Exact data: for commutative fields any unital ring homomorphism defines this algebra
  structure, with scalar multiplication by its image. No injectivity, separability,
  algebraicity, or finite-degree condition is added; injectivity follows for fields.
- Commutative k-algebra S: `(S : Type w) [CommRing S] [Algebra k S]`. Exact, including
  the zero ring. No domain, reducedness, nontriviality or smoothness assumption.
- S finite type over k: `[Algebra.FiniteType k S]`. Exact. Opened the class in
  `Mathlib.RingTheory.FiniteType` (lines 36–40) and its polynomial-surjection
  characterization `Algebra.FiniteType.iff_quotient_mvPolynomial''` (lines 174–182).
  These match `def-weil-pbc-finite-type-algebra`; no private definition.
- Scalar extension S tensor_k K: `S ⊗[k] K`, with the factors in the node's order.
  Exact. The statement installs `Algebra.TensorProduct.rightAlgebra` explicitly.
- K-algebra map lambda to 1 tensor lambda: the same `rightAlgebra` instance. Exact.
  Opened `Mathlib.RingTheory.TensorProduct.Basic`, lines 485–508;
  `right_algebraMap_apply` identifies this precise map, so the LCI and finite-type
  expressions use the intended coefficient structure, including when k = K = S.
- First conclusion, finite type over K: `∃ h : Algebra.FiniteType K (S ⊗[k] K)`.
  Exact. This is a conclusion, not an assumed instance. Since this class is a Prop,
  `letI := h` simply makes that proved clause available to the following predicate.
  Proof irrelevance prevents dependence on a choice of finite-type witness.
- Second conclusion, both directions of LCI: `IsLocalCompleteIntersection k S ↔
  IsLocalCompleteIntersection K (S ⊗[k] K)` after installing h. Exact; neither
  direction omitted and no existential choice of coefficient map. Objects and
  algebra structures are fixed before either conclusion.
- The LCI notion: opened all of `Sheaf.RingTheory.CompleteIntersectionOverField`,
  including `Algebra.IsGlobalCompleteIntersection` and `Algebra.IsLocalCompleteIntersection`.
  Compared with `def-weil-pbc-complete-intersection-over-field` and source 00S9:
  quotient polynomial presentation, integer codimension represented by `c ≤ n`
  and natural subtraction, zero-ring convention, principal-open cover, and
  `Localization.Away` all agree. A set of elements expresses the same covers as
  an indexed family (use its range; repetitions are immaterial). Exact dependency.

Edge cases: S = 0 is allowed, its spectrum and an admissible covering set are empty,
and its scalar extension is zero. The global-intersection dependency explicitly
admits `Subsingleton T`. Empty equation and variable families (`Fin 0`), including
n = c = 0, are allowed by that dependency. No nonempty index condition is introduced.
Identity, transcendental, infinite-degree and inseparable extensions are covered in
all characteristics. Fields themselves cannot be zero, as in the source. Independent
universes u, v, w are explicitly bound; tensor products live in the required maximum
universe. There is no quantification over test objects in a smaller universe.

Independent searches (different wording from the worker; msearch calls logged in
searches.jsonl):

- LeanFinder: "complete intersection descends and ascends along arbitrary extensions
  of coefficient fields". Eight hits on standard smoothness and smooth descent;
  none states LCI field-change invariance.
- Loogle: `"intersection"`. Twelve returned hits concern intersections of ranges,
  not complete-intersection algebras; no usable candidate.
- LeanSearch: "local complete intersection property preserved and reflected by
  scalar extension of fields". Unavailable (Internal Server Error); no verdict
  inferred from an unavailable service.
- `rg` across all Mathlib, source WeilConjectures, and repository lean/Sheaf for
  `complete[_ ]intersection`, `local.*intersection`, `IsLCI`, and
  `lci.*(base|field|tensor)`, plus the names `CompleteIntersection`, `fieldChange`
  and `field_change` and dag/lean_names_upstream.json. Mathlib has only the
  presentation-dimension comment, and the source has no LCI field-change theorem.
  Opened the project's field-subalgebra and fraction-field-model theorem signatures
  and the relative-global-intersection definition: none duplicates this statement.
  The existing complete-intersection dependency is reused. No existing statement found.

H5/H6/H8/H9: no definitions are added, no data is supplied by sorry, and the sole
theorem proof remains `by sorry`. The module and declaration docstrings cite 00SJ
and the item's blueprint id. The declaration docstring follows all five node steps:
presentation and finite type; exact conormal base change; localization/dimension and
residue-field fibres; ascent via the conormal criterion; descent via a prime above
each prime and Nakayama. Both imports are used, namespace and topic conventions hold,
and every variable/universe is bound. No new nodes, dependency modules or statement
correction are part of this delivery, so H12/H13 and correction-citer review do not arise.

Compilation: reran scompile.py with the sandbox module's absolute path. Exit code 0,
compiled in 1.3 seconds, no errors or warnings. The initial relative-path invocation
failed before compiling because it resolved against the read-only repository; using
the actual sandbox path fixed that invocation. The node's lean.statement remains
verbatim equal to the module signature. No statement is disputed and no repair needed.
