## Worker report

The module `Sheaf.CategoryTheory.PresheafNaiveFibrationWhitehead` states
`CategoryTheory.Presheaf.naiveFibration_whitehead`, with its only proof `sorry`.
It defines no new notions. The earlier sandbox draft duplicated two definitions;
this completion removes them and imports their now-landed owning module,
`Sheaf.AlgebraicTopology.PresheafCylinderModelRecognition`.
Only the item's `lean` record changes. No new nodes, dependency modules, or
statement corrections are needed.

Source checked: [Cisinski, Higher Categories and Homotopical Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
Example 2.4.10, Definition 2.4.11 (An0--An2), Definitions 2.4.14 and 2.4.18,
Proposition 2.4.17, and Lemmas 2.4.27--2.4.28, printed pp. 53--61.
The module docstring carries the source and the theorem docstring reproduces all
fourteen proof steps from the DAG. The source's Lemma 2.4.28 is exactly the
criterion here; its trivial fibrations lift against all monomorphisms.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Input universe: `universe u`. The small category is `{A : Type u}
  [SmallCategory A]`, with presheaves `Aᵒᵖ ⥤ Type u`. All testing targets and
  the generating class and transfinite composition indices use `u`. The type
  of the presheaf category itself may live in a larger universe.
- Interval and terminal presheaf: `(I : Aᵒᵖ ⥤ Type u)` and
  `(e₀ e₁ : ⊤_ (Aᵒᵖ ⥤ Type u) ⟶ I)`. The boundary is the actual coproduct
  arrow `coprod.desc e₀ e₁`, monic by `hδ`. No extra endpoint assumption is added.
- Pushout product: Mathlib's
  `(Functor.PushoutObjObj.ofHasPushout prod.functor i j).ι`. Its point is
  `(V × K) ⨿[U × K] (U × L)`, and its two component maps give the canonical
  arrow to `V × L`. This uses the existing canonical construction.
- The class `An` is a `MorphismProperty`. The hypothesis `hAn` supplies
  `∃ G`, `IsSmall.{u} G`, and `G ≤ monomorphisms`, precisely a small set of
  generating monomorphisms. It includes `G ≤ An`, `isomorphisms ≤ An`,
  `An.IsStableUnderCobaseChange`, `IsStableUnderTransfiniteComposition.{u} An`,
  and `An.IsStableUnderRetracts`. Its last universal clause says `An ≤ P`
  for every class `P` containing `G` and isomorphisms with those closure
  properties. This is the least closure, not just a closed containing class.
  Cobase change is invariant under every isomorphic pushout square, so it
  also supplies closure under isomorphisms of arrows. `IsSmall` is smallness
  of the set of actual arrows, as in its Mathlib docstring and
  `isSmall_iff_eq_ofHoms`.
- The first interval axiom is `hEnd`: for every `j` with `Mono j`, its two
  conjuncts put `e₀ □ j` and `e₁ □ j` in `An`, covering both endpoints.
- The second axiom is `hBoundary`: for every `i` with `An i`, put `δ □ i`
  in `An`. It is retained although the expanded proof needs only `hEnd`.
- A map's naive fibrancy is exactly Mathlib's `An.rlp`. Its definition
  quantifies over every arrow of `An` and requires `HasLiftingProperty`,
  namely a diagonal for every commutative square.
- The map and codomain assumptions are `{X Y} (p : X ⟶ Y)`,
  `hp : An.rlp p`, and `hY : An.rlp (terminal.from Y)`. Source fibrancy
  is derived in the planned proof, never added as an assumption.
- Homotopy classes use the already-landed
  `CategoryTheory.Presheaf.intervalHomotopy`. Its full definition is
  `Relation.EqvGen` of pairs of endpoint restrictions of a map `K × I ⟶ Z`.
  Thus it is precisely equality modulo the generated equivalence relation,
  even when the direct homotopy relation is not itself an equivalence.
- The already-landed `CategoryTheory.Presheaf.intervalWeakEquivalences`
  tests every `Z : Aᵒᵖ ⥤ Type u` with `An.rlp (terminalIsTerminal.from Z)`.
  Its first conjunct says every `a : X ⟶ Z` is homotopic to some `p ≫ b`,
  exactly surjectivity of precomposition on classes. Its second says
  homotopic `p ≫ b₀` and `p ≫ b₁` imply homotopic `b₀` and `b₁`, exactly
  injectivity. Precomposition preserves the generating endpoint relation
  by precomposing a homotopy with `p × id`, so these clauses characterize
  bijectivity of the canonical induced map without assuming fibrancy of
  its source. `terminal.from` and `terminalIsTerminal.from` are the same
  canonical terminal arrow.
- The conclusion is exactly `intervalWeakEquivalences e₀ e₁ An p ↔
  (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp p`. Both directions
  are present. There is no model-structure hypothesis, chosen model
  structure, or appeal to the imported model-recognition theorem.

Dependency declarations and imports read:

- `def-weil-size-convention`: its record is `existing: true`,
  `convention: true`, with null declaration/module, and instructs each
  consumer to state its universe hypotheses directly. `universe u` and
  the bounds listed above implement it; there is no module to import.
- `CategoryTheory.Presheaf.intervalHomotopy` and
  `CategoryTheory.Presheaf.intervalWeakEquivalences`, full signatures and
  docstrings at lines 55--77 of
  `Sheaf.AlgebraicTopology.PresheafCylinderModelRecognition`, recorded in
  `lem-coef-presheaf-cylinder-model-recognition`'s `lean.declarations`.
  They already express the notions explicitly introduced by this item.
- `Functor.PushoutObjObj.ofHasPushout` and `.ι`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj`, lines 73--102;
  `MorphismProperty.IsSmall` and `isSmall_iff_eq_ofHoms`,
  `Mathlib.CategoryTheory.MorphismProperty.IsSmall`, lines 30--58;
  `MorphismProperty.rlp`, `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`,
  lines 34--38; and the closure classes in `MorphismProperty.Limits`,
  `TransfiniteComposition` and `Retract`, including their full field signatures.
  These are available through the public import of the existing owning module.

Import-cycle note for the maintainer and second reader: cylinder recognition
has this item as a proof dependency, and its existing module owns the two
notions that this item must reuse. The present import is for those definitions
alone. Under stages/2-statements.md section 3 rule 7, omit the reverse proof
import `PresheafCylinderModelRecognition → PresheafNaiveFibrationWhitehead`,
which would close a two-module cycle. This item has no proof dependencies.
No reverse DAG statement dependency is added: the notions are explicitly
introduced in this item's own statement, and no new independent notion is
needed. A future stage-3 reorganization can move the shared definitions to
a lower module with the owning node's review; no live file is changed here.

Edge cases checked: an empty category `A` is allowed, and no object of `A`
is selected. Empty presheaves, empty generating families and empty sources
of lifting squares are not excluded. Empty Hom sets are allowed by both
clauses of the testing definition. Identity and isomorphism cases agree
with the criterion. For the terminal indexing category, a two-element
interval and `An = monomorphisms`, naive fibrations are surjections and
naive fibrant targets are nonempty sets. The criterion then agrees with
lifting against all injections. The empty-to-nonempty arrow fails `hp`,
so it is not a counterexample. For empty `A`, monicity of the boundary is
still the exact condition; no artificial inequality of endpoints is added.
No node fault or statement dispute was found.

Searches checked and refreshed:

- `msearch.py leanfinder`: "A naive fibration of presheaves to a naive fibrant
  object is an interval homotopy weak equivalence if and only if it lifts
  against every monomorphism". Eight hits: the Kan model's lifting
  characterization, fibrant/bifibrant full-subcategory transport, model-category
  Whitehead results and precomposition bijectivity. These require a model
  structure or an already specified weak-equivalence predicate, so none
  states this generic interval criterion.
- `msearch.py loogle`: `CategoryTheory.MorphismProperty.rlp,
  CategoryTheory.HasLiftingProperty`. One hit,
  `MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty`, the singleton
  lifting characterization, not this theorem.
- `msearch.py grep`: `naive.*fibr|Cisinski|interval.*homotopy`, in
  `CategoryTheory`. Zero hits.
- The earlier attempt's logged `msearch.py leansearch` query about weak naive
  fibrations with fibrant targets returned eight model-category hits led by
  `HomotopicalAlgebra.ModelCategory.cm4a`; none was an exact match.
- Fresh `rg` on upstream `WeilConjectures/`, side `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for
  `naive.*[Ff]ibr|presheaf.*[Ww]hitehead|intervalHomotopy|intervalWeakEquivalences|naiveFibration_whitehead`:
  no upstream theorem or name collision; side search found the existing
  cylinder-recognition helpers, now reused, and discussion references.
  The prescribed upstream node-id grep found no occurrence.
- Read `Bifibrant.lean`'s `FibrantObject.weakEquivalence_homMk_iff` and
  `JoyalTrick.lean`'s dual Joyal-trick signature: they transport a supplied
  predicate or assume model-category factorization/lifting data, respectively.

Validation: the revised module compiled cleanly through `scompile.py Q25
lem-coef-presheaf-naive-fibration-whitehead`, including the side-only owning
module overlay and both sandbox and library-path checks (0.9--1.1 seconds
each). No warnings were reported. The node's `lean.statement` is verbatim
from `theorem` through the signature before `:=`, and its UTC date is
2026-10-17. The required delivery dry run is the final check; its result
is reported when handing this packet to the second reader.

## Second reading by Q25

I independently opened the shared node, sandbox node and Lean file, the recorded
size dependency, and the current source of the imported cylinder-recognition
module (`scompile.py --source`). There is no maintenance repair note for this
item. The only node field changed by this delivery is `lean`; there are no new
nodes, dependency modules, or `statement_change` to review. No mismatch was
found, and I retained the statement, module and existing worker report.

The actual source is [Cisinski's book](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
not a Stacks tag. I read Section 2.4's standing assumptions, Example 2.4.10,
Definitions 2.4.11, 2.4.14 and 2.4.18, and Lemmas 2.4.24, 2.4.27 and 2.4.28.
They supply the interval setting, lifting and homotopy notions used by the node.
The product cylinder supplies its contraction through the terminal map. No
additional assumption from the source is missing. The closure formulation of
An0 agrees with the node's weak saturation of a small generating set.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

| Node item | Lean rendering and independent verdict |
| --- | --- |
| Fixed input universe; small ordinary category A | `universe u`, `{A : Type u} [SmallCategory A]`. PASS: Mathlib's `SmallCategory A` is exactly `Category.{u} A`; this is the same signature as the owning helpers' `[Category.{u} A]`, with no additional structure. |
| Category of set-valued presheaves | `Aᵒᵖ ⥤ Type u`. PASS: both objects and arrows of A, values, generators and tests use the input universe, while the presheaf category may itself live in `u+1`. |
| Terminal presheaf, interval I, endpoints e0 and e1 | `(I : Aᵒᵖ ⥤ Type u) (e₀ e₁ : ⊤_ (Aᵒᵖ ⥤ Type u) ⟶ I)`. PASS: the terminal object is the categorical one, not a freely supplied object. |
| Monic boundary delta from the coproduct of terminals | `(hδ : Mono (coprod.desc e₀ e₁))`. PASS: the coproduct desc is the specified boundary; endpoint distinctness is not imposed independently. |
| The specified canonical pushout-product arrow | `(Functor.PushoutObjObj.ofHasPushout prod.functor i j).ι`. PASS: I opened Mathlib's structure, `ofHasPushout` and the definition of `ι`; its domain and both maps to `V × L` are exactly the node's pushout. |
| An is the least weakly saturated class generated by a small set of monos | `hAn : ∃ G, IsSmall.{u} G ∧ G ≤ monomorphisms _ ∧ G ≤ An ∧ isomorphisms _ ≤ An ∧ ...`. PASS: the remaining conjunctions are cobase-change, small transfinite-composition and arrow-retract closure. The final universally quantified `P` clause asserts leastness, with precisely these same closure conditions. I checked the full Mathlib class fields, including arbitrary pushout squares and `RetractArrow`. Closure under isomorphic arrow presentations follows from cobase-change closure. `IsSmall` concerns actual arrows and is equivalent to a family indexed by `Type u`, as required for a small generating set. |
| Endpoint axiom for every mono and both endpoints | `hEnd : ∀ {K L} (j : K ⟶ L), Mono j → An (... e₀ j).ι ∧ An (... e₁ j).ι`. PASS: no generating-only restriction, and both endpoints occur. |
| Boundary axiom for every anodyne map | `hBoundary : ∀ {K L} (i : K ⟶ L), An i → An (... (coprod.desc e₀ e₁) i).ι`. PASS: retained exactly, even though the expanded proof uses the endpoint axiom. |
| Right lifting means every square has a diagonal; naive fibrant maps and objects | Mathlib's `An.rlp` and `HasLiftingProperty`. PASS: I opened `rlp`; it quantifies over all arrows in An. Object fibrancy is this property of the unique terminal arrow. |
| Homotopy classes generated by restrictions of maps K times I to Z | Imported `Presheaf.intervalHomotopy`. PASS: I read its complete body: `Relation.EqvGen` applied to an existential `h : Limits.prod K I ⟶ Z`, with both endpoint equations using the unique map to the terminal presheaf. This is the generated equivalence relation, without an assumed direct-homotopy equivalence. |
| W tests bijectivity of precomposition on these classes into every naive fibrant Z | Imported `Presheaf.intervalWeakEquivalences e₀ e₁ An`. PASS: `∀ Z : Aᵒᵖ ⥤ Type u, An.rlp (terminalIsTerminal.from Z) → ...`; its first conjunct is surjectivity on classes, and its second is injectivity. Precomposition sends an endpoint witness to the witness precomposed with `p × id`, so it descends to the generated equivalence relation. Thus the two clauses describe the canonical induced map exactly. |
| An arbitrary p:X to Y, p naive fibrant and Y naive fibrant | `{X Y : Aᵒᵖ ⥤ Type u} (p : X ⟶ Y) (hp : An.rlp p) (hY : An.rlp (terminal.from Y))`. PASS: there is no extra assumption on X. `terminal.from Y` and the helpers' `terminalIsTerminal.from Y` are the same canonical terminal morphism. |
| Equivalence with lifting against every mono, without a model structure | `intervalWeakEquivalences e₀ e₁ An p ↔ (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp p`. PASS: both implications and the universal mono class are present. There is no model-category binder or invocation of the imported recognition theorem. |

I also opened the size-convention node's full record: it is explicitly a
metatheoretic convention with no module or declaration, implemented by these
universe binders. The imported helpers are already recorded in the recognition
node's `lean.declarations`; their signatures agree with its natural statement.
They introduce no hidden instances beyond the stated category and available
presheaf limits. No missing notion or unusable dependency requires an addition.
Recognition has this item as a proof dependency; the documented stage-2 rule 7
exception therefore omits its reverse proof import. Using its existing helper
definitions here neither assumes recognition nor creates an import cycle.

Edge cases were checked without adding hypotheses. Empty A is admitted:
there is one presheaf up to unique isomorphism, and every relevant square has
its unique filler. Empty generating families and empty presheaves are admitted;
the interval axioms themselves determine when such a family is possible.
For nonempty A the initial presheaf is not artificially declared fibrant:
the endpoint lifting tests still apply to it. No `Nonempty` instance is added
to A, X, Y, the generating family, or any Hom set. There is no zero object in
general, and the initial and terminal cases are both covered. For A terminal,
the two-point interval and An equal to all injections give surjections as
naive fibrations and nonempty sets as fibrant objects; the criterion has its
expected set-theoretic meaning. No degree, n, scheme, ring or characteristic
occurs. All universe parameters are bound; tests X and Y and all finite
products used in the proof remain in the declared input universe.

Independent searches used different wording from the first worker:

- LeanFinder through `msearch.py`: "Right lifting property against monomorphisms
  of a presheaf naive fibration equivalent to bijective interval homotopy class
  tests on fibrant objects". Eight hits, including Kan lifting criteria,
  model-category homotopy precomposition and Joyal's trick. None is this
  criterion for the given An and interval without a model structure.
- Loogle through `msearch.py`:
  `CategoryTheory.HasLiftingProperty, CategoryTheory.MorphismProperty.rlp`.
  The one hit is `rlp_ofHoms_iff_hasLiftingProperty`, a constant-family lifting
  equivalence, not the present theorem.
- LeanSearch through `msearch.py`: "A fibration between fibrant presheaves is
  a trivial fibration if and only if precomposition induces bijections on
  interval homotopy classes into every fibrant presheaf". Eight hits about
  supplied model-category trivial fibrations, none defining or recognizing
  this presheaf interval testing class.
- `msearch.py grep` for `strong.*deformation|homotop.*equiv.*fibr|fibr.*homotop.*equiv`
  in `AlgebraicTopology/ModelCategory`: no hits. I also ran `rg` over Mathlib's
  CategoryTheory and AlgebraicTopology trees for naive fibrations, Cisinski and
  interval homotopy, with no match for this statement. Searches of upstream
  `WeilConjectures/`, project `lean/Sheaf/`, and `dag/lean_names_upstream.json`
  for naive fibrations, presheaf Whitehead, both helper names and the proposed
  theorem name found only the existing project helpers and discussion in their
  consumers. The prescribed upstream item-id search found no occurrence.
- I opened the returned `RightHomotopyClass.precomp_bijective_of_weakEquivalence`
  and `ModelCategory.hasLiftingProperty_of_joyalTrickDual` in Mathlib. They need
  supplied model or factorization structures and do not replace this statement.

H5/H6/H8/H9 checks: the file declares only the theorem and its whole proof is
`sorry`; it defines no data and proves nothing. Both docstrings carry the source
and this item's blueprint id. I checked all fourteen proof steps against the
node: homotopy equivalence into fibrant targets, source fibrancy, the two
homotopy-Yoneda calculations, correction to a section, the three-face filler
over Y, arbitrary mono lifting, and the converse section/homotopy calculation
are all present in order. Every line is at most 100 characters; there is no
private copy, file-local notation, unbound variable or name collision.
`lean.statement` was checked byte-for-byte against the theorem signature up
to `:= by`. No statement correction or disputed flag is needed.

Validation: I compiled the only delivered module with the prescribed
`scompile.py Q25 lem-coef-presheaf-naive-fibration-whitehead` command.
The sandbox and library-path compiles both passed without diagnostics
(1.2 and 1.1 seconds). Second reading changes only this report.
The prescribed `deliver2.py --no-push` then reported
`OK (dry run): commit a661569832 passes the preflight and compiles; nothing pushed`.
