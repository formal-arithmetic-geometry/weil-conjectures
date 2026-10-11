## Worker report

The module `Sheaf.CategoryTheory.GrothendieckAbelian.AcyclicQuotientComplexesBoundedSize`
states `CochainComplex.exists_cardinal_acyclic_subcomplex_and_coproduct_quotient`.
Its only proof is `sorry`. No definitions, new nodes, dependency replacements, or statement
corrections were necessary.

Hypothesis and clause correspondence:
- The arbitrary Grothendieck abelian category is `{C : Type u} [Category.{v} C]
  [Abelian C] [IsGrothendieckAbelian.{v} C]`. Object and hom universes are independent;
  this is the hom-universe convention explicitly recorded by def-sp-grothendieck-abelian.
- Size is exactly `Cardinal.mk (Shrink.{v} (Subobject X))`. Well-poweredness permits the
  small model without altering subobject cardinality. This is the expression already
  used by the recorded bounded-size dependency; no second size definition is introduced.
- The cardinal chosen once for the whole category is `∃ κ : Cardinal.{v}` before
  `∀ M : CochainComplex C ℤ`. Thus it does not depend on the complex or degree.
- Acyclicity of the arbitrary cochain complex is the implication hypothesis `M.Acyclic`.
- Clause (1) has exactly the condition `¬ IsZero M`; its subcomplex is represented by
  `∃ (N : CochainComplex C ℤ) (ι : N ⟶ M), Mono ι`. A monomorphism of complexes is
  degreewise monic, hence represents a subcomplex, without requiring chosen inclusions.
  The remaining clauses are `¬ IsZero N`, `∃ b : ℤ, N.IsStrictlyLE b`, `N.Acyclic`, and
  `∀ n : ℤ, Cardinal.mk (Shrink.{v} (Subobject (N.X n))) ≤ κ` respectively.
- Clause (2) is `∃ (I : Type v) (F : I → CochainComplex C ℤ) (π : ∐ F ⟶ M), Epi π`.
  In the abelian category of complexes this is a degreewise surjection. For every `i : I`
  it requires an independently chosen upper bound `∃ b : ℤ, (F i).IsStrictlyLE b`,
  acyclicity `(F i).Acyclic`, and the same cardinal bound in every integer degree.
  No common upper bound, nonzero summand condition, or bound on the number of summands
  is imposed. The two clauses are joined by conjunction for each acyclic M.

Dependencies read and used:
- `def-sp-grothendieck-abelian`: Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic,
  `CategoryTheory.IsGrothendieckAbelian` (including small colimits and well-poweredness).
- `lem-pur-kinjective-set-iso-classes-bounded-size`:
  Sheaf.CategoryTheory.BoundedSubobjectSize,
  `CategoryTheory.bounded_subobject_size_quotient_and_small_iso_classes`.
  Imported its module and used its exact subobject-size convention. The quotient and
  small-isomorphism-class assertion itself is not a premise of this lemma.
- `def-pc-cochain-complex-modules`: Mathlib.Algebra.Homology.HomologicalComplex,
  `CochainComplex`, specialized to the arbitrary abelian category as the item explicitly asks.
- `def-pc-acyclic-complex-modules`: Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex,
  `HomologicalComplex.Acyclic`, likewise specialized to C.
- Mathlib.Algebra.Homology.Embedding.CochainComplex, `CochainComplex.IsStrictlyLE`:
  terms above the bound are zero objects, not merely vanishing cohomology.
- Mathlib.Algebra.Homology.HomologicalComplexLimits provides coproducts of complexes;
  Mathlib.Algebra.Homology.HomologicalComplexAbelian supplies their abelian structure.

Source checked: the local literature checkout does not contain injectives.tex, so opened
https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex directly,
Lemma `lemma-acyclic-quotient-complexes-bounded-size` and its full proof. Both clauses
agree with the node, including the absence of a nonzero requirement in clause (2).
The docstring includes the cardinal construction, descending kernel-lifting induction,
nonzero specialization, and generator-indexed coproduct argument, naming the DAG nodes
used at each step.

Edge cases checked before writing:
- For the zero complex clause (1) is vacuous; clause (2) permits the empty coproduct.
- The zero Grothendieck category is allowed and imposes no nonzero witness requirement.
- Upper bounds can be any integer, with no bounded-below or common-upper-bound assumption.
- The indexing type can be empty or infinite. `Type v` is the small-set convention for
  this Grothendieck category, and includes the set of maps from a generator to all integer
  degrees, so does not restrict the source construction.
- `IsZero` rather than literal equality to a chosen zero object captures categorical zero;
  replacing it with object equality would incorrectly exclude isomorphic zero objects.

Searches for an existing statement (actual service results logged in searches.jsonl):
- LeanFinder: "Every acyclic complex in a Grothendieck abelian category is a quotient of
  a coproduct of bounded above acyclic complexes of uniformly bounded subobject cardinality".
  Eight hits about Grothendieck categories of complexes, injective dimensions and homotopy
  acyclicity; none asserts either bounded-size clause.
- Loogle: `HomologicalComplex.Acyclic, CategoryTheory.IsGrothendieckAbelian`:
  available, zero hits.
- Mathlib grep via msearch: `bounded.*size|acyclic.*quotient` under CategoryTheory:
  only a conical-product docstring, no matching theorem.
- LeanSearch: "An acyclic complex in a Grothendieck abelian category contains bounded
  above acyclic subcomplexes with uniformly bounded cardinality of subobjects and is a
  quotient of their direct sum"; service outcome recorded in searches.jsonl.
- Direct rg of WeilConjectures and lean/Sheaf for `bounded.*size|acyclic.*quotient` and
  this node id: no upstream theorem; the project has KInjectiveCriterion, whose h_sub
  and h_quot assume precisely these clauses, and KInjectiveDegreewiseExistence, whose
  proof cites this item. Neither proves or states the existence assertion itself.
- Direct rg for the proposed full declaration name in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no collision.

Validation: server single-file compilation succeeded cleanly (1.3 s). The delivery
preflight and server recompilation are run by deliver2.py --no-push before handoff.
No STATEMENT-DISPUTED issue found.

## Second reading by C1

I independently opened the node copy and the delivered Lean module, all four statement
dependency nodes and their recorded declarations, and the Stacks source. No statement
correction, new definition node, or dependency module is present or required.

The local checkout lacks `injectives.tex`. I read the original source at
[Stacks injectives.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex),
including `definition-size`, `lemma-set-iso-classes-bounded-size`, the surrounding
Grothendieck-category assumptions, and
`lemma-acyclic-quotient-complexes-bounded-size` with its proof. This section assumes an
arbitrary Grothendieck abelian category, with no geometric, ring, or finiteness restriction.

Object/hypothesis/conclusion inventory and correspondence (H3):

- Category A: `{C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C]`. Verdict: exact. In
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`, the recorded
  `CategoryTheory.IsGrothendieckAbelian` supplies a separator, exact filtered colimits,
  and (by its `hasColimits` instance) small colimits. The node explicitly records this
  hom-universe convention; no extra category instance is demanded.
- Object size: `Cardinal.mk (Shrink.{v} (Subobject X))`. Verdict: exact cardinality of
  subobjects, as in the dependency's
  `CategoryTheory.bounded_subobject_size_quotient_and_small_iso_classes` in
  `Sheaf.CategoryTheory.BoundedSubobjectSize`. `wellPowered` supplies the small model;
  shrinking is an equivalence, not a replacement by a smaller set of subobjects.
- One cardinal for the category: `∃ κ : Cardinal.{v}` precedes `∀ M` and both clauses.
  Verdict: exact; the bound cannot depend on M, a degree, or a summand.
- Arbitrary integer cochain complex: `∀ M : CochainComplex C ℤ`. Verdict: exact.
  The recorded `CochainComplex` in `Mathlib.Algebra.Homology.HomologicalComplex` is
  `HomologicalComplex C (ComplexShape.up ℤ)`, with terms and square-zero differentials
  raising degree. Its morphisms commute with the differentials. The dependency's
  module specialization is intentionally replaced by A, as the item's text requires.
- Acyclicity hypothesis: `M.Acyclic →`. Verdict: exact. The recorded
  `HomologicalComplex.Acyclic` in
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` means exactness in every
  degree, equivalent in this abelian category to zero homology in every degree.
- Clause (1), conditional on nonzero M: `¬ IsZero M →`. Verdict: exact; categorical
  zero, not equality with a chosen representative of the zero object.
- Clause (1), subcomplex: `∃ (N : CochainComplex C ℤ) (ι : N ⟶ M), Mono ι`.
  Verdict: exact representation up to isomorphism. A mono of complexes is degreewise
  mono: evaluation preserves kernels/limits, and monos are normal in this abelian
  category. Conversely `HomologicalComplex.mono_of_mono_f` gives a mono from
  degreewise monos. Thus there is no weaker embedding condition.
- Clause (1), nonzero N: `¬ IsZero N`. Verdict: present exactly.
- Clause (1), bounded above: `∃ b : ℤ, N.IsStrictlyLE b`. Verdict: exact.
  `CochainComplex.isStrictlyLE_iff` in
  `Mathlib.Algebra.Homology.Embedding.CochainComplex` identifies this with
  `∀ i > b, IsZero (N.X i)`, not merely vanishing homology.
- Clause (1), acyclicity and all degree bounds: `N.Acyclic` and
  `∀ n : ℤ, Cardinal.mk (Shrink.{v} (Subobject (N.X n))) ≤ κ`.
  Verdict: both are present, with the original single cardinal and every integer degree.
- Clause (2), family and surjection: `∃ (I : Type v)
  (F : I → CochainComplex C ℤ) (π : ∐ F ⟶ M), Epi π`. Verdict: exact.
  `HomologicalComplexLimits` constructs colimits degreewise and evaluation preserves
  them. In the abelian category of complexes, normal epis are therefore degreewise
  epis; `epi_of_epi_f` supplies the converse. The coproduct is the source's direct sum.
- Clause (2), every summand: `∀ i : I, (∃ b : ℤ, (F i).IsStrictlyLE b) ∧
  (F i).Acyclic ∧ ∀ n : ℤ,
  Cardinal.mk (Shrink.{v} (Subobject ((F i).X n))) ≤ κ`.
  Verdict: exact. Each summand has its own upper bound; no common bound, nonzero
  condition, cardinal bound on I, or bounded-below condition was added.
- Both conclusions hold for each acyclic M: the conjunction lies after `M.Acyclic →`.
  Verdict: exact order and simultaneous assertions.

Edge cases: the zero complex makes only clause (1) vacuous; clause (2) allows an empty
family and the empty coproduct. A zero Grothendieck category is allowed. Subobjects of
zero still have cardinality one, not zero; the existential cardinal is unrestricted and
can accommodate this. The integer degree zero and negative degrees are included; no
characteristic or scheme hypothesis occurs, so categories arising from empty schemes
are not excluded. Object universe u is independent of hom universe v. `I : Type v`
suffices because the source construction indexes by all maps from a generator to terms
of M: the sigma type over integer degrees of these hom sets is v-small, including v = 0.
Thus no larger indexing universe is needed to witness the existential conclusion.

Independent searches (H4), using queries different from the first worker's:

- LeanFinder via msearch: "An exact cochain complex admits an epimorphism from a direct
  sum of bounded above exact complexes with uniformly small subobject lattices".
  Eight hits, including CM5b factorizations and IsLE/IsGE exactness lemmas; none states
  this cardinal-existence theorem or its two conclusions.
- Loogle via msearch: `CochainComplex.IsStrictlyLE, HomologicalComplex.Acyclic`.
  Successful response, zero hits.
- Mathlib grep via msearch: `subcomplex.*cardinal|cardinal.*subcomplex|acyclic.*coproduct`.
  Successful response, zero hits.
- Direct rg across Mathlib CategoryTheory and Algebra/Homology, WeilConjectures, and
  project lean/Sheaf: `acyclic.{0,50}(cardinal|size|quotient)`,
  `exact.{0,40}complex.{0,40}bounded`, and `bounded.{0,40}subobject`.
  Read upstream `CochainComplex.exists_acyclic_degreewiseCardinalGenerated_le` in
  `AcyclicSwallowing.lean`: it uses a fixed regular cardinal, a generator, and generated
  subobjects, and does not assert bounded-above complexes or a subobject-size bound.
  It is not this statement. Project `KInjectiveCriterion.lean` assumes the two clauses
  instead of establishing the existence of κ; its signatures agree with this delivery.
  `KInjectiveDegreewiseExistence.lean` cites this item in its proof, without duplicating it.
- Searched the proposed declaration and node id in the source, project modules, and
  `dag/lean_names_upstream.json`; no duplicate declaration was found.

H5/H6/H8/H9: there are no definitions or private notions. The only theorem proof is
`sorry`. Module and theorem docstrings name the source and blueprint id. The proof
narrative follows all four node steps: generator/cardinal construction, initial images
and descending kernel-lifting induction using the bounded-size-surjection node, the
nonzero specialization, and the generator-indexed coproduct epimorphism. Every variable
and universe is bound. Lines are at most 100 characters. Imports provide the recorded
size convention, strict term bounds, acyclicity, coproducts, and the abelian structure.
The node's `lean.statement` was compared byte-for-byte with the file signature and agrees.

Mismatches and repairs: none. I preserved the correct module, signature, and node copy;
only this independent second-reading report was added. No unit statement issue or
STATEMENT-DISPUTED issue was found.

Validation: the supplied scompile.py compiled the single delivered module on the server
cleanly in 1.3 seconds, exit code 0, with no warnings. The required deliver2.py dry run
and actual delivery follow this reading.
