## Worker report

The module `Sheaf.Paper.PbcQbarIdempotentComplete` states
`AlgebraicGeometry.Scheme.pbcQbarIdempotentComplete`, with its whole proof `sorry`.
It uses the actual raw rational finite-stage pair category of the recorded
`def-weil-pbc-qbar-category`, without taking a Karoubi envelope in its definition.
The module and theorem docstrings cite the blueprint node at order 1542 and give
all five steps of the node's natural-language proof. No other DAG node is stated,
no definition is introduced, and only this item's `lean` field changes.

Hypothesis and clause correspondence (the hypotheses are those explicitly fixed
in the category definition and in proof step 1 of this node):

- A prime ell: `(l : ℕ) [Fact l.Prime]`.
- Q_l and its chosen algebraic closure: `(Qbar : Type w) [Field Qbar]
  [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]`. This is the same
  `Padic l` as the dependency's notation `ℚ_[l]`.
- The scheme T: `(T : Scheme.{u})`.
- Noetherian: `[IsNoetherian T]`.
- Finite dimension: `[hDim : Fact (∃ n : ℕ,
  topologicalKrullDim T ≤ (n : WithBot ℕ∞))]`, exactly the recorded category API.
- Ell invertible on T: `[hInv : Fact (∀ t : T,
  IsUnit (l : T.presheaf.stalk t))]`, exactly the recorded category API.
- The category Dbc(T,Qbar) = P_T: every occurrence is the recorded
  `pbcQbarCategory l Qbar T`; its abbreviation unfolds to the actual
  `PbcFiniteStagePairCategory l Qbar T hDim.out hInv.out`.
- Idempotent completeness: `IsIdempotentComplete (pbcQbarCategory l Qbar T)`.
  The Mathlib class quantifies over every idempotent endomorphism and asks for
  an object and two arrows with both splitting equations.
- The canonical functor to the envelope is `toKaroubi (pbcQbarCategory l Qbar T)`:
  it sends X to (X,identity) and f to f, rather than an arbitrary equivalence.
- Fully faithful: the conjunction of that functor's `.Full` and `.Faithful`,
  i.e. surjectivity and injectivity on every Hom set.
- Equivalence: the same functor's `.IsEquivalence`.
- Exact: the same functor's `.IsTriangulated`, using the upstream canonical
  `.CommShift ℤ` and the upstream retract pretriangulation. Its definition is
  preservation of distinguished triangles for that shift comparison. Thus the
  equivalence and exactness clauses concern the same specified functor.

Dependency declarations read and used:

- `Sheaf.Paper.PbcQbarCategory`:
  `AlgebraicGeometry.Scheme.pbcQbarCategory` and its existing instances,
  including `pbcQbarTriangulated`. The entire module was read, including its
  concrete specialization and all scheme/coefficient binders.
- `Mathlib.CategoryTheory.Idempotents.Karoubi` (recorded Mathlib match for
  `def-weil-karoubi-envelope`): `CategoryTheory.Idempotents.Karoubi` and
  `CategoryTheory.Idempotents.toKaroubi`, with their objects, morphism relation,
  identity, composition, and full/faithful instances.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  `Mathlib.CategoryTheory.Triangulated.Triangulated`, and
  `Mathlib.CategoryTheory.Triangulated.Functor` (the recorded Mathlib match for
  `def-weil-triangulated-category`): `CategoryTheory.Pretriangulated`,
  `CategoryTheory.IsTriangulated`, and `CategoryTheory.Functor.IsTriangulated`.
  Full signatures and defining fields were read. These are imported transitively
  through the two public imports, rather than duplicated.
- `WeilConjectures.CategoryTheory.Idempotents.Triangulated` and its public
  `Pretriangulated`/`Shift` imports supply the exact canonical retract structure:
  `CategoryTheory.Idempotents.Karoubi.pretriangulated`,
  `CategoryTheory.Idempotents.toKaroubi.commShift`, and
  `CategoryTheory.Idempotents.toKaroubi.isTriangulated`. Their source and
  `Karoubi.mem_distTriang_iff` were checked, so exactness has the intended meaning.
- The stated proof dependency `Sheaf.Paper.PbcFilteredRetractDescent` is a
  proof-only import, using its declaration
  `AlgebraicGeometry.Scheme.pbcFilteredRetractDescent` in the proof plan.
  `Sheaf.Paper.FiniteStagePairCategory` and `Sheaf.Paper.PbcVerdierAxioms`
  already enter through the public category dependency. Mathlib's
  `fullyFaithfulToKaroubi` is available through the envelope import.
  The unrecorded finite-stage Karoubian and envelope-triangulated DAG nodes
  are not restated here. The upstream envelope structure is already available.

Edge cases checked before writing:

- The empty scheme is allowed: no nonemptiness or point is chosen; invertibility
  is the source's pointwise condition, hence vacuous on the empty scheme.
- Dimension zero is included by the existential finite bound; no positive bound
  or fixed dimension is imposed.
- Identity and zero idempotents, including the zero object, are covered by the
  unrestricted `IsIdempotentComplete` quantification. No nonzero object or arrow
  is assumed. All objects of the envelope, including zero formal summands, occur
  in the equivalence assertion.
- The prime 2 is allowed; no oddness condition or coefficient characteristic
  restriction beyond the given prime and its invertibility is added.
- The base finite stage and repeated stages remain part of the unchanged pair
  category; no strict field inclusion is required.
- The scheme universe `u` and closure universe `w` are bound independently, as
  in the recorded category. No extra universe equality or smallness hypothesis
  is added. All variables and universes in the new theorem are explicit.

Searches for an existing statement:

- `msearch.py leanfinder`, query "The finite coefficient pair category of bounded
  constructible Qbar l complexes is idempotent complete and its Karoubi inclusion
  is an exact equivalence": 8 hits, all generic Karoubi/complex equivalences;
  none concerns the specified Qbar pair category.
- `msearch.py loogle`, query
  `CategoryTheory.IsIdempotentComplete, CategoryTheory.Idempotents.toKaroubi`:
  4 hits. `toKaroubi_isEquivalence` assumes idempotent completeness; it cannot
  state the whole item, whose first conclusion establishes that property.
  Its source and signature were read in `Karoubi.lean`.
- `msearch.py grep`, query
  `pbcQbar.*[Ii]dempotent|[Ii]dempotent.*[Qq]bar|toKaroubi_isEquivalence`:
  1 hit, the same conditional Mathlib equivalence instance.
- `msearch.py leansearch`, query "The category of bounded constructible Qbar l
  adic complexes is idempotent complete": 8 generic hits concerning splitting,
  abelian categories, homological complexes, functor categories, equivalences,
  and the Karoubi envelope itself. None proves the item for the raw pair category.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf`, for
  `qbar.*[Ii]dempotent|[Ii]dempotent.*[Qq]bar|Qbar.*[Kk]aroub|[Kk]aroub.*Qbar`
  and the proposed name `pbcQbarIdempotentComplete`: no hits.
- Upstream search for `thm-weil-pbc-qbar-idempotent-complete`: no hits.
  `dag/lean_names_upstream.json` also has no match for that id.
- Searches for canonical Karoubi exactness located the existing upstream
  `CategoryTheory/Idempotents/{Shift,Pretriangulated,Triangulated}.lean`.
  Their declarations are reused, including the retract distinguished-triangle
  characterization, rather than creating another notion of exactness.

The blueprint node source and its unit `_section.md` were opened. The statement
agrees with the node and its inherited category hypotheses; there is no statement
correction, new node, dependency repair, or STATEMENT-DISPUTED issue.

Validation: `scompile.py Q36 thm-weil-pbc-qbar-idempotent-complete` compiled
the delivered module cleanly, with no errors or warnings. The wrapper compiled
each required side dependency separately, then checked both sandbox and library
module paths. The recorded signature was checked using `stage2_delivery.py
signature`; only the node field `lean` differs, and no Lean line exceeds 100
characters. The required `deliver2.py --no-push` dry run is the final check.

## Second reading by Q36

I independently read the item node and its blueprint source at
`sec-smooth-purity/sk-prop-sf-cbc/thm-weil-pbc-qbar-idempotent-complete.md`
(order 1542), the unit `_section.md`, all three statement-dependency nodes,
and the recorded source declarations. The Lean says exactly what the node says.
No statement, definition, import, or proof-docstring repair was needed; this
second reading adds this report only. The node has no `statement_change`, and
there are no new nodes or dependency modules to review.

Object, hypothesis and conclusion checklist, in source order:

1. A prime ell, Q_l, and a chosen algebraic closure Qbar: `(l : ℕ)
   [Fact l.Prime] (Qbar : Type w) [Field Qbar] [Algebra (Padic l) Qbar]
   [IsAlgClosure (Padic l) Qbar]`. These are exactly the binders of
   `pbcQbarCategory`; `Padic l` is the dependency's `ℚ_[l]`. PASS.
2. A scheme T: `(T : Scheme.{u})`, with independent bound universes `w u`.
   No scheme over a field, separation or finite-type structure is assumed. PASS.
3. The inherited noetherian hypothesis: `[IsNoetherian T]`. The category node
   explicitly requires it, as does the theorem node's proof step 1. PASS.
4. Finite dimension: `[hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤
   (n : WithBot ℕ∞))]`. This is existence of a finite natural bound, exactly
   the category API, rather than a fixed dimension or positive bound. PASS.
5. Ell invertible on T: `[hInv : Fact (∀ t : T,
   IsUnit (l : T.presheaf.stalk t))]`. This is the inherited pointwise
   invertibility condition; there is no extra characteristic restriction. PASS.
6. The particular category Dbc(T,Qbar) = P_T: every conclusion uses
   `pbcQbarCategory l Qbar T`. Its definition is precisely
   `PbcFiniteStagePairCategory l Qbar T hDim.out hInv.out`, itself the
   `PairCategory` of the actual `pbcScalarSystem`. I read `pbcStageCategory`,
   `pbcScalarExtension`, `pbcScalarAssociator`, and `pbcScalarSystem` in
   `Sheaf.Paper.FiniteStagePairCategory`, and `PbcRationalCategory` in
   `Sheaf.Paper.PbcRationalCategory`. The stages are raw scalar localizations
   of bounded constructible complete integral complexes. Upstream
   `StageSystem.tr`, `PairCategory`, `Rep` and `Rep.Rel` implement the specified
   associator transport and eventual equality of common-stage arrows.
   In particular no envelope or arbitrary stage system replaces P_T. PASS.
7. Every idempotent splits: `IsIdempotentComplete (pbcQbarCategory l Qbar T)`.
   I read `IsIdempotentComplete.idempotents_split` in Mathlib's
   `CategoryTheory/Idempotents/Basic.lean`: it quantifies over every X and e,
   assumes exactly `e ≫ e = e`, and gives S, i, p with `i ≫ p = 𝟙 S`
   and `p ≫ i = e`. PASS.
8. The canonical fully faithful functor to the specified envelope: all four
   functor clauses use the same `toKaroubi (pbcQbarCategory l Qbar T)`.
   Mathlib's `Karoubi` has objects (X,e), morphism equation `e ≫ f ≫ d = f`,
   identity e and inherited composition; `toKaroubi` sends X to (X,identity)
   and f to f. `.Full ∧ .Faithful` is exactly full faithfulness. PASS.
9. Equivalence: that very functor's `.IsEquivalence`, with no arbitrary
   replacement equivalence. Mathlib's existing conditional instance requires
   completeness, so does not already state this whole theorem. PASS.
10. Exactness: that very functor's `.IsTriangulated`. I read Mathlib's
    `Functor.IsTriangulated.map_distinguished`, the upstream
    `toKaroubi.commShift`, `Karoubi.distinguishedTriangles`,
    `Karoubi.pretriangulated`, `Karoubi.mem_distTriang_iff`, and
    `toKaroubi.isTriangulated`. The comparison is the canonical identity on
    underlying shifted objects, and the envelope triangles are retracts of
    images of distinguished triangles. In the domain,
    `pbcQbarTriangulated` uses `pbcVerdierAxioms`; its inherited
    `qbarPairPretriangulated` uses the unique structure characterized by
    the common-stage distinguished predicate. Thus this clause is exactness
    for the triangulations named by the node. PASS.

Source check: the tag table identifies 09SF/09SH/05QV in `homology.tex`
(lines 507–588) and 05QW in `derived.tex` (lines 805–823), which I read.
09SH assumes preadditivity and gives equivalent Karoubian criteria. 05QV
assumes countable products and split-epi kernels, or the dual hypotheses;
05QW assumes a pretriangulated category and countable products or coproducts.
These are background criteria, not additional hypotheses for this blueprint
node: its source note explicitly distinguishes its finite-stage descent proof.
The Lean correctly adds none of those countability assumptions. The node's
scheme assumptions come from `def-weil-pbc-qbar-category` and are all explicit.

Edge cases: the empty scheme is allowed (the invertibility condition is then
vacuous); dimension zero and the empty-space Krull dimension satisfy a finite
bound; zero objects and both zero and identity projectors are covered by the
unrestricted idempotent quantifier. Ell = 2 is included, and no oddness or new
field-characteristic assumption occurs. No arbitrary index set or n-level is
introduced by this theorem; the finite-stage poset contains the base field
and repeated stages are allowed. Scheme and closure universes remain
independent, with no smallness or universe equality imposed.

Independent searches, using words different from the worker's main query:

- `msearch.py leanfinder`: "Splitting projectors in the rational l-adic finite
  coefficient colimit and equivalence of the canonical idempotent envelope
  inclusion" returned eight Dold–Kan/projector results, none this statement.
- `msearch.py leansearch`: "The rational constructible l-adic coefficient
  colimit category is Karoubian" returned generic Karoubi constructions,
  completeness of the envelope, and equivalences conditional on completeness.
- `msearch.py loogle '"toKaroubi_isEquivalence"'` returned the single generic
  instance assuming `[IsIdempotentComplete C]`; its full signature and source
  were read, so it cannot replace the present completeness conclusion.
- `msearch.py grep 'IsIdempotentComplete|toKaroubi'` returned generic
  Dold–Kan uses. Independent `rg -n -i` over Mathlib's category theory,
  upstream `WeilConjectures`, project `lean/Sheaf`, and the upstream name map
  for `pbcQbarIdempotentComplete`, `qbar.{0,50}(idempoten|karoub)`, and
  `idempoten.{0,50}(qbar|filtered)` found no existing item declaration.
  The single project hit was unrelated ind-etale ring idempotent splitting.

H5–H9 check: this delivery introduces no definition. Its sole theorem has
exactly `by sorry`; both docstrings cite the source and blueprint id. The
proof docstring follows all five current node steps, including finite-stage
splitting, the canonical inclusion, essential surjectivity, the explicit
additive quasi-inverse and exactness. The stated proof dependency
`pbcFilteredRetractDescent` was opened and is imported; the finite-stage
Karoubian and envelope-triangulation nodes have no recorded Lean declarations.
The available upstream canonical envelope structure is reused. No unbound
variable, file-local notation, private notion, duplicate declaration or line
longer than 100 characters occurs. The node's `lean.statement` was compared
with the file signature verbatim and agrees.

Validation by the second reader: `scompile.py Q36
thm-weil-pbc-qbar-idempotent-complete` with the absolute sandbox module path
compiled both the sandbox and library module forms successfully (4.8 seconds
each), with no errors or warnings. The initial relative-path invocation was
reissued with the absolute sandbox path because the module is intentionally
absent from the read-only shared repository.
