## Worker report

The module `Sheaf.CategoryTheory.DGModuleSemiFreeReplacement` states
`CategoryTheory.RightDGModule.exists_semiFree_replacement`, with `sorry` as its
only postponed proof. All supporting definitions contain real data or actual
predicates. These helpers spell out the dg-module and semi-free conventions
introduced in this node's own statement; they do not state another DAG theorem.
The module imports no other unpublished DAG node.

Source checked: Drinfeld, [*DG quotients of DG categories*](https://arxiv.org/pdf/math/0210114),
§14.8, printed pp. 36–37 (PDF pp. 36–37), including the reference to Lemma 13.3.
That paragraph states semi-free replacement for dg categories, and the same
paragraph and §14.9 explicitly allow right modules. I also read the local
Stacks `dga.tex`, `lemma-resolve` (Tag 09KP), as the one-object comparison.
The theorem docstring gives the cycle-generator/kill-kernel construction in
natural language, so the empty `proof` array of the supplied node does not
leave the eventual prover without a proof plan.

Clause matching:

- Size: the recorded `def-weil-size-convention` is a metatheoretic convention,
  with `lean.convention: true` and no declaration/module to import. The file
  declares `universe u v` explicitly. `B : Type u` is an arbitrary set of objects;
  complexes and coefficients use `max u v`, containing the object set and all
  degrees and generator indexing types. No finiteness, boundedness, or
  nonemptiness assumption is imposed. Lifted integer coefficients
  `ULift.{max u v, 0} ℤ` are the canonical copy of the integers in that universe;
  modules over them are precisely abelian groups. This avoids the pinned
  Mathlib monoidal API's requirement that the coefficient and module universes
  coincide, without bounding the cardinality of the objects by a smaller
  coefficient universe.
- Small dg category: `DGModuleCategory B` abbreviates Mathlib's
  `EnrichedCategory DGModuleComplexᴹᵒᵖ B`. `DGModuleComplex` is Mathlib's
  `CochainComplex (ModuleCat ...) ℤ`. Thus the differential has degree +1 and
  square zero, and the units and associative compositions are actual chain
  maps with proved laws in the structure. `MonoidalOpposite` reverses only
  tensor order, not arrows: `dgModuleComp U V W` has source
  `B(V,W) ⊗ B(U,V)`. This is the usual `b a` composition and needs no Koszul
  braiding or extra sign. `dgModuleComplexMonoidal` is exactly the existing
  upstream monoidal instance, exposed under the complex abbreviation.
- Right dg module: `RightDGModule.obj` is the family of complexes;
  `RightDGModule.action U V` is the chain map
  `M(V) ⊗ B(U,V) → M(U)`. Its `unit` and `assoc` fields are equations, hence
  proofs of the stated laws, rather than unconstrained proposition-valued data.
  `Hom.app` consists of chain maps, and `Hom.action` imposes their module
  linearity. There is no implicit choice of a module structure.
- Cohomology and quasi-isomorphism: `IsAcyclic` uses Mathlib's `ExactAt` in
  every object and integer degree, and `Hom.IsQuasiIso` uses `QuasiIso` at
  every object. In an abelian module category these say respectively that the
  kernel/image cohomology vanishes and that its induced maps are isomorphisms;
  no private definition of cohomology is made.
- Representables: `dgModuleHom U V` is the actual hom complex, and
  `representableAct` evaluates the actual composition on a homogeneous pure
  tensor. These are the complexes and actions of `B(-,V)`, not arbitrary
  modules carrying a predicate that they are representable.
- Shifts and free quotients: `FreePresentation.index`, `vertex` and `shift`
  specify an arbitrary family of shifted representables. Its `equiv U r`
  is a linear equivalence from the actual Mathlib direct sum
  `⨁ j, B(U,vertex j)^(r + shift j)` to the module term. Its `differential`
  field imposes exactly `(-1)^(shift j)` times the old differential on each
  summand; its `action` field imposes the unchanged right action, expressed
  by `representableAct`. Equality of integer degree expressions is transported
  using `Int.add_right_comm`; this transport has no sign. Checking the
  equations on each summand suffices by the direct sum universal property.
  Thus a free presentation is precisely a dg-module isomorphism from the
  coproduct of the specified shifts. It adds no chosen basis to the theorem:
  the presentation is existential under `IsSemiFree`.
- Graded splitting: `GradedHom r` is a family of linear maps of degree `r`
  satisfying the unsigned rule `f(m a) = f(m) a`. `SemiFreeFiltration.retraction`
  and `split` provide a degree-zero module retraction of each successor map;
  they impose no chain-map condition on the retraction.
- The filtration: `step` and `inclusion` give dg modules embedded into `P`;
  `inclusion_injective` imposes degreewise injectivity. `successor` and
  `compatible` identify these embeddings as an increasing sequence.
  `zero` says every degree of stage zero is the zero module, and `exhaustive`
  says every homogeneous element of `P(U)` lies in a stage. This is exactly
  the union condition, without requiring an extra arbitrary colimit object.
- Quotients: `quotient` and `projection` provide the actual quotient through
  a surjective dg-module map; `exact` says its kernel is the image of the
  successor inclusion, objectwise in every degree. The injection and these
  two conditions identify it uniquely up to dg-module isomorphism with
  `P_(i+1)/P_i`. `free` supplies its free presentation.
- Final assertion: for arbitrary `M`, the two existential binders produce
  `P` and the actual dg-module map `q : Hom P M`. `IsSemiFree P ∧ q.IsQuasiIso`
  is exactly the two requested properties. There are no extra hypotheses or
  stronger conclusions such as degreewise surjectivity, functoriality, or
  homotopical projectivity.

The preliminary prose also describes the Hom complex and homotopically
projective modules. Those notions are context for the sibling theorem
`lem-coef-dg-semi-free-homotopically-projective`; neither occurs in this item's
existential assertion, and this module does not assert that sibling theorem or
introduce a second Hom-complex construction. The graded module-map convention
that is needed here is explicitly present in `GradedHom`.

Dependency interfaces inspected: the entire `lean` record of
`def-weil-size-convention`; Mathlib `CategoryTheory.EnrichedCategory`
(`Mathlib.CategoryTheory.Enriched.Basic`), `MonoidalOpposite`
(`Mathlib.CategoryTheory.Monoidal.Opposite`), `CochainComplex`,
`HomologicalComplex.ιTensorObj`, `HomologicalComplex.QuasiIso`,
`HomologicalComplex.ExactAt`, `ModuleCat`, `DirectSum.lof`, and the upstream
`instMonoidalCategoryHomologicalComplexIntUp_weilConjectures`
(`WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex`). Their
source signatures and relevant docstrings were read. The latter source was
also checked with `scompile.py --source`.

Edge cases checked: the empty dg category requires no object or nonempty
instance; the zero module and zero successive quotients are allowed; the free
index type may be empty; shifts and cohomological degrees range over all
integers, including zero and negative integers; the filtration starts at zero
and allows arbitrary plateaus; complexes are unbounded. Graded splittings are
module splittings, not merely splittings of abelian groups. There are no
characteristic restrictions: the coefficient ring is the integers. All module
laws and all quotient and splitting conditions are actual equations or
injectivity/exactness assertions.

Searches performed with the prescribed `msearch.py` wrapper (recorded in
`searches.jsonl`):

- LeanFinder: “Every right differential graded module over a small dg category
  admits a semi-free resolution by shifts of representables”. Eight hits,
  including `ModuleCat.projectiveResolution` and the ordinary
  `ProjectiveResolution` API; no dg-category module or semi-free replacement.
- Loogle: `"EnrichedCategory"`. Twelve hits; `EnrichedCategory` is the exact
  underlying enriched-category structure and is reused. None states the
  desired resolution theorem or defines right dg modules.
- Mathlib grep: `dg.?module|semi.?free|homotopically.?projective`. Zero hits.
- LeanSearch: “A right module over a small differential graded category admits
  a semi-free replacement with a filtration whose quotients are sums of
  shifted representables”. Eight hits: ordinary module filtrations and
  projective resolutions, no exact match.
- `rg` on the project's upstream `WeilConjectures`, side `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the chosen declaration names, dg modules,
  semi-freeness, and the item's blueprint id found no existing declaration.
  The DAG search finds this node and the related resolution/model-structure
  theorem nodes, not a separate recorded definition of these modules.

No statement correction or disputed mathematical assertion was needed. The
supplied repository copy has `status: "unsplit"`, despite the stage-2 dispatcher
brief's general claim that assigned items are split; the delivery preserves
that maintainer-owned field. The node copy changes only `lean`.

Resumed-worker verification (2026-10-16 UTC): reread the complete node and the
size-convention dependency, inspected the enriched-category and cochain
monoidal interfaces, and checked Drinfeld §14.8 against the filtration and
existence assertion. The earlier sandbox draft needed no mathematical change.
The module now sets `autoImplicit false`, enforcing the explicit-binder rule.
Repeated LeanFinder search for “Every right dg module over a small dg category
has a semi-free replacement by a quasi-isomorphism” returned only ordinary
module and derived-category results, not this theorem. Repeated Loogle
`"EnrichedCategory"` confirmed the reused enrichment API; direct source searches
again found no pre-existing dg-module or semi-free replacement declaration.
The final `scompile.py` check passed cleanly against the current library with
`autoImplicit false` enabled: sandbox elaboration took 22.5 seconds and library
compilation took 18.8 seconds. The node's recorded signature matches the file
verbatim; the only postponed proof is the named replacement theorem.

## Second reading by NM

I independently read the node, the complete delivered module, the
`def-weil-size-convention` dependency and its convention-only Lean record,
`coord/brief-stage2.md`, and delivery-errors H. No maintenance repair note is
present for this item. There are no new nodes or dependency modules in this
packet to review under H12/H13.

Source verification: I opened [Drinfeld, DG quotients of DG categories]
(https://arxiv.org/pdf/math/0210114), including the opening conventions,
§§13.1–13.3, 14.1, 14.4, and 14.7–14.9 (printed pp. 32–37). The ground ring
is an arbitrary commutative ring and categories are small by convention;
taking the ground ring to be Z is the node's stated specialization. Section
14.8 gives the free-quotient exhaustive filtration and replacement theorem;
§14.1 identifies right modules with modules over the opposite dg category.
I also read the local Stacks `dga.tex`, `lemma-resolve` (Tag 09KP), and its
property-(P) discussion. These impose no field, boundedness, finiteness or
nonempty-object assumption. The graded splitting in the node agrees with the
free-quotient convention: shifted representables are projective as graded
modules, so these quotient sequences split after forgetting differentials.

Independent object/hypothesis/conclusion checklist, with the Lean file open:

1. Chosen size bounds and a set of objects: `universe u v`, `B : Type u`,
   and complexes in `max u v`. Verdict: exact within the chosen enlarged
   bound. `ULift.{max u v, 0} ℤ` changes the size of the integer carrier, not
   the coefficient ring up to its canonical isomorphism. Every abelian group
   has the unique module structure over this copy of Z. No relation between
   the originally chosen object and module bounds is assumed; `max` permits
   both. The size-convention node explicitly has no declaration to import.
2. Hom complexes and dg-category structure: `DGModuleComplex` is the actual
   Mathlib cochain-complex type, and `DGModuleCategory` is the actual
   `EnrichedCategory` in its monoidal opposite. I read
   `Enriched/Basic.lean`'s `Hom`, `id`, `comp`, `id_comp`, `comp_id`, and
   `assoc` fields. `dgModuleHom` and `dgModuleComp` unwrap this structure.
   Verdict: exact. The monoidal opposite reverses tensor order and keeps
   morphisms covariant; composition has source `B(V,W) ⊗ B(U,V)`, with
   genuine chain maps and their unital associative laws.
3. Right dg module: `RightDGModule.obj`, `action`, `unit`, and `assoc`
   give precisely `M(V) ⊗ B(U,V) → M(U)` with both required equations.
   `Hom.app` is an objectwise chain map and `Hom.action` is compatibility
   with the action. Verdict: exact; no implicit or arbitrarily supplied
   replacement action is hidden in the statement.
4. Objectwise cohomology, acyclicity and quasi-isomorphisms:
   `IsAcyclic` uses `(M.obj U).ExactAt r`, and `Hom.IsQuasiIso` uses
   `QuasiIso (f.app U)` for every U. I read the Mathlib definitions in
   `ShortComplex/HomologicalComplex.lean` and `QuasiIso.lean`.
   Verdict: these are zero kernel/image cohomology and isomorphisms on that
   cohomology in the abelian category of modules, respectively.
5. Representables: `dgModuleHom U W` is B(U,W), and `representableAct`
   applies the actual `dgModuleComp` to a homogeneous pure tensor.
   Verdict: composition gives the actual representable action; there is no
   independent predicate claiming an arbitrary family is representable.
6. Shifts and coproducts of representables: `FreePresentation.index`,
   `vertex`, `shift`, and `equiv U r` identify the degree-r term with the
   actual Mathlib direct sum of B(U,vertex j) in degree `r + shift j`.
   `differential` multiplies each summand's differential by
   `(shift j).negOnePow`; `action` uses unchanged `representableAct`.
   Verdict: exact. The differential target `r + 1 + shift j` equals
   `(r + shift j) + 1`, and the action's sole cast identifies
   `(p + shift j) + q` with `(p + q) + shift j`. No Koszul sign is introduced
   in that cast. Linearity and the direct sum universal property extend
   the displayed summand equations to all elements, so the degreewise
   equivalences constitute precisely the required dg-module isomorphism.
7. Graded module maps: `GradedHom r` gives linear maps from degree p to
   degree `p + r`; its `action` imposes unsigned `f(ma) = f(m)a`.
   Verdict: exact. Its HEq only identifies equal integer degrees.
   The node's preliminary Hom-complex differential and homotopical
   projectivity describe context for its sibling theorem; neither occurs
   in this item's existence assertion or in the definition of semi-free.
   The module does not replace those contextual notions by a weaker one or
   claim to state the sibling theorem. No missing Hom-complex dependency is
   needed to type this item.
8. Increasing dg submodules starting at zero:
   `SemiFreeFiltration.step`, `inclusion`, `inclusion_injective`,
   `successor`, `compatible`, and `zero` embed the stages into M and
   identify their nested images. Verdict: exact. In particular, successor
   maps are injective because their composites with the next injective
   inclusion equal the preceding injective inclusion. `Subsingleton` of
   stage-zero module terms means the zero module, not a zero morphism.
9. Exhaustive union: `exhaustive U r m` requires every homogeneous element
   of M to be in some stage. Verdict: exact. Because stages are nested,
   a finite collection of homogeneous elements lies in a common stage.
10. Graded splitting: `retraction i : GradedHom ... 0` and `split` require
    a left inverse to the successor map in the category of graded modules.
    Verdict: exact; there is no chain-map condition on this retraction and
    the splitting is module-linear, not merely additive.
11. Successive quotients: `quotient`, `projection`,
    `projection_surjective`, and `exact` specify a surjective dg-module map
    with kernel the image of the successor inclusion at every object and
    degree. `free i` gives its `FreePresentation`.
    Verdict: exact. These conditions identify the actual quotient up to
    dg-module isomorphism; they do not allow an unrelated free object.
12. Final quantifiers and clauses: for every `M : RightDGModule B`,
    `exists_semiFree_replacement` gives `∃ P, ∃ q : Hom P M,
    IsSemiFree P ∧ q.IsQuasiIso`. `IsSemiFree` is existence of the preceding
    filtration. Verdict: exactly the node's assertion, with the same
    direction of q and no extra surjectivity, functoriality, cofibrancy,
    or homotopical-projectivity conclusion.

Edge-case review: B may be empty, so all objectwise laws may be vacuous
without excluding the unique empty module. A zero module and empty free
index type are permitted. Quotients may be zero and stages may repeat.
The filtration starts at index 0 and is indexed by all natural numbers;
all shifts and complex degrees are integers, including 0 and negative
integers. No boundedness or characteristic assumption is present. The free
index universe `max u v` contains the object/degree/element indexing families
needed by the countable construction, and integer lifts impose no cardinality
bound on the module carriers beyond the declared universe. Schemes, empty
schemes and geometric dimension hypotheses do not enter this algebraic node.

Independent duplicate searches (all wrapper results recorded in
`searches.jsonl`):

- LeanFinder: "A differential graded presheaf has a cellular resolution
  with graded split stages and representable cells". Eight hits concerning
  ordinary projective/injective resolutions and `CochainComplex.IsKProjective`;
  none is a right dg-category-module semi-free replacement.
- Loogle: `"EnrichedCategory", "Module"`. No hits. I independently read the
  existing enrichment class and used it in the checklist above.
- Mathlib grep: `SemiFree|semi[Ff]ree|DGModule|[Dd][Gg].?[Pp]resheaf|[Cc]ellular`.
  One irrelevant hit in the bibliography of abstract CW complexes.
- LeanSearch: "An unbounded enriched presheaf on a differential graded category
  has a resolution filtered by shifted Yoneda modules". Eight hits for
  ordinary resolutions, Yoneda/sheaf constructions and ind-objects; no match.
- Direct `rg` over Mathlib, upstream `WeilConjectures`, this project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json` used `DGModule`, `SemiFree`,
  `semi.?free`, `dgModule`, `differential.?graded`, `enriched.*module` and
  `module.*enriched`. The only side-library prose hits were Koszul complexes
  and an unrelated extension lemma. I read the returned ordinary K-projective
  definition: it concerns complexes in an abelian category, not modules
  over a dg category. The DAG search found the related theorem nodes, whose
  Lean records are absent, and no independently recorded definition node
  supplying these notions. There is no existing declaration to bind instead.

H5–H9 check: the helpers contain actual complex/module data or predicates;
there is no data chosen from a sorry existence theorem. The sole postponed
proof is the named `exists_semiFree_replacement`, whose source/blueprint
and cycle-generation, kernel-killing, countable-union and splitting proof
plan are in its docstring. All declarations have the source/blueprint
markers. No proof was filled, no local notation/private helper was added,
all lines are at most 100 characters, and `autoImplicit false` leaves no
unbound variable or universe. The recorded `lean.statement` agrees verbatim
with the theorem signature up to its proof delimiter.

Mathematical mismatches found: none; no signature or node statement changed.
The dry run refreshed against the current server base and reported a newer
stage-1 proof (ten elementary steps), which is absent from the older read-only
shared checkout. I read that current node in the wrapper's worktree and matched
all ten steps to the same construction. I expanded the theorem's proof docstring
to include those ten steps explicitly, including the differential-square,
Leibniz, chain-map, graded-splitting, union and cohomology calculations.
This repairs the documentation gap relative to the newly split proof without
altering the mathematical assertion. The wrapper preserves the maintainer's
new proof, proof dependencies and review fields rather than copying the stale
sandbox fields. The required command
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NM
lem-coef-dg-module-semi-free-replacement
lean/Sheaf/CategoryTheory/DGModuleSemiFreeReplacement.lean` passed cleanly
for both sandbox elaboration (10.8 s) and module compilation (10.5 s),
with no errors or warnings. Delivery dry-run and push follow this review.
