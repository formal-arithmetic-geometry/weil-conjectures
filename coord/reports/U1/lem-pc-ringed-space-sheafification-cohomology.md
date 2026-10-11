## Worker report

The module `Sheaf.AlgebraicGeometry.RingedSpaceSheafificationCohomology` states
`AlgebraicGeometry.RingedSpace.sheafification_cohomology`, with a single `sorry`.
No definitions are duplicated, no node statement is corrected, and no new nodes or
dependency modules are needed. The cohomology presheaf described within this node's
statement is expressed as an existential functor with its defining natural factorization;
thus its construction and descent are asserted, rather than assumed as new hypotheses.

Hypotheses and clauses, in order:

- A ringed space is `(X : RingedSpace.{u})`. Its module category is
  `SheafOfModules.{u} (moduleRings X)`, using the shared ring-sheaf carrier.
- The chosen derived category is `DerivedCategory` with
  `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]`. The latter chooses
  the localization and its morphism universe; it is not a mathematical extra assumption
  (the standard localization exists). There are no boundedness assumptions.
- The integer degree is `(q : ℤ)`, including negative degrees.
- The functorial K-injective choice is exactly
  `CochainComplex.kInjectiveResolutionFunctor.{u}` from the derived-direct-image
  dependency, with Grothendieck structure `RingedSpace.moduleGrothendieckAbelian`.
- `∃ P : DerivedCategory ... ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})` asserts the
  cohomology-over-opens functor. The following `Nonempty (DerivedCategory.Q ⋙ P ≅ ...)`
  identifies its values AND maps with replacement, forgetting to abelian presheaves,
  termwise application via `Functor.mapHomologicalComplex`, and degree-q
  `HomologicalComplex.homologyFunctor`. Homology in a functor category is computed
  objectwise: its value at `op U` is precisely `H^q(Γ(U,I(K)))`; its restriction maps
  are induced by restriction in the resolution. This natural factorization encodes
  both formulas for complexes and chain maps and descent through localization.
- `∃ e : P ⋙ presheafToSheaf ... ≅ DerivedCategory.homologyFunctor ... q ⋙
  SheafOfModules.toSheaf ...` is the sheafification identification. It is an isomorphism
  of FUNCTORS, so includes naturality in every derived morphism, not merely a family
  of unrelated object isomorphisms. The target is the underlying abelian sheaf of the
  module cohomology sheaf, matching the Ab-valued presheaf in the node.
- `θ` has source `P` and target the underlying presheaf of that cohomology sheaf.
  Its displayed equality specifies it as the sheafification unit followed by `e.hom`.
  It is the comparison used consistently for every germ in the conclusions.
- The first universal conjunct quantifies over every derived object `K`, point `x`,
  and element `t` of the stalk of its cohomology sheaf. It supplies an open `U`,
  membership `hx : x ∈ U`, and `s : (P.obj K).obj (op U)` whose comparison germ is `t`.
- The second universal conjunct takes any such neighborhood and section with zero
  comparison germ. It supplies `V`, `_hxV : x ∈ V`, and `i : V ⟶ U` with
  `(P.obj K).map i.op s = 0`. The arrow of opens means precisely containment, and
  its opposite gives the restriction in the correct direction. `_hxV` is an
  existential membership witness, not an omitted condition.
- The last conjunct takes arbitrary derived objects `K,L`, a derived morphism
  `f : K ⟶ L`, and a section over `U` containing `x`. It equates the comparison germ
  of `((P.map f).app (op U) s)` with the stalk map of `H^q(f)` applied to the
  comparison germ of `s`. Stalks and germs are Mathlib's `TopCat.Presheaf.stalkFunctor`
  and `TopCat.Presheaf.germ`, so the germ and cohomology stalk are the actual ones.

Dependencies read and used:

- `def-weil-sheaf-of-modules-category`: its record points to the scheme specialization
  `AlgebraicGeometry.Scheme.Modules`, but its note explicitly directs general ringed
  spaces to its `mathlib_match`, `SheafOfModules`, in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`. The latter's full structure and forget
  functor signatures were read; the scheme-only wrapper is not used on a ringed space.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `DerivedCategory.Q`, and
  `DerivedCategory.homologyFunctor` from Mathlib's derived-category Basic and
  HomologySequence modules (read source signatures and docstrings).
- `def-pc-ringed-spaces-derived-direct-image`:
  `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`, especially
  `RingedSpace.moduleGrothendieckAbelian` and its use of
  `CochainComplex.kInjectiveResolutionFunctor` (read the whole module).
- `prop-pur-kinjective-resolutions-exist`:
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`,
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions` (read whole
  module), used through the shared Grothendieck instance and resolution construction.
- `def-pur-kinjective-complex`: `CochainComplex.IsKInjective` in
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` (read its full signature and
  docstring), used through the dependency's replacement functor.
- `def-weil-pbc-sheafification`: `presheafToSheaf` and `sheafificationAdjunction` in
  `Mathlib.CategoryTheory.Sites.Sheafification` (read source signatures/docstrings).
  The LeftExact import supplies sheafification existence for the small opens site.

The theorem docstring follows each of the node's proof steps: resolution and descent;
exact sheafification of cycles and boundaries, with naturality through localization;
stalk colimits, local representation, local zero detection, and naturality on germs.

Edge cases checked: empty space (no point clauses, but the functorial sheaf isomorphism
still applies), empty open (included among all opens), zero derived object and zero
section (included), degree zero and negative degrees (all integers), arbitrary
unbounded complexes (K-injective replacement, no degreewise-injective substitute),
and arbitrary characteristic (no coefficient restrictions). All universes and binders
are explicit. The site of opens is small in the space universe, and module values
are in the same universe as in the shared direct-image construction.

Searches, 2026-10-11:

- `msearch.py ... leanfinder "sheafification of cohomology presheaf of a complex equals
  its cohomology sheaf"`: eight hits, including `CategoryTheory.Sheaf.cohomologyPresheaf`,
  `.cohomologyPresheafFunctor`, and `.H`. These are natural-degree Ext cohomology of a
  single abelian sheaf, not integer-degree unbounded ringed-space derived objects.
- `msearch.py ... loogle "CategoryTheory.presheafToSheaf,
  DerivedCategory.homologyFunctor"`: zero hits.
- `msearch.py ... grep "sheafification.*cohomology|cohomology.*sheafification"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "sheafification of the cohomology of sections of a
  K-injective complex is the cohomology sheaf"`: unavailable, Internal Server Error.
  This is an unavailable search, not evidence of absence.
- `rg` of the source `WeilConjectures` and project `lean/Sheaf` for
  `sheafification_cohomology|sheafification.*cohomology|cohomology.*sheafification`
  found only related statements, inspected in full where relevant:
  `Paper/HigherDirectImageSheafifiedPresheaf` is natural-degree higher direct images
  of a single étale sheaf; upstream `SixFunctors/Etale/SmoothBaseChange/HigherDirectImage`
  concerns bounded-below complexes on the small étale site with constant coefficients.
  Neither covers arbitrary ringed spaces and unbounded module complexes.
- `rg` for the exact node id in upstream `WeilConjectures`: no hit.
  `tools/lean_names_upstream.py show` for the item: no recorded declaration.
- `rg` for the chosen declaration name in Mathlib/upstream/project: no prior declaration.

Source checked at https://stacks.math.columbia.edu/tag/0BKJ (the local literature source
is absent on this machine): the proof computes the quotient of cycles by boundaries
in sections of a K-injective representative and identifies its sheafification with
sheaf cohomology. No node fault or STATEMENT-DISPUTED issue was found.

Validation: compiled on the server with `scompile.py`; the initial elaboration errors
were repaired and the line-length warnings were removed. The worker dry run is the
final check; the independent second reader supplies their own reading and delivers.

## Second reading by U1

I read the node statement, the Lean declaration, its dependency records, and Stacks Tag
0BKJ independently. The source introduces a ringed space `(X, O_X)`, an object `K` of
`D(O_X)`, and an integer `q`; it states that the presheaf `U ↦ H^q(U,K)` sheafifies to
`H^q(K)`. The node expands this into an explicit functorial K-injective construction,
a natural sheafification isomorphism, and three stalk/germ consequences. The Lean renders
these items as follows, in the same order:

- `(X : RingedSpace.{u})` and `[HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings X))]` give the ringed space and its derived category;
  no Noetherian, separated, characteristic, boundedness, or finiteness hypothesis is
  added.
- `(q : ℤ)` allows every integer degree, including negative degrees.
- `P : DerivedCategory ... ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})` is the presheaf-valued
  cohomology functor. The first `Nonempty` isomorphism identifies `DerivedCategory.Q ⋙ P`
  with the degree-`q` homology of the sheafified sections of the selected
  `CochainComplex.kInjectiveResolutionFunctor`; this records both values and maps.
- `e : P ⋙ presheafToSheaf ... ≅ DerivedCategory.homologyFunctor ... q ⋙
  SheafOfModules.toSheaf` is the canonical sheafification comparison and is an isomorphism
  of functors, hence natural in `K`.
- `θ` is explicitly the sheafification unit whiskered by `e.hom`; the first universal
  clause gives a neighborhood, membership witness, and section for every stalk element.
- The second universal clause gives a smaller neighborhood and restriction map on which a
  section with zero germ is zero; `_hxV : x ∈ V` is present explicitly.
- The final universal clause compares the germ after `P.map f` with the stalk map induced
  by `DerivedCategory.homologyFunctor ... .map f`, for every derived morphism `f`.

Every object, hypothesis, quantifier order, and conclusion clause in the node is therefore
rendered by the declaration. The Lean statement is well typed under the project options and
has no unbound variables. The source's local identity `H^q(U,K)=H^q(U,K|_U)` is represented
by taking sections of the global K-injective resolution, as specified by the node's direct-
image dependency; no restriction of a K-injective complex is assumed.

Edge cases were checked: the empty space and empty opens remain in the presheaf quantifiers;
the zero derived object and zero sections satisfy all clauses; `q = 0` and negative `q` are
included; unbounded complexes are handled by the K-injective replacement; and no coefficient
or characteristic restriction is introduced. Universes of schemes, presheaves, and additive
groups are shared explicitly, while `w` only indexes the derived-category localization.

I repeated the existing-definition searches with `rg` in `WeilConjectures/`, `lean/Sheaf`,
and Mathlib, and with LeanFinder/Loogle queries for sheafification of cohomology presheaves.
Only the unrelated `CategoryTheory.Sheaf.cohomologyPresheaf`/`Sheaf.H` Ext constructions
were found; no declaration has this statement. The source page is Stacks Tag 0BKJ, whose
lemma and proof match the node's core assertion. The sole citer,
`lem-pc-ringed-space-derived-limit-stalk-injective`, uses the representation and local-zero
clauses exactly as stated, so its use holds.

No mismatch was found. I changed no Lean code or node statement; I added this independent
second-reading record only. The module recompiles cleanly with `scompile.py`.
