## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricStalkCohomology` states
`AlgebraicGeometry.Etale.nonempty_geometricStalk_cohomology_iso`, with its entire proof
`sorry`. No definitions, helper declarations, new nodes, dependency modules or statement
corrections are introduced.

Source read: the complete statement and proof of blueprint
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-stalks-of-cohomology.md`.
The node's equality denotes the canonical identification, as its proof explicitly says;
it is represented by an isomorphism of abelian groups, under `Nonempty` so this remains
a theorem rather than a data definition.

Hypothesis and clause correspondence:

- The scheme is `{T : Scheme.{u}}`, with no finiteness, separation or characteristic condition.
- A geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `t : Spec (.of Ω) ⟶ T`. The corrected binder is `[IsAlgClosed Ω]`, as required
  by `def-weil-geometric-point` through `def-weil-pbc-scheme-conventions`.
  `Scheme.pointSmallEtale` requires only separable closedness, supplied by the
  existing `IsSepClosed.of_isAlgClosed` instance.
- `Q ∈ D(T_Et)` is `Q : DerivedCategory (Sheaf T.smallEtaleTopology
  AddCommGrpCat.{u + 1})`, exactly the abelian-sheaf encoding in the dependency record.
  This is the unbounded derived category.
- The degree is arbitrary `(q : ℤ)`, including negative degrees.
- `H^q(Q)` is `(DerivedCategory.homologyFunctor _ q).obj Q`.
- Its stalk at `t` is the object image under
  `((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber`.
- The pullback `Q_t` is `(upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory.obj Q`:
  the existing exact inverse image applied to the unbounded derived category.
- `H^q(Q_t)` is the same homology functor on the target derived category. Its sheaf on
  the separably closed point is read as an abelian group by the fibre at `𝟙 (Spec (.of Ω))`.
  Thus both sides of `≅` are abelian groups, and the RHS explicitly uses inverse image.
  This is the conventional identification of abelian sheaves on a separably closed
  field's étale site with abelian groups, not an additional hypothesis on `Q`.

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: imports
  `Sheaf.AlgebraicGeometry.DerivedCategories`; uses its recorded existing
  `DerivedCategory` on abelian sheaves. The module's docstring explicitly specifies
  `AddCommGrpCat.{u + 1}` for the coefficient-free notation.
- `def-weil-pbc-geometric-stalks`: `Scheme.pointSmallEtale` from
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint` (full definition at line 64), and
  `GrothendieckTopology.Point.sheafFiber` from
  `Mathlib.CategoryTheory.Sites.Point.Basic` (definition at line 277). Universe lift
  uses the upstream `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` API,
  imported through `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`.
  The lift changes the size of the indexing presentation, not the stalk.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (full definition, adjunction
  and exactness API read at lines 227–299). Imported via the derived module.
  `CategoryTheory.Functor.mapDerivedCategory` is the existing termwise localization
  construction in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, lines 27–43.
- `def-weil-derived-cohomology-sheaves` is a Mathlib leaf, not a missing record:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`, read in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, lines 26–46.
- The proof dependency `prop-weil-pbc-geometric-stalks-exact` is a Mathlib leaf;
  its finite-limit-preservation instance in Point.Basic and skyscraper adjunction
  in `Mathlib.CategoryTheory.Sites.Point.Skyscraper` were read. The latter is
  explicitly imported. `lem-kun-stalk-as-pullback` has no recorded module to import;
  the existing `Etale.upperStarCompUliftSheafFiberIso` declaration and full docstring
  in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk` were read and imported
  for the proof plan.

Edge cases checked: zero complexes and all integer degrees give zero groups on both
sides; no boundedness or injectivity is assumed. The empty scheme admits no geometric
point, so the statement is correctly vacuous there. No nonempty scheme hypothesis is
added. The coefficient universe follows the recorded derived-category encoding;
`ulift` permits its geometric fibre without reducing the allowed coefficient size.
The equality in the source is an identification of objects up to canonical isomorphism,
not literal equality of arbitrary chosen quotient constructions.

Searches performed (msearch queries are logged in this sandbox's searches.jsonl):

- LeanSearch: “The geometric stalk of a cohomology sheaf is the cohomology of the
  derived pullback to the geometric point”. Service returned Internal Server Error;
  unavailable, not evidence of absence.
- LeanFinder, same query: eight topological stalk/pullback declarations, including
  `TopCat.stalkToFiber`, `TopCat.Presheaf.germToPullbackStalk` and
  `TopCat.Presheaf.stalkPullbackInv`; no étale derived comparison.
- msearch grep: `mapDerivedCategory.*[Hh]omology|[Hh]omology.*mapDerivedCategory`
  in Mathlib/Algebra: zero hits. Direct source inspection located the general exact
  functor localization construction; it does not state this geometric comparison.
- Direct rg of project and upstream for
  `sheafFiber.*(mapDerived|homology)|stalk.*[Hh]omology|stalks.*[Cc]ohomology|derivedStalk`
  found ringed-space tensor/stalk lemmas, strict-local base change, and special
  Fourier-transform statements, not this statement for arbitrary derived abelian sheaves.
- Direct rg of upstream for `lem-kun-stalks-of-cohomology` returned no hits;
  dag/lean_names_upstream.json has no attachment for this node or the chosen declaration.
- Direct rg located `upperStarCompUliftSheafFiberIso` and the geometric-point derived
  module: these give underived stalk compatibility and single-degree morphism extensionality,
  respectively, not the item. Both signatures and docstrings were inspected.

No mathematical node fault or disputed statement was found. Server-only compilation
uses scompile.py with the prescribed per-file limit; final result is recorded by the dry run.


## Second reading by NZ

Read independently against the full node, its master-blueprint source, all four
statement-dependency records and their actual declarations, the stalk/pullback
comparison, and Stacks homology.tex, lemma-exact-functor (Tag 010N), including its
statement and proof. The blueprint source has no standing finiteness, boundedness,
torsion, coefficient-ring, or characteristic hypothesis. Tag 010N only assumes
abelian categories and the stated exactness property of the functor.

Object, hypothesis and conclusion checklist:

1. Arbitrary scheme T: `{T : Scheme.{u}}`. PASS: no Noetherian, separated, proper,
   smooth, nonempty or base-field condition.
2. Geometric point of T: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
   `(t : Spec (.of Ω) ⟶ T)`. PASS after maintainer correction: the project defines geometric points using
   algebraically closed fields. `Scheme.pointSmallEtale` in Mathlib EtalePoint.lean
   accepts the weaker separable-closedness input, inferred from `IsAlgClosed Ω`. Its fibre is `Etale.forget T ⋙ coyoneda.obj (op (Over.mk t))`,
   so its elements really are lifts through etale neighbourhoods. The theorem
   now quantifies over exactly the algebraically closed geometric points of the node.
3. Q in D(T_Et): `(Q : _root_.DerivedCategory
   (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))`. PASS: this is exactly the
   coefficient-free encoding explicitly recorded in DerivedCategories.lean and
   def-weil-pbc-derived-categories. It is unbounded, with abelian-group coefficients,
   not a module category over an extra ring or a bounded derived subcategory.
4. Every degree q: `(q : ℤ)`. PASS: no positivity or vanishing hypothesis.
5. Left side H^q(Q) at t: `DerivedCategory.homologyFunctor _ q` followed by
   `((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber`. PASS: read the actual
   homologyFunctor and homologyFunctorFactors in Mathlib HomologySequence.lean,
   and sheafFiber in Point/Basic.lean. These are cochain cohomology and the
   neighbourhood-colimit stalk required by the two dependency nodes.
6. Q pulled back to the point: `(upperStar AddCommGrpCat.{u + 1} t).
   mapDerivedCategory.obj Q`. PASS: upperStar in UpperLowerStar/Defs.lean is the
   sheafified inverse image, not direct image or an arbitrary exact functor.
   The actual Mathlib mapDerivedCategory is termwise application localized at
   quasi-isomorphisms. The source Derived/UpperLowerStar module expressly uses
   this construction for unbounded exact inverse image.
7. Right side H^q(Q_t): the target `DerivedCategory.homologyFunctor _ q` followed
   by the geometric fibre at `𝟙 (Spec (.of Ω))`. PASS: the latter reads a sheaf
   on a separably closed point as an abelian group. Read the signature and body of
   upperStarCompUliftSheafFiberIso: with f=t and s=identity it identifies pullback
   followed by this fibre with the original geometric stalk.
8. Equality/identification: `Nonempty (left ≅ right)`. PASS: the node's expanded
   proof expressly interprets equality as the cohomology identification, not
   equality of chosen localization objects. Both sides are the prescribed abelian
   groups. The docstring records the canonical construction; no additional
   conclusion about maps or choices is asserted by the node's displayed formula.

Edge cases: q=0 and negative q are included by the integer binder. The zero object
has zero cohomology and zero stalk on both sides. There is no index-set or finite
family binder to restrict, and no extra nonempty condition. The empty scheme has
no geometric point, so its instance is vacuous for exactly the mathematical reason.
All characteristics are allowed. The universe u is bound explicitly; Ω and T use
the dependency API's common scheme universe, while abelian sheaves use u+1 as the
recorded derived-category convention requires. The point's ulift is the existing
universe comparison, not a different neighbourhood category or a size hypothesis.
No free variables or universes remain, and no typeclass assumptions are hidden
in section variables.

Independent searches (logged in searches.jsonl where run through msearch):

- LeanFinder: "Taking a geometric fibre commutes with cohomology of a derived
  etale sheaf". Eight hits, chiefly Point.Hom.sheafFiber_comp and toPresheafFiber
  naturality; none states this derived comparison.
- Loogle: `"sheafFiber", "homology"` returned zero hits. An earlier malformed
  two-string query returned a parser error and is not evidence of absence.
- LeanSearch: "Cohomology sheaves evaluated at a geometric point agree with
  cohomology of inverse image" returned Internal Server Error; unavailable.
- rg independently searched Mathlib, the full upstream WeilConjectures tree and
  project lean/Sheaf for stalk/cohomology in both orders, sheafFiber/homology in
  both orders, and mapDerivedCategory/homology. Read the actual generic
  Functor.mapDerivedCategoryHomologyFunctorIso (upstream ExactFunctor.lean,
  lines 258ff): it supplies exact-functor/cohomology commutation, but its target
  is a pulled-back cohomology sheaf and it does not identify geometric stalks.
  Together with upperStarCompUliftSheafFiberIso it is a proof ingredient, not an
  existing declaration of this complete item. The ringed-space stalk comparison,
  strict-henselian object-cohomology statements and field continuous-cohomology
  comparisons have different objects/hypotheses. No duplicate was found.

No statement correction, new definition node or dependency module is needed.
No hollow definitions or hollow hypotheses occur; the only theorem has its entire
proof `sorry`. The module and theorem docstrings include the source and blueprint
id and the three proof steps (cycles/boundaries, exactness, localization/pullback).

Mismatch found and repaired: Point.Skyscraper was a public import although only
used for the exactness proof plan. Changed it to ordinary `import`, following
stage 2 section 3 rule 7. At the group reading the mathematical signature and node record were unchanged;
checked the recorded signature verbatim against the file and every line <=100
characters. Compilation via scompile.py passed on the server (nice 19, two threads,
60 seconds per file); the delivery dry run repeats the final-file check.


## Maintainer correction of the geometric-point hypothesis

H3: the delivered `[IsSepClosed Ω]` dropped the algebraic-closedness hypothesis
required by `def-weil-pbc-geometric-stalks` through
`def-weil-pbc-scheme-conventions` and `def-weil-geometric-point`. Mathlib's point
API supports the stronger theorem, but does not change the project's definition.
The complete replacement uses `[IsAlgClosed Ω]`; `IsSepClosed.of_isAlgClosed`
supplies the instance needed by `pointSmallEtale`. The record's signature is
updated verbatim. The source statement, dependency lists and proof plan need no
change. The correspondence entries above describe the corrected signature.

Maintainer validation: the complete replacement module compiled through
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NZ
lem-kun-stalks-of-cohomology
fixes/lean/Sheaf/AlgebraicGeometry/GeometricStalkCohomology.lean`.
Result: exit 0, no diagnostics, 1.6 seconds, nice 19, two threads, 60-second
per-file limit. The replacement record's `statement` equals the module signature
verbatim; its sole proof remains `by sorry`.
