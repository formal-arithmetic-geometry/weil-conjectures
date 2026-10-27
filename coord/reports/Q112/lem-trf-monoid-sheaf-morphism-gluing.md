## Worker report

Q112 states `CategoryTheory.monoidSheafMorphism_gluing` in
`lean/Sheaf/CategoryTheory/MonoidSheafMorphismGluing.lean`. The unique theorem
has proof `sorry`; no definitions, helper theorems, or new nodes are introduced.
Only the item's `lean` field changes. Its accepted stage-1 split, statement,
statement dependencies and proof dependencies remain verbatim unchanged.

The inherited BLOCKED ending concerned stage-1 re-splitting. I checked the
current stage-2 queue entry, the live node (reviewed stage-1 PASS, no Lean
record), and `coord/brief-stage2.md` section 0. That handoff explicitly permits
this stage-2 statement delivery. No released repair note for this item was found.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small category of the site is `{C : Type u} [Category.{v} C]`; its
  topology is `J : GrothendieckTopology C`. The full fibre-product hypothesis
  is `[HasPullbacks C]`.
- The covering family is `{I : Type w}`, `U : C`, `X : I → C`,
  `f : ∀ i, X i ⟶ U`, with `hcov : Sieve.ofArrows X f ∈ J U`.
  Passing from covering families to generated covering sieves gives the same
  sheaves and gluing condition; it adds no subcanonicality hypothesis.
- The stated size convention is explicit: the coefficient universe is
  `max u v w`, containing objects, arrows and the covering index type, and
  closed under the products used here. No finite or nonempty index condition
  is imposed. `def-weil-size-convention` is recorded as a convention, with no
  module or declaration to import.
- The three commutative-monoid sheaves on the slice are
  `R A B : Sheaf (J.over U) CommMonCat.{max u v w}`. A functor into
  `CommMonCat` supplies the sectionwise operations and homomorphic restriction
  maps. The usual category-valued sheaf condition equals the underlying-set
  sheaf condition by `Presheaf.isSheaf_iff_isSheaf_forget`; the forgetful
  functor preserves and reflects the relevant limits (MonCat/Limits.lean).
- The structural homomorphisms are `α : A ⟶ R` and `β : B ⟶ R`.
- `localMap` is a morphism between the canonical descent objects of `A` and
  `B` for `J.pseudofunctorOver CommMonCat`. Its field `hom i` is exactly
  `A|_(X i) ⟶ B|_(X i)`. Its `comm` field is agreement on overlaps, with
  the canonical repeated-restriction identifications. Mathlib tests on every
  common refinement; with pullbacks, this is equivalent to agreement on the
  double fibre products: evaluate on the pullback for one direction, and
  restrict along its universal map for the other. Thus this bundled hypothesis
  does not add a cocycle condition on the local maps.
- `hbase` is `localMap.hom i ≫ (J.overMapPullback ... (f i)).map β =
  (J.overMapPullback ... (f i)).map α` for each `i`, exactly the local
  structural-map equation, in Lean's diagrammatic composition order.
- The conclusion chooses `u : A ⟶ B`. Its first conjunction gives
  `u ≫ β = α` and `(toDescentData f).map u = localMap`. The latter equality
  says precisely that all component restrictions are the prescribed local
  maps: descent morphisms are extensional in their `hom i` fields.
- The second conjunction gives uniqueness among global monoid-sheaf maps
  with that structural equation and those restrictions, by `u' = u`.
- The last conjunction quantifies over `hiso : ∀ i, IsIso (localMap.hom i)`
  and gives `e : A ≅ B`, `e.hom = u`, `e.inv ≫ α = β`, and, for each `i`,
  the restriction of `e.inv` equals `@CategoryTheory.inv ... (hiso i)`.
  An actual isomorphism supplies both inverse equations. This includes both
  the assertion that `u` is an isomorphism over `R` and the specified-inverse
  restriction clause.
- There are no log, integrality, finite-generation, saturation, cancellation,
  or injectivity assumptions on any of the commutative monoids or maps.

Dependencies and source declarations read:

- `def-weil-pbc-sites-and-cohomology`: imported
  `Sheaf.CategoryTheory.SiteCoveringAxioms`; read
  `CategoryTheory.Precoverage.IsSiteForCoverings` and its complete docstring.
  As its record's note specifies, its sheaf component remains Mathlib's
  `GrothendieckTopology`, `Sheaf`, and generated-sieve topology. Here global
  pullbacks are already assumed by the item; no new site notion is defined.
- `def-pur-localized-ringed-site`: read its existing Mathlib record, including
  the module-specific `SheafOfModules.overFunctor` and the recorded general
  `CategoryTheory.GrothendieckTopology.over` and `CategoryTheory.Sheaf.over`.
  The monoid-valued case uses those general slice definitions, exposed through
  `Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver`. Its
  `GrothendieckTopology.overMapPullback` is restriction by precomposition with
  `Over.map f`, hence evaluates on `W → X i → U`; it is the exact slice
  restriction in the node. No module-valued specialization is substituted.
- `def-weil-size-convention`: metatheoretic universe convention, rendered by
  the explicit universe levels as described above.
- Proof dependency `lem-pe-set-sheaf-cover-descent`: plain import
  `Sheaf.CategoryTheory.SetSheafCoverDescent`, declaration
  `CategoryTheory.setSheafCoverDescent`; read its full signature and proof
  docstring. Its fully faithful restriction functor is the map-gluing clause
  used twice in the node's proof. Its imports remain private to this module.
- Mathlib infrastructure: `Pseudofunctor.DescentData.Hom`, `DescentData.ofObj`,
  and `Pseudofunctor.toDescentData` in Sites/Descent/DescentData.lean;
  `GrothendieckTopology.pseudofunctorOver` in Sites/PseudofunctorSheafOver.lean;
  `GrothendieckTopology.overMapPullback` and composition isomorphisms in
  Sites/Over.lean; `CommMonCat` and its limit/forgetful instances in
  Algebra/Category/MonCat/Limits.lean. All notions are reused directly.

Source check: read `literature/stacks-project/sites.tex` at
`lemma-glue-maps` (Tag 04TQ, lines 5638 onward) and `lemma-relocalize`
(Tag 03EH, lines 5455 onward). The theorem docstring records all five accepted
proof steps: forget and glue maps, preserve product and identity by
separatedness, preserve the map to `R` and prove uniqueness, glue inverse
maps, and verify both inverse equations locally.

Edge cases checked: the empty covering is allowed when its generated sieve
covers; the sheaf condition then forces terminal values on the covered slice,
so existence and uniqueness and the vacuous local-isomorphism conclusion are
correct. Singleton covers and identity maps recover the given map. Repeated
indices and self-overlaps occur in descent-data compatibility and are not
excluded. The trivial monoid and noncancellative monoids need no change.
Arbitrary unequal object, arrow and index universes remain explicit.

Searches (the retained machine results are in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder`: "Compatible morphisms of sheaves of
  commutative monoids over a fixed sheaf glue uniquely along a site covering
  and local inverses glue". Eight hits included topological-space gluing,
  presheaf amalgamation, and cover-dense constructions, not this statement.
- `msearch.py ... loogle`: `"Sheaf", "CommMonCat"`; no hits.
- `msearch.py ... leansearch`: "Gluing homomorphisms of sheaves of
  commutative monoids over a fixed sheaf along a covering". Eight hits,
  including section gluing and hypercover morphism gluing, not the fixed-R
  monoid sheaf map with inverse restriction conclusion.
- `msearch.py ... grep`: `glueMorphisms|presheafHom_isSheaf|isIso_of_coversTop`
  in `CategoryTheory/Sites`, repeated on continuation: ten hits. Read
  Sites/SheafHom.lean and its `Presheaf.IsSheaf.hom`, `sheafHom` and
  `sheafHomSectionsEquiv`. These give the general Hom sheaf; they do not
  state the full fixed-R and inverse conclusion. `isIso_of_coversTop`
  detects invertibility of an already global map. Hypercover
  `glueMorphisms` glues arrows of the base category.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for monoid/gluing names,
  the item id, and the new declaration name found no existing declaration of
  this statement; the incidental hits concerned monoid actions, toric gluing,
  and graded-module localizations. The exact new declaration name was also
  searched in Mathlib and was absent.

Validation: `scompile.py Q112 lem-trf-monoid-sheaf-morphism-gluing
<module file>` passed for the sandbox and library module modes. No errors or
unexpected warnings. All variables are explicit (`autoImplicit false`), all
Lean lines are at most 100 characters, and the JSON signature is extracted
verbatim from the module. No node fault, statement correction, or
STATEMENT-DISPUTED issue was found.

## Second reading by Q112

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
