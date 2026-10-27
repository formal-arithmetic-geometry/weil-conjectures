## Worker report

The module `Sheaf.AlgebraicGeometry.FppfAffineRefinementPullbackModel` states
`AlgebraicGeometry.exists_fppf_affine_refinement_pullback_model`, with its sole
proof `sorry`. It introduces no new definitions, dependency modules or nodes,
and changes only the item's `lean` field. Its docstring follows all seven proof
steps of the node and names their DAG dependencies.

Hypotheses and their renderings:

- The scheme T and family T_i -> T are `T : Scheme.{u}`, `Ti`, and `f`.
  `hcov : Presieve.ofArrows Ti f ∈ Scheme.fppfPrecoverage T` is precisely
  flatness, local finite presentation, and joint surjectivity.
- The given family scheme descent datum is `F : SchemeCoverDescentDatum f`.
  Its local schemes V_i -> T_i are `(F.localScheme i).left` and
  `(F.localScheme i).hom`; its transitions are `F.data.hom`, interpreted
  through the specified `F.representation` bijections.
- A and Z, with coprojections `inA` and `inZ`, are presented by
  `hA : IsColimit (Cofan.mk A inA)` and `hZ : IsColimit (Cofan.mk Z inZ)`.
  These hypotheses are the universal properties of the coproducts already
  specified by the node, not additional geometric assumptions. The equations
  `ha` and `hq` specify their induced structure maps `a : A ⟶ T` and
  `q : Z ⟶ A` uniquely. No arbitrary structure map replaces those induced maps.
- `D : Over.DescentDatum a (Over.mk q)` is the singleton datum.
  `hD` states that its transport on all component test points is the transition
  of F followed by the component coprojection. Its auxiliary point y has its
  underlying map prescribed, so it is unique. It exists by `hq` and the fact
  that the represented point lies over r. The auxiliary equality proof ht
  exists by `ha`, hr, and hs. Thus the implication used in hD has precisely the
  intended content; it is not a condition only on a possibly empty class of
  tests. There is no extra transport normalization or effectivity assumption.
- `U : T.Opens` and `hU : IsAffineOpen U` encode any affine open subscheme,
  including the empty affine open.
- `hAU : IsPullback b aU a U.ι` presents A_U = A x_T U with projections b,aU.
  `hZU : IsPullback z v q b` presents Z_U = Z x_A A_U with projections z,v.
  Using universal-property presentations accommodates the specified chosen
  pullbacks and all their uniquely isomorphic presentations. It adds no
  hypothesis beyond the equalities defining these objects in the node.
- The universe is explicit: schemes in `Scheme.{u}` and the family index in
  `Type (u + 1)`, matching the recorded family-datum interface. There is no
  `[Small I]` or `[Nonempty I]` assumption. Presenting the given coproducts by
  cofans handle any index for which the node's coproducts lie in this fixed
  scheme universe, without requiring a chosen large coproduct instance.

Conclusion, clause by clause:

- `∃ DU : Over.DescentDatum aU (Over.mk v)` gives the datum D_U over U.
  The following universal equation states that projection z intertwines its
  transport with D along b. Here y is the unique lift of x.left followed by z;
  existence follows from hZU. The proof ht exists by hAU and hrs. Quantifying
  over these uniquely determined point maps and proof-irrelevant equalities
  avoids any hidden choice or extra hypothesis in the conclusion.
- `m : ℕ`, `i : Fin m → I`, and
  `W : ∀ j, (pullback (f (i j)) U.ι).Opens` give finitely many indexed open
  subschemes of T_i x_T U. `∀ j, IsAffineOpen (W j)` is their affineness.
  The next clause states `Flat` and `LocallyOfFinitePresentation` of each
  composite to U. The pointwise `∀ x, ∃ j, x ∈ Set.range ...` clause states
  that their images cover U.
- C is the actual Mathlib coproduct `∐ fun j ↦ (W j).toScheme`, with no
  arbitrary replacement scheme. The equality for p specifies its canonical
  induced morphism as `Sigma.desc` of the component maps to U.
- `IsAffine C` gives affineness of C. The successive properties of p are
  `Flat p`, `Surjective p`, `LocallyOfFinitePresentation p`, `QuasiCompact p`,
  and `QuasiSeparated p`. The last three together are exactly finite
  presentation under `def-weil-pbc-scheme-conventions`; there is no additional
  project definition of finite presentation to repeat.
- `Presieve.singleton p ∈ Scheme.fpqcPrecoverage U.toScheme` is the full
  singleton fpqc-cover condition, including quasi-compactness of the family.
- The morphism h and equation `hh : h ≫ aU = p` give a U-morphism C -> A_U.
  Its component equations after b force the prescribed refinement maps into A;
  together with hh and hAU they characterize the induced map uniquely.
- The underlying scheme of E is exactly `pullback v h` and its structure map
  is `pullback.snd v h`. Thus its projection to Z_U is `pullback.fst v h`
  and its square over h is Cartesian by construction. This is encoded by the
  actual pullback object, with no redundant tautological Cartesian conjunct.
  `Over.DescentDatum.IsBaseChange hh (pullback.condition ...) DU E` is precisely
  the specified intertwining equation, using the recorded singleton API.
- The last existential is an actual scheme isomorphism from `pullback v h`
  to the coproduct of
  `pullback (F.localScheme (i j)).hom ((W j).ι ≫ pullback.fst (f (i j)) U.ι)`.
  These are exactly Q_j = V_i x_T_i W_j, with the prescribed projection
  W_j -> T_i. The final equality makes this an isomorphism over C using the
  coproduct of the Q_j projections. A bare isomorphism without this equation
  would omit the node's over-C clause.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`, `Scheme.fpqcPrecoverage`.
- `Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum`:
  `SchemeCoverDescentDatum`, its `localScheme`, `data`, and `representation`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `Over.DescentDatum`, its `transport`, and `Over.DescentDatum.IsBaseChange`.
- `Mathlib.AlgebraicGeometry.Limits`: coproduct existence and universal
  property, `sigmaOpenCover`, `disjoint_opensRange_sigmaι`, and finite
  coproduct affineness. The usual `Cofan` / `IsColimit` universal property
  expresses the existing coproduct-family node without copying its notion.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `IsPullback` is its universal-property form.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and the open
  immersion base-change instance; open subschemes are `W : X.Opens`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `QuasiSeparated`:
  `QuasiCompact`, `QuasiSeparated`; these are the notions of the conventions
  node, which defines no extra object. The size-convention node likewise
  defines no object and is rendered by the explicit universe binders.

The stated proof dependencies are imported: the existing
`Sheaf.AlgebraicGeometry.FppfAffineRefinement` theorem
`Scheme.exists_finite_fppf_affine_open_refinement`; the upstream
`WeilConjectures.AlgebraicGeometry.FpqcCanonicalPullbackDatum` theorem
`exists_canonical_pullback_descent_datum`; Mathlib's `Precoverage.mem_coverings_of_isPullback`
through the fppf-site import; affine-morphism permanence and morphisms of affines
through `Mathlib.AlgebraicGeometry.Morphisms.Separated`; open-immersion base change
through the scheme imports; and `Scheme.Cover.glueMorphisms` through
`Mathlib.AlgebraicGeometry.Gluing`. All recorded dependency interfaces are usable.

Edge cases checked: m = 0 is allowed by `Fin m`, with no nonemptiness binder.
For U empty all objects over U are empty and the unique maps meet every clause;
for nonempty U the coverage clause forces m nonzero. The family I may itself be
empty, in which case hcov forces T empty. Repeated selected indices are allowed;
there is no injectivity requirement on i. Arbitrary nonaffine T, arbitrary local
schemes V_i, and non-effective descent data remain allowed. Neither separation
nor quasi-compactness is assumed of the original covering arrows or of q.

Searches performed with the prescribed msearch.py, plus local source searches:

- LeanFinder: `finite affine fppf refinement with cartesian pullback descent datum
  coproduct local model`: eight hits, mostly `ExistsHomHomCompEqCompAux` and
  affine refinements of open covers; none gives this combined statement.
- Loogle: `AlgebraicGeometry.Scheme.fppfPrecoverage,
  CategoryTheory.Over.DescentDatum`: no hit, since the external project's
  `Over.DescentDatum` is not in the Mathlib search index. Follow-up query
  `"fppf"`: ten hits, identifying the existing precoverage/topology and
  stability declarations, but no Cartesian local model.
- LeanSearch: `finite affine refinement of an fppf covering and Cartesian
  pullback of scheme descent data`: eight hits concerning open-cover pullbacks,
  generic descent data, and affine pullbacks, not the node's statement.
- Mathlib grep via msearch: `affine.*refin|refin.*affine|DescentDatum` in
  `AlgebraicGeometry`: 25 hits, no exact combined theorem.
- `rg` in the project's `lean/Sheaf/AlgebraicGeometry` and upstream
  `lean/WeilConjectures/AlgebraicGeometry` for affine refinements,
  `SchemeCoverDescentDatum`, and singleton descent finds the recorded family
  interface, FppfAffineRefinement, canonical pullback datum, and consumers,
  but not this statement. `grep -rn` of the exact item id in
  `lean/WeilConjectures` finds no match; the upstream-name index likewise
  contains no exact item match.

The source paragraphs were read directly in `literature/stacks-project/descent.tex`
(lemma-descending-types-morphisms and lemma-pullback) and `topologies.tex`
(lemma-fppf-affine and definition-standard-fppf). No statement correction or
STATEMENT-DISPUTED issue is needed. The example CompactObject module has been
withdrawn in the current checkout, so the module header follows the active
SchemeCoverDescentDatum dependency and the brief's current module-mode rules.

Validation: the prescribed scompile.py compiled the statement in sandbox and
library module modes cleanly. The deliver2.py --no-push dry run passed server preflight and final per-file
compilation (OK, dry-run commit c2fa360094e).

## Second reading by Q74

The worker reread the complete node and Lean signature clause by clause, with the
correspondence recorded above. This is a worker consistency check; the brief's
independent review is performed by the maintainer, not claimed to have been
performed by a second agent. No agents were started, as instructed.

The rereading removed the redundant `IsPullback` conjunct for the chosen
`pullback v h`: its Cartesian property is already intrinsic to that object.
It checked especially the variable-base D_U transport equation (the upstream
IsBaseChange is fixed-base and is used only for E), actual coverage of U,
all five properties of p, the fpqc membership, characterization of h, and the
final over-C equation. No other mismatch was found. Every variable and universe
is explicitly bound, every theorem proof is sorry, and there are no helper
choices or definitions.
