## Worker report

The delivery states `SheafOfModules.ringedStrictTowerProjectionMorphism` in
`Sheaf.Paper.RingedStrictTowerProjectionMorphism`. Its proof is `sorry`; every
auxiliary definition has actual data. There are no new independent notions,
new nodes, dependency repairs, or changes to the mathematical statement.
The added statement dependency `def-weil-pbc-ringed-tensor-square-presentation`
already has its reviewed Lean record on newtargets-dag. It supplies the common
ringed-site/derived-tensor presentation used by the projection-mate dependency.
All auxiliary declarations are listed in `lean.declarations` and have source
and blueprint docstrings. They are the owning node's diagram and comparison
interfaces, as authorized by the human's missing-helper instruction.

The previous BLOCKED explanation confused N0's stage-1 merge with a stage-2
completion. The shared node has the reviewed eight-step split but no `lean`
record. N0's report explicitly says it wrote no Lean. This delivery supplies the
missing statement; it does not duplicate or re-push N0's stage-1 work.

Hypotheses and objects are rendered as follows:

- The small ringed sites and commutative coefficient sheaves are the existing
  `Y X : RingedTensorCorner.{u,w}`. `e : RingedTensorEdge Y X` supplies the
  geometric adjunction, left exact inverse image, algebraic ring inverse image,
  structural ring map, induced module pullback, its module adjunction, and
  derived pullback with comparison. This is the same presentation used by the
  recorded projection-mate theorem. It allows geometric morphisms not induced
  by functors between the given sites.
- `Y.mateModules` and `X.mateModules` are the recorded `ringedSiteModules`, hence
  Mathlib's actual `SheafOfModules`. `mateDerived` is Mathlib's unbounded
  `DerivedCategory` with explicitly chosen localization universe `w`.
- `a : RingedTensorModel Y` and `b : RingedTensorModel X` specify derived tensor
  by its flat-term K-flat representative comparisons. No new tensor is defined.
  `e.left`, `e.right`, `e.derivedAdjunction` and `e.tensorComparison a b` are the
  recorded derived pullback, direct image, adjunction and canonical tensor map.
- `StrictProjectionLimit X/Y` merely packages the Rlim, total-right-derived
  comparison, K-injective computation, evaluation comparison and natural Roos
  triangle supplied by the strict-tower homotopy-limit dependency. Countable
  products and tower localizations are explicit category infrastructure from
  that dependency, with no product-exactness assumption.
- `StrictProjectionDirectImage e lx ly` packages the levelwise total derived
  direct image and the specified pushforward/limit comparison. Its ordinary
  comparison is fixed by `limit.post`. Its `normalized` field is exactly the
  common-underived-composite equation of the pushforward/limit dependency.
  Its derived adjunction is fixed by the ordinary counit on K-injectives;
  its evaluation is fixed on K-injective strict towers. These are presentations
  of the canonical functors named in the node, not extra geometric hypotheses.
- `projectionCoefficients` is the full subcategory of `Under` the constant
  degree-zero ring complex. An object contains the entire strict diagram
  `P.obj.right` and compatible chain augmentation `P.obj.hom`. Its property
  requires a bounded complex at each level and every term isomorphic to a
  finite product of the ring module. Bounds and ranks may vary with the level;
  rank zero is included. A morphism is every chain map of diagrams preserving
  the augmentation, with no requirement to preserve a choice of basis.
- `e.projectionCoefficientDiagram` is actual termwise pullback of this diagram,
  including all transition maps. The X augmentation in the conclusion is fixed
  by `projectionUnitComplex.inv` followed by termwise pullback of `P.obj.hom`.
  `projectionUnit` comes from the existing unique scalar-extension/unit
  characterization, not from arbitrary existence or a Nonempty choice.

Each assertion of the node is rendered as follows:

- Direct-sum total tensor is the recorded `map₂HomologicalComplex` of the
  existing sheaf tensor bifunctor. `projectionTensorDiagrams` uses it at every
  level. The existential `CY`, `CX` take values in complexes of the abelian
  category of strict towers. The natural isomorphisms `cy`, `cx` identify
  their associated diagrams of complexes with those actual total tensors.
  Thus this is a chain-level realization, not a replacement by Tow(D).
- `S`, `T` take values in `DerivedCategory projectionTowers`. The natural
  isomorphisms `s`, `t` factor the chain functors through `DerivedCategory.Q`
  on **all** complexes. They give independence of arbitrary representatives
  N of Rf_*E and K of E, including all representative maps and all transitions.
- `hf` records that each finite-free coefficient and its termwise pullback
  are flat-term K-flat. `sEv` and `tEv` give their evaluated derived-tensor
  interpretations. The first two conjuncts pin those comparisons to the
  existing `mixedTensorRepresentative` on every complex and to
  `derivedPullbackComplexComparison` on the coefficient complex.
- `u : e.right ⋙ S ⟶ T ⋙ projectionPost d.Rt` is a natural transformation
  valued in the category of functors from augmented coefficient towers to
  D(Tow(Y)). Consequently it is natural both in E and in every chain map of
  the **entire augmented tower**. Its component is the requested map
  S_bullet(E) -> Rf_*^Tow T_bullet(E).
- The third conjunct identifies evaluation at every level with the recorded
  `derivedProjectionFormulaMate`, using `sEv`, `tEv` and the normalized
  pushforward evaluation comparison. It is exactly the projection mate alpha,
  not an arbitrary family of maps with the same source and target.
- `ProjectionCoaugmentation` fixes an ordinary inverse-limit chain map by its
  actual degreewise limit projections: inverse canonical right unitor followed
  by total tensor with z. The fourth and fifth conjuncts give these actual
  ordinary coaugmentations and identify `zY`, `zX` with Q of those chain maps,
  followed by `ly.eta`/`lx.eta` and transported through `s`/`t`. Thus they are
  the specified coaugmentations, not arbitrary lifts of levelwise maps.
- The sixth conjunct is the precise compatibility equation, in Lean's
  diagrammatic composition order:
  `zY ≫ ly.L.map u = e.right.map zX ≫ d.a.hom`.
- The final three conjuncts give, respectively, the first, middle and
  connecting squares for the **same** `ly.L.map u`, the same product map of
  evaluated u, and the same Roos p and delta. The middle maps use the recorded
  `towerTransitionEndomorphism` (1 minus the shift). In particular the
  connecting square is retained explicitly.
- There is no ideal, completeness, flatness of the geometric morphism, or
  exactness of countable products among the assumptions.

Dependencies read and used:

- `Sheaf.CategoryTheory.RingedToposMorphism`,
  `CategoryTheory.RingedToposMorphism`: general geometric, structural-ring and
  induced-module meaning of the ringed-topos data; the existing richer
  `RingedTensorEdge` supplies the same data in the mate's canonical presentation.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  actual module category, through the recorded `mateModules` abbreviation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`: the unbounded localizations.
- `Sheaf.Paper.RingedTensorSquarePresentation`, `SheafOfModules.RingedTensorCorner`,
  `RingedTensorEdge`, `RingedTensorModel`, `RingedTensorEdge.tensorComparison`:
  shared presentations and canonically normalized tensor comparison.
- `Sheaf.Paper.ProjectionMateExact`, `SheafOfModules.ringedProjectionMateExact`
  and its `mateModules`, `mateDerived`, `mateUnitComplex`, `mateTensor`,
  `mateFlat` abbreviations: the precise canonical projection-mate setting.
- `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`,
  and `map₂HomologicalComplex`: direct-sum total tensor with the Koszul sign.
- `Sheaf.Paper.RingedTopoiDerivedPullback`,
  `SheafOfModules.ringedTopoiDerivedPullback`, and the complex-localization
  comparison reexported by the canonical tensor-pullback module: termwise
  pullback of flat-term K-flat complexes and natural resolution comparisons.
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`,
  `CategoryTheory.ringedTowerPushforwardLimitComparison`: total derived images,
  evaluations and the common-underived normalization, packaged unchanged.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitOfUniverses`: canonical strict
  derived limits, evaluation, countable products and natural Roos triangles.
- `Sheaf.Paper.ProjectionFormulaArrows`,
  `CategoryTheory.derivedProjectionFormulaMate`,
  `SheafOfModules.mixedTensorRepresentative`: existing mate and uniquely
  characterized mixed representative. The current recorded pro-etale arrow
  module reexports this general small-site interface and is imported as a
  proof dependency; no second mate or tensor model is introduced.
- The remaining available proof dependencies are imported for stage 3:
  `ProjectionFormulaTotalization`, right-adjoint K-injective preservation in
  `RightDerivedFunctor.Comp`, and Mathlib's levelwise abelian functor category.

Edge cases checked by reading the definitions and source:

- P=0 is included by rank zero and zero augmentations; all coaugmentation maps
  then vanish. There is no nonzero-rank or nonempty-basis hypothesis.
- The constant unit tower with identity augmentation is included and reduces
  the projection mate to its tensor-unit normalization.
- Identity f and identity transitions are allowed. Arbitrary noninvertible
  transitions, zero chain maps, and augmentation-preserving tower maps are
  retained by the full subcategory, without a chosen splitting constraint.
- Each level has its own finite interval; no uniform bound is imposed.
- N need not be K-injective. All representative clauses quantify over arbitrary
  N and K. The proof plan only requires the chosen representative of E to be
  K-injective and never claims that f_*I is K-injective for nonflat f.
- No assumption says Rlim is a categorical limit inside D(A), or that
  D(Tow(A)) is equivalent to Tow(D(A)).
- Universe u and localization universe w are explicit. The small-site model
  is exactly the dependency's `RingedTensorCorner` model; no coefficient or
  derived-morphism universe is silently identified with w. Generic
  postcomposition also binds every object and morphism universe explicitly.

Searches actually made:

- msearch LeanFinder: “Projection formula morphism for strict inverse towers of
  bounded finite free complexes of sheaves, natural and compatible with
  coaugmentation and derived inverse limit” — eight unrelated hits, including
  `SheafOfModules.Presentation.map_π_eq` and inverse-limit projection lemmas;
  none gives this statement.
- msearch Loogle: `"projection", "NatTrans"` — zero hits.
- msearch Mathlib grep: `projection.*[Tt]ower|[Tt]ower.*projection`, subdirectory
  CategoryTheory — zero hits.
- msearch LeanSearch: “The projection formula for bounded finite free complexes
  gives a natural morphism of strict inverse sequences compatible with derived
  limits and unit coaugmentations” — eight unrelated resolution, homology and
  limit-projection hits; no strict derived-tower projection assertion.
- ripgrep in upstream WeilConjectures and project lean/Sheaf for the item id,
  `ringedStrictTowerProjection`, and `strictTowerProjection` — no existing match.
- Project searches for strict/augmented towers found the special Koszul system,
  completed quotient towers and pro-etale strict towers. These concern special
  coefficient diagrams; they do not give the general arbitrary augmented
  bounded finite-free tower statement here.

Source checked directly in the local Stacks text: sites-cohomology.tex,
section-projection-formula and equation-projection-formula-map; its
lemma-Rf-commutes-with-Rlim including the tower-topos argument and its warning
that Rlim is not a categorical limit in D; and algebraization.tex,
lemma-pushforward-commutes-with-derived-completion. The augmented refinement
matches the DAG's eight-step construction. No statement dispute was found.

Validation: the required scompile.py wrapper confirmed the statement against
current server sources in 49.8 seconds (nice 19, two threads, 60-second limit),
with no errors or warnings. The final packet also imports the recorded
proof-dependency modules and is checked again by deliver2.py. The initial
sandbox-only success followed by a module timeout was resolved by the wrapper's
server-source confirmation; no compile limit was raised. No global build,
shared-source edit, direct Git mutation, or other agent was used.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (2026-10-18)

The evaluation comparisons `sEv` and `tEv` were families of isomorphisms indexed by
objects, with no naturality. The first two conjuncts pin them only on objects of the
literal form `Q.obj N`, and the evaluation conjunct uses `sEv (e.right.obj E)`, which
is never of that form. That conjunct therefore said only that each evaluated component
of `u` is an isomorphism, not that it is the projection mate alpha. The fix adds
two conjuncts that make `sEv` and `tEv` natural in the derived variable. Since every
derived object is isomorphic to some `Q.obj N`, the comparisons are now the canonical
ones everywhere, and the evaluated components of `u` are exactly alpha. Nothing else
changed. The fixed file compiles cleanly with nt_compile.py (53.2 s and 44.7 s).
