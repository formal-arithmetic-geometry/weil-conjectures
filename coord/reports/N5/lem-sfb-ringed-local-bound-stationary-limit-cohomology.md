## Worker report

The module `Sheaf.CategoryTheory.RingedLocalBoundStationaryLimitCohomology` states
`CategoryTheory.ringedLocalBound_stationaryLimit_cohomology`, with its whole proof
`sorry`. It introduces no definitions or additional nodes. The node is unchanged
except for `lean`. The statement follows Stacks 0D6T, including its canonical
projection maps, with the local assumptions of Situation 0D6R expanded.

Hypothesis and conclusion correspondence:

- The site is `C : Type c`, `[Category.{v} C]`, `J : Precoverage C` and
  `_hJ : J.IsSiteForCoverings`. Objects and arrows fit the coefficient universe
  `max c v r`; `[EssentiallySmall.{max c v r} C]` explicitly records the small-site
  convention without equating the object and morphism universes. The standard
  sheafification and locally-bijective instances make the existing abelian
  module-sheaf category available. These are size infrastructure, not extra
  geometric assumptions.
- The ring sheaf is `R : Sheaf J.toGrothendieck RingCat.{max c v r}` and `_hcomm`
  asserts multiplication commutative on every object. This uses the same RingCat
  presentation as the recorded strict-tower theorem.
- Module sheaves are the recorded `ringedSiteModules.{max c v r} R`, transparently
  Mathlib `SheafOfModules`; the unbounded derived category is `DerivedCategory`
  under the explicit `HasDerivedCategory.{w}` instance.
- The strictly full weak Serre subcategory is its object predicate
  `P : ObjectProperty ...`. The five existing classes `ContainsZero`,
  `IsClosedUnderIsomorphisms`, `IsClosedUnderKernels`, `IsClosedUnderCokernels`,
  and `IsClosedUnderExtensions` give exactly the node's closure conditions.
  In particular this does not demand closure under all subobjects or quotients.
- The covering subset is `B : Set C`. `_hB` says each object has an actual
  covering presieve whose domains belong to B, including empty coverings.
- `_hlocal` quantifies separately over every V in B, then existentially over
  its integer d and collection Cov of covering presieves. Its first conjunct
  says Cov consists of actual J-coverings. Its second says that every covering
  T has a refinement S in Cov: `S ≤ Sieve.generate T`, i.e. each S-arrow
  factors through a T-arrow. Its final clause quantifies over every domain W
  of each such S, every integer p>d, and every F with P F.
- The last clause of `_hlocal` is precisely H^p(W,F)=0, computed as the homology
  of termwise sections of a K-injective resolution of F[0]. It quantifies over
  every such resolution `ι : singleFunctor ... 0 |>.obj F ⟶ K`, with
  `K.IsKInjective` and `QuasiIso ι`. It uses the existing forgetful, sheaf-to-
  presheaf and evaluation functors. Existence of these resolutions follows
  from the recorded resolution theorem; no existential choice or arbitrary
  replacement of the section functor is made. Integer negative cohomology
  is canonically zero, so integer indexing adds no vanishing condition.
- `X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules R) ℤ` is the specified strict
  tower of complexes; `X.asFunctor.obj (op n)` is its level-n complex and
  `X.asFunctor.map (homOfLE (Nat.le_succ n)).op` its actual transition.
  `_hbounded : ∀ n, ∃ b, ...` asserts only bounded-below cohomology of each
  term; b can depend on n. `_hP` says all level cohomology objects lie in P.
  These are exactly membership in D^+_S, with no requirement that complex
  terms themselves vanish below b.
- `threshold : ℤ → ℕ` is n_j, and `_hstationary` says the actual degree-j
  homology transition is invertible for every n at least that threshold.
- `I` and `ι : X ⟶ I` range over any K-injective tower resolution, with
  `_hI : I.IsKInjective` and `[QuasiIso ι]`. The object
  `DerivedCategory.Q.obj (limit I.asFunctor)` computes the stipulated
  resolution-derived inverse limit. HomologicalComplex limits are computed
  degreewise, so this is termwise inverse limit of the K-injective tower.
  This is a representative presentation of Rlim, not a different notion or
  an additional condition on X. Resolutions exist by the recorded strict
  tower theorem. Naturality and independence of the chosen resolution are
  part of that derived-functor interface.
- The first conjunct of the conclusion says `IsIso` for every j and every
  n with `threshold j ≤ n`, using `DerivedCategory.homologyFunctor ... j`.
  The map is `Q.map (limit.π I.asFunctor (op n))` followed by the inverse of
  `Q.map` of the evaluated resolution map. Evaluation is exact and hence
  preserves quasi-isomorphisms; Mathlib supplies its invertibility directly
  when written via `Functor.mapHomologicalComplex` of evaluation. Thus this
  is exactly the canonical projection Rlim X -> X_n, not an arbitrary map
  between its cohomology objects.
- The second conjunct is `∀ j, P (H^j(Q(limit I.asFunctor)))`, exactly the
  final D_S membership assertion. No uniform bound on the limit is asserted.

Statement dependencies read and used:

- `def-weil-size-convention`: metatheoretic convention, no declaration;
  rendered by explicit c, v, r, w and the size hypotheses above.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: recorded site interface.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: the actual sheaf-of-modules category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`: localization and size.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`: the
  K-injective tower-resolution computation, existing derived functor, and
  Roos triangle, without exactness of module-sheaf products.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimit` / `IsDerivedLimitTriangle`, exposed through
  the preceding import: the stipulated Roos interpretation of this computation.

Plain proof imports include the recorded modules of
`prop-pur-kinjective-resolutions-exist`, the two sheafification facts, module
sheafification, local sheafification sections, derived sections and limits,
eventually-isomorphic first derived limits, and both Milnor factorization
lemmas. Their signatures and docstrings were read. The proof dependency
`lem-sfb-ringed-bounded-below-section-window-comparison` has no Lean record
in the read DAG, so it has no module to import yet; it is not a statement
prerequisite, and no substitute theorem is introduced. Its use remains in
the complete seven-step proof docstring for stage 3.

Edge cases checked before and after elaboration: the zero weak Serre class;
zero tower; constant tower with threshold zero (projection is identity after
resolution comparison); negative degrees; negative d (the integer formulation
is legitimate because negative cohomology of F[0] vanishes); empty site and
empty covering families; differing lower bounds tending to minus infinity;
stationarity thresholds varying arbitrarily with j; and a value n equal to
its threshold rather than strictly larger. The conclusion is for all such n,
not just a finite-window threshold depending on V. No exact-products assumption
is present. No STATEMENT-DISPUTED issue or node correction was found.

Searches for existing declarations, 2026-10-24:

- `msearch.py ... leanfinder "Cohomology of derived inverse limit of bounded
  below sheaf complexes with eventually constant cohomology and local
  cohomological bounds"`: eight hits, including Sheaf.H, cohomologyPresheaf,
  and bounded-support facts for DerivedCategory; none states this theorem.
- `msearch.py ... loogle '"homologyFunctor", "limit"'`: zero hits.
- `msearch.py ... grep 'eventually.*(homology|cohomology)|((homology|cohomology).*eventually)|[Mm]ilnor'`:
  three unrelated Mathlib hits (CM5a import, ElladicCohomology prose, and
  PoincareConjecture). No local-bound stationary-limit theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the exact node id
  and `olsson.laszlo`: no matches. Concept searches for weak Serre classes,
  stationary cohomology, local bounds, and derived limits found reusable
  ObjectProperty closure classes, SiteTruncationDerivedLimit, and the recorded
  strict-tower and derived-section modules; none states the item.
- Mathlib sources for ObjectProperty.Kernels, ObjectProperty.Extensions,
  Functor/evaluation of complexes, HomologicalComplexLimits, and the derived
  localization were inspected for the exact notions used. The proposed full
  declaration name has no existing match in either project root.

Validation: the prescribed scompile.py compiled the module both as a sandbox
probe and under its library module name, cleanly (about two seconds each).
No diagnostic commands, file-local notation, private helpers or local instances
remain. Every variable and universe is explicitly bound.

## Second reading by N5

A separate in-thread rereading of the node, source and final file checked all
clauses above; no second agent was started, as the dispatcher brief prohibits
it. The maintainer's independent review remains the independent reading.

The rereading specifically checked the direction of the projection: it starts
at Q(limit I_n), goes to Q(I_n), then through Q(ι_n) inverse to Q(X_n).
The first compiler pass could not infer the quasi-isomorphism of the evaluation
written as the component of complexOfFunctorsToFunctorToComplex. The final
expression uses the identical evaluation map written as mapHomologicalComplex,
for which the existing exact-functor instance applies. This changes no
mathematical hypothesis. Parsing fixes to this expression were recompiled.

The weak Serre conditions are the kernel/cokernel-of-maps-between-members
conditions, not full Serre conditions. The cofinal collection is existential
per V, its members really cover, and refinement is factorization through the
original covering. Both boundedness and stationarity retain their independent
index quantifiers. The two conclusion clauses exactly match the node. No
statement correction, dependency repair or new definition was necessary.
