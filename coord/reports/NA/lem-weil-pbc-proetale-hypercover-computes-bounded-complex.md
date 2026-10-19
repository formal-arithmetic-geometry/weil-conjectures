## Worker report

The delivery states `AlgebraicGeometry.Scheme.ProEt.hypercover_computes_boundedBelow_complex`
in `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`, and adds the
explicit, non-hollow total-section functor in
`Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal`. All four new theorem proofs are
`sorry`; every definition and the transported preadditive instance is given in full.
No node statement was corrected, no dependency record replaced, and no source
checkout was modified. No local Lean or Lake invocation was made.

Clause-by-clause reading:

- Scheme, site, sizes: `(X : Scheme.{u})`, `X.ProEt`, `topology X`, coefficients
  in `CommRingCat.{u + 1}` and module carriers in universe `u + 1` use the recorded
  pro-etale convention. `universe w u` and the explicit `HasDerivedCategory.{w}`
  binder allow every chosen derived-category morphism universe. That binder is
  the chosen localization, not a mathematical restriction; the standard localization
  supplies it. There is no hypothesis on X or W being qcqs or affine.
- Commutative ring sheaf: `R : Sheaf (topology X) CommRingCat.{u + 1}`. The explicit
  `sheafCompose ... (forget₂ CommRingCat RingCat)` forgets commutativity only to use
  Mathlib's module-sheaf category. `ringedSiteModules` is the dependency's transparent
  abbreviation of `SheafOfModules`, with no copy of the category.
- Site object and augmentation: `W : X.ProEt` and
  `U : SimplicialObject (Over W)`. Working in the slice imposes exactly the required
  compatibility of every face and degeneracy with the augmentation.
- Weak contractibility: `hweak` says that every epimorphism of full-site set sheaves
  is surjective at every `U _⦋n⦌`. This is exactly the dependency's predicate;
  it is not weakened to epimorphisms of abelian or module sheaves.
- All-degree hypercover: `hzero` is the epimorphic representable augmentation;
  `hone` uses the limiting two-object fan in `Over W`, hence the fibre product over
  W; `hhigher` uses the dependency's `matchingBoundaryIndex` multicospan for degree
  `n + 2`. Each matching map is required to have the actual faces as projections,
  and its Yoneda map is epimorphic. These are verbatim the matching conditions
  in the recorded affine-acyclic hypercover declaration, with its extraneous
  existence/affineness/qcqs clauses omitted because here U is given.
- Strict lower bound: each `E F J L : CochainComplex.Plus (ringedSiteModules ...)`
  carries `∃ n : ℤ, IsStrictlyGE n`. This means vanishing of the TERMS below n,
  exactly as in the node, and permits independent lower bounds for each complex.
- Total terms and signs: `hypercoverSections` restricts module presheaves to
  `Over W`; `Over.mkIdTerminal.op` then gives a presheaf of `R(W)`-modules.
  Precomposing with `U.rightOp` produces its cosimplicial sections. The actual
  implementation of `AlgebraicTopology.alternatingCofaceMapComplex` has differential
  `∑ j : Fin (p+2), (-1 : ℤ)^j • X.δ j`. `embeddingUpNat.extendFunctor`
  makes its negative terms zero. Applying rows termwise to E gives coefficient
  degree first, and `HomologicalComplex₂.flipFunctor` exchanges the two directions.
  `totalFunctor` therefore uses horizontal delta and vertical `(-1)^p d_E`.
  Its diagonal coproduct is precisely the stated direct sum. There are only
  r-N+1 possibly nonzero terms for r≥N and none for r<N. The construction is
  genuine Mathlib totalization, not a chosen complex with unproved properties.
- Derived isomorphism: the first conjunct produces a family `c`. For every E and
  bounded-below termwise-injective J, every quasi-isomorphism `i : E.obj ⟶ J.obj`
  gives `Q.obj (T.obj E.obj) ≅ Q.obj (evaluation(W).obj J.obj)`. The target is
  exactly the node's DEFINITION of `RΓ(W,QE)` by a chain resolution; no independent
  invented derived functor is used. Bounded-below injective complexes are K-injective,
  so adding a redundant K-injectivity hypothesis is unnecessary. Existence of these
  resolutions is the cited resolution node, after passing to the size-convention
  skeleton; the theorem applies to every choice, without choosing construction data
  from an unresolved existence theorem.
- Naturality and independence: for every coefficient chain map f and every map a
  between bounded-below injective resolutions, the premise
  `Nonempty (Homotopy (i ≫ a.hom) (f.hom ≫ j))` imposes the correct derived square,
  rather than requiring strict chain equality. The equation says
  `Q(T f) ≫ c_F = c_E ≫ Q(a(W))`. Setting f to the identity compares any two
  resolutions. The K-injective Hom bijection realizes every derived coefficient
  morphism by such a square, while the final quasi-isomorphism clause permits
  localization, so this expresses naturality in the derived complex as well.
- Quasi-isomorphism invariance: the second conjunct universally quantifies E and F
  with independent lower bounds, and says
  `QuasiIso f.hom → QuasiIso ((hypercoverTotal ...).map f.hom)`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its defining source fixes the
  same `Scheme.ProEt`, `ProEt.topology`, module universe and commutative-ring forgetting
  used here. Arbitrary R, as required by this node, replaces its constant-ring case.
- `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover`:
  `AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_hypercover`;
  the full signature and docstring supply the set-sheaf and matching predicates.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`:
  `SheafOfModules.exists_boundedBelow_injective_resolution`, imported for stage 3.
- `Sheaf.CategoryTheory.DoubleComplexTotal`: Mathlib's `HomologicalComplex₂.total`
  and the signed total convention; imported for stage 3.
- `Sheaf.Algebra.Homology.FirstQuadrantTotalComparison`:
  `HomologicalComplex₂.quasiIso_totalMap_of_columns`, imported for stage 3.
- `Mathlib.CategoryTheory.Sites.EpiMono` and `.LocallySurjective`:
  `Sheaf.isLocallySurjective_iff_epi'` and `Sheaf.isLocallySurjective_iff_epi`,
  imported for the exact-evaluation proof.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective`, and
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`.
- The size-convention node has no declaration: its record explicitly instructs
  citers to state the universes directly.
- `lem-weil-pbc-ringed-hypercover-injective-augmentation` has no Lean record yet;
  its future proof import is omitted, as required for an unstated proof dependency.
  This does not prevent stating the theorem. The whole eight-step proof is in
  the theorem docstring, including that augmentation input.

Edge cases checked: arbitrary (including negative) lower bound; distinct bounds
for E,F,J,L; zero coefficient sheaf or complex; zero coefficient ring; empty scheme
or site object; degree r<N; p=0 and the two cofaces into p=1; matching degrees 0,
1 and all degrees ≥2; no assumption that underlying abelian sheaves of injective
module sheaves are injective. Empty schemes and zero rings are not excluded by
any binder. Extending the alternating complex by zero does not shift or negate
its differential. Transposition is done BEFORE totalization, so the sign is in
the simplicial coordinate p, not in the coefficient coordinate q.

Searches (the new node's `mathlib_searches` records the queries and returned names):

- msearch leanfinder: “A bounded below complex of module sheaves on a site is
  computed by total sections of a weakly contractible hypercover”: eight hits
  concerning sheaf cohomology, Mayer–Vietoris squares and one-hypercover sheaf tests;
  none states this result or defines this total functor.
- msearch loogle: `AlgebraicTopology.alternatingCofaceMapComplex,
  HomologicalComplex₂.total`: zero hits. Both constructions were found by reading
  Mathlib and are reused in full.
- msearch grep `hypercover|derivedEvaluation|hypercoverTotal` under
  `Algebra/Homology`: zero hits.
- msearch leansearch: “Total complex of sections of a complex of sheaves of modules
  on an augmented simplicial object”: service unavailable, Internal Server Error.
- rg of the source project for the item id and the proposed names, and rg of
  Mathlib, `lean/Sheaf` and `dag/lean_names_upstream.json` for those names: no match.
  Broad hypercover search found finite-degree cover APIs and specialized etale
  open-cover material, not this pro-etale arbitrary-ring-sheaf totalization.
- `blueprint_refs.py search 'hypercover total'`: zero blueprint matches. DAG text
  grep for total-section/section-total expressions found this item and specialized
  open-cover Cech nodes. In particular `def-sc-alternating-cech-total-complex`
  concerns a finite open cover of a ringed space and does not define this functor.
- Read `coord/pefw-upstream-framework.md` and searched the actual copied pro-etale
  framework in `lean/WeilConjectures`: no competing totalization or theorem.

No STATEMENT-DISPUTED issue was found. Single-file server compilation validates
both delivered modules, in dependency order, with nice 19, two threads and the
60-second per-file limit. All errors and non-sorry warnings have been repaired.

## New nodes

`def-weil-pbc-proetale-hypercover-total` defines total sections for an augmented
simplicial object of the pro-etale site, over an arbitrary sheaf of commutative
rings. Its source is the bicomplex in the second paragraph of the proof of Stacks
09A2. The node records the three search kinds plus unavailable LeanSearch, and
cites the existing scheme, site, size, simplicial-object, module-sheaf and total
complex nodes. Its module defines section cosimplicial objects, alternating rows
and the signed total functor by compositions of existing Mathlib constructions.
The three named additive-law theorems are the only postponed proof obligations;
they have proof docstrings and this node's blueprint tag. The cosimplicial module
preadditive instance transports the existing functor-category structure directly.
No definition chooses data from `sorry`, and no existing notion is copied.


## Second reading by NA

Independent second reader: I read the original node, both sandbox modules, the
new definition node, Stacks proetale.tex at lemma-compute-cohomology (09A2), and
sites-cohomology.tex at lemma-w-contractible (0946), including the preceding
weak-contractibility definition. Neither source assumes qcqs or affineness for
this computation. Tag 09A2 is stated for abelian sheaves; the node explicitly
requests its ringed-module version. Exact module evaluation and injective module
augmentation are the two appropriate inputs for that version, as the proof says.

Object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Arbitrary scheme X: `(X : Scheme.{u})`; matches. The recorded
   `proEtaleDerivedCategory` abbreviation was opened: its Mathlib `X.ProEt` and
   `ProEt.topology X` are exactly the site used here. I also opened Mathlib's
   Proetale source: objects are weakly etale schemes over X, topology generated
   by fpqc weakly etale coverings, with finite limits and subcanonicity.
2. Arbitrary commutative ring sheaf R: `Sheaf (topology X) CommRingCat.{u+1}`;
   matches, without a constant-coefficient or field restriction. The displayed
   `sheafCompose` forgets commutativity only. I opened `ringedSiteModules`:
   it is precisely `SheafOfModules`, so the objects and linear maps are correct.
3. Site object W and augmented simplicial U: `(W : X.ProEt)` and
   `(U : SimplicialObject (Over W))`; matches. Slice morphisms impose all
   augmentation compatibility, including the degeneracies.
4. Every U_p weakly contractible: `hweak` quantifies over every epimorphism of
   full-site set sheaves and requires sectionwise surjectivity; matches the
   recorded affine-acyclic-hypercover declaration, which I read in full. Its
   existence, affine and qcqs conditions are correctly absent for a GIVEN U.
5. All-degree hypercover: `hzero` covers degree zero; `hone` gives a limiting
   two-object fan in the slice, hence the fibre product over W; `hhigher`
   gives every degree n+2. The matching maps have the actual face projections
   and are epimorphic after Yoneda. I opened `matchingBoundaryIndex`: its
   pairwise overlap maps are d_(j-1) and d_i, the proper-face compatibility
   equations. Subcanonical Yoneda preserves these finite limits. Matches.
6. Coefficient complex with terms zero below SOME integer: each coefficient
   is `CochainComplex.Plus (ringedSiteModules ...)`. I opened Mathlib's Plus:
   this is the full subcategory defined by `exists n, IsStrictlyGE n`.
   E, F, J, L have independent bounds, including negative ones. Matches.
7. Sections over the augmentation ring: `hypercoverSections` restricts to
   `Over W`, uses its terminal identity object and then `U.rightOp`.
   I opened `forgetToPresheafModuleCatObjObj` and its map: they use actual
   `ModuleCat.restrictScalars` and the original restriction maps. Thus the
   ring is exactly R(W), with the right linear face maps. Matches.
8. Alternating differential and total terms: `hypercoverSectionRows` uses
   Mathlib's alternating coface complex, whose `objD` I read: sum over
   `Fin (p+2)` of `(-1 : integer)^j` times the coface. Extension by zero
   has zero negative simplicial terms. The coefficient complex is mapped
   termwise, flipped, and passed to `totalFunctor`. I read total's two
   differential components and the up-integer tensor signs: epsilon_1=1,
   epsilon_2=(-1)^p. Therefore this is the requested coproduct total and
   delta+(-1)^p d, not a total with the coefficient-degree sign. Matches.
9. Derived comparison: the family `c E J hJ i hi` is an isomorphism from
   `Q(T(E))` to `Q(J(W))` for EVERY bounded-below termwise-injective chain
   resolution i. This is exactly the node's resolution definition of derived
   evaluation. The explicit `HasDerivedCategory` chooses the localization;
   its standard instance supplies it. No extra geometric hypothesis appears.
10. Naturality: for f:E to F and a:J to L, the premise is
    `Nonempty (Homotopy (i >> a.hom) (f.hom >> j))`, and the conclusion is
    `Q(T f) >> c_F = c_E >> Q(a(W))`. This permits homotopy-commuting
    resolution squares. I opened `Qh_map_bijective`; it represents all
    derived resolution morphisms, uniquely up to homotopy. The identity f
    compares two resolutions. This expresses naturality and independence
    without selecting an object from an unproved nonunique existence claim.
11. Quasi-isomorphism invariance: the final conjunct universally quantifies
    E,F,f and asserts `QuasiIso f.hom` implies `QuasiIso (T.map f.hom)`;
    matches, with no common-bound assumption imposed on the input.

New-node review: `def-weil-pbc-proetale-hypercover-total` records the genuine
section-bicomplex construction in the second paragraph of 09A2. Its statement
introduces X,R,W,U and E, specifies scalar restrictions, the alternating rows,
the signed coproduct total and its finite effective diagonals. Its module
implements those operations by existing functors, rather than axiomatizing a
complex with these properties. The transported preadditive instance contains
real structure. The three additive-law obligations are named sorry theorems
with proof explanations; no definition has a sorry body or an arbitrary chosen
object. Its chapter/unit, created record, ancestor/via, cited statement
dependencies, empty proof fields, search records and lean_audit fields satisfy
the new-node rules. It is cited by the delivered item. No dependency module
is being delivered. Existing proof-dependency signatures were opened, including
bounded-below injective resolutions and first-quadrant total comparison; the
former needs passage to the stipulated small skeleton, the latter natural
reindexing of the common lower bound, both explained in the theorem docstring.
The injective-augmentation proof node has no statement module yet and is
correctly not imported. The theorem docstring follows all eight node proof steps.

Edge cases: W or X empty; zero ring and zero complex; arbitrary characteristic
(including 2); p=0 and its two cofaces; higher matching n=0 (degree 2);
arbitrary negative lower bounds; r<N, when every summand is zero; different
bounds for E,F,J,L. No nonempty or nonzero assumption is present. There is no
external index set here; the possibly infinite diagonal has only finitely many
nonzero terms for bounded-below coefficients. Scheme universe u, section
universe u+1 and localization universe w follow the recorded convention and
leave no free implicit variable. No same-bound, Noetherian or finiteness
hypothesis was added.

Independent searches: msearch leanfinder, "Cohomological descent by an acyclic
simplicial resolution for a bounded below complex of sheaves of modules", gave
eight generic injective-resolution/K-injective hits, none this statement.
msearch loogle, `"alternatingCofaceMapComplex"`, returned the existing alternating
coface construction and its component lemmas, which this delivery already uses.
I ran rg with `acyclic.*hypercover`, `hypercover.*[Tt]otal`,
`[Tt]otal.*hypercover`, and the proposed declaration stems in Mathlib, upstream
WeilConjectures, the exact copied lean/WeilConjectures framework, and lean/Sheaf.
The only nearby theorem is `AlgebraicGeometry.hypercover_cohomology`; I opened
its module and signature: it concerns colimits over finite split ETALE
hypercovers and individual coefficient sheaves on qcqs schemes, not a fixed
weakly contractible PRO-ETALE hypercover or a bounded-below variable-ring
complex. It cannot replace this statement or construction. DAG concept search
likewise finds specialized Cech totals, not this general section functor.
I read coord/pefw-upstream-framework.md and opened ModuleObject/Basic.lean:
its condensed ring objects and scalar maps do not supply this total functor.
The worker's LeanSearch failure is recorded, not claimed as a successful search.

Verdict: no mathematical mismatch found; no Lean or node repair was needed.
Only this independent-reading section was appended. The lean.statement strings
were checked verbatim against both source signatures; line widths are at most
100. All four theorem bodies remain sorry, and all constructions are real.
Both delivered modules compiled cleanly through scompile.py on the server,
separately in dependency order, nice 19, two threads, 60 seconds per file:
ProEtaleHypercoverTotal 1.6 seconds; ProEtaleHypercoverComputesBoundedComplex
3.5 seconds. No warning or error was emitted.
