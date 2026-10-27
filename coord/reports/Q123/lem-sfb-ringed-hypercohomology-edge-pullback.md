## Worker report

The module `Sheaf.CategoryTheory.RingedHypercohomologyEdgePullback` states
`SheafOfModules.RingedHypercohomology.edge_pullback`. Its one postponed theorem
has proof `sorry`; every helper definition has actual data. The original statement,
proof, proof dependencies and all other node fields are preserved. Four already-landed
definition nodes are added to statement dependencies to record the exact interfaces used.
There are no new nodes or dependency repairs.

Hypotheses and clauses, checked against the entire node statement:

- A ringed site small in the common coefficient universe is `Site.{u,w}`. Its `C`
  and `SmallCategory C` are in `u`, its `A` is a `CommRingCat.{u}` sheaf, and its
  module category is the recorded `ringedSiteModules.{u,u,u,u}`. The hom universe
  `w` of the chosen unbounded derived category is independent. The `closed`,
  `model`, `symmetry`, and `coherence` fields present the existing derived tensor;
  they do not assert flatness of a structural map or boundedness of any object.
- The source ringed site in the node is `Y`; the primed site is `X`.
  `g : Morphism X Y` is exactly the recorded `RingedToposMorphism X.ring Y.ring`,
  allowing arbitrary geometric morphisms rather than only functors of presented
  sites. `l : Lift g` uses the normalized canonical derived adjunction and tensor
  model of the already-landed comparison-data interface. Its ordinary adjunction
  is tied to the underlying geometric adjunction by `ordinary_adjunction`, and its
  derived adjunction by `canonical_adjunction`. These are the node's specified
  canonical constructions, not an additional flatness or exactness hypothesis.
- `K : Y.D` and `D : X.D` are arbitrary unbounded derived objects. `cohomology`
  is exactly `DerivedCategory.homologyFunctor` on module sheaves. In particular
  there is no nonnegative or boundedness restriction on K or D.
- The coefficient ring A is `RingedSiteCup.scalars Y.corner`, the existing ring
  of compatible families. `derivedGlobalSections` is module-valued RΓ, computed
  by K-injectives. `globalAbelianDerived` forgets only its scalar action by the
  exact scalar-forgetful functor on derived categories. This retains the precise
  underlying hypercohomology groups used in the node and allows comparison of
  the source and target global scalar rings without equating them.
- `eY` and `eX` have type `RΓ(-) ⋙ H^n ⟶ H^n ⋙ coefficientSections`. The component
  on each K-injective representative is fixed by `EdgeSpec`: global cycles are
  included in sections of sheaf cycles, then quotiented by boundaries. The
  normalization explicitly uses `globalAbelianUnit` and
  `DerivedCategory.homologyFunctorFactors`. Thus the witnesses are the specified
  cocycle-to-cohomology-sheaf edges; they are not arbitrary maps. Their natural
  transformation types include naturality for every derived morphism.
- `r n` has type `H^n ⋙ l.edge.pullback ⟶ l.edge.left ⋙ H^n`. Ordinary pullback
  is the existing scalar extension after exact inverse image: its `object_eq`
  and `map_eq` fields use the recorded `changeOfRings`, not a new category or
  functor. `PullbackSpec` fixes r on every flat-term K-flat P: pull back the
  cycles inclusion, factor through cycles of the pulled-back complex, and
  quotient by boundaries. This is precisely the scalar-tensor/cocycle pairing
  κ^(0,n) with H^0(O'[0])=O', evaluated after the exact inverse image. The map z
  is uniquely fixed by its monic cycles inclusion; the induced map is fixed
  because pullback preserves the homology quotient epimorphism. The isomorphism
  v is fixed by `v.inv = l.alpha P`, the canonical left-derived comparison.
  Equivalently the local formula is b tensor [z] maps to [b tensor z]. Local
  lifting and sheafification are built into cycles and homology in module sheaves.
  This does not require inverse image of K itself to have flat terms; one uses
  flat-term K-flat P to compute the indicated derived object. The NatTrans type
  includes r's naturality in K in every integer degree.
- `θ` is the ordinary comparison Γ(g_*F) ≅ Γ'(F).
  `SectionsComparisonSpec` normalizes its inverse through the actual module
  adjunction and the canonical ordinary unit isomorphism. Evaluating sections
  via the existing `globalUnderlyingSections` identifies this with the usual
  compatible family. `ordinaryUnit` chooses the isomorphism from the recorded
  unit-and-scalar-action normalization, which determines that object up to the
  equality needed here; it is not chosen from a bare Nonempty.
- `c : Rg_* ⋙ RΓ ≅ RΓ'` is the derived Leray comparison, normalized by
  `LeraySpec` on every K-injective representative and the specified right-derived
  units. Its comparison at complexes is the actual termwise image of θ.
- `hypercohomologyPullback l c t n` is H^n applied to the composite of RΓ of
  the derived-adjunction unit, c, and RΓ'(t). Thus it is exactly P_(g,t)^n;
  t has exactly type `l.edge.left.obj K ⟶ D`.
- The identity is quantified over `n : ℕ`, cast to ℤ in every cohomology functor,
  and every element x. This is exactly n ≥ 0, including n=0. Its left side is
  `(eX n).app D (hypercohomologyPullback ... x)`. Its right side is Γ' applied
  to `(r n).app K ≫ H^n(t)` at `sectionPullback ... ((eY n).app K x)`.
- `sectionPullback` is pullback of the Hom(O,F) representative of a section,
  preceded by the inverse ordinary-unit comparison and then evaluated at 1.
  This is exactly s maps to 1 tensor g^(-1)s, with no final object needed.
- The final two conjuncts give naturality of P under a map K→K' (with the
  corresponding precomposition of t) and under postcomposition t→t≫a.
  Together with the NatTrans naturality of e and r, these express the stated
  naturality of the displayed identity in K and t. They assert no invertibility
  of r. Maps e and r exist in all integer degrees as the node specifies; only
  the claimed compatibility identity is restricted to nonnegative degrees.

Dependencies actually used, with exact modules and declarations:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: site convention, with existing
  `CategoryTheory.GrothendieckTopology` and `Sheaf` used throughout the imports.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  the existing K-injective RΓ convention, publicly imported by the cup interface.
- `Sheaf.CategoryTheory.RingedSiteModuleCupProduct`:
  `SheafOfModules.RingedSiteCup.globalUnderlyingSections`, `globalAbelianDerived`,
  `globalAbelianUnit`. Publicly re-exports the recorded global-sections,
  cohomology-pairing and derived-adjunction definitions.
- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, used by `Morphism`.
- `Sheaf.Paper.ProjectionMateExact`: `RingedTensorCorner.mateModules`,
  `.mateDerived`, `.mateFlat` and the canonical derived-adjunction interface
  of `RingedTensorEdge`, used via `Lift`.
- Added already-landed node `def-sfb-ringed-derived-comparison-data`:
  `Sheaf.SixFunctors.RingedDerivedComparisonData`,
  `CategoryTheory.RingedDerivedComparisons.Site`, `Morphism`, `Lift`.
- Added already-landed node `def-sfb-coefficient-module-global-sections`:
  `Sheaf.CategoryTheory.DerivedSectionsScalarCoherence`,
  `CategoryTheory.CoefficientDerivedSections.coefficientSections` and
  `coefficientComplexSections`.
- Added already-landed node `def-sfb-ringed-site-global-derived-adjunction`:
  `Sheaf.CategoryTheory.RingedSiteGlobalDerivedAdjunction`,
  `globalSections`, `scalars`, `derivedGlobalSections`.
- Added already-landed node `def-sfb-ringed-site-cohomology-tensor-maps`:
  `Sheaf.CategoryTheory.RingedSiteCohomologyTensorMaps`,
  `cohomology`, `representativeCohomology`, `cohomologyPairing` and its
  cocycle-normalized specification. PullbackSpec is the scalar-extension
  specialization of that cocycle formula, not a second cohomology pairing.
- Proof-only import `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`.
  The proof prerequisite `lem-sfb-ringed-hypercohomology-shifted-unit` has no
  recorded Lean declaration at the time of writing. It is not needed to type
  the theorem, is left as the unchanged proof dependency, and its role is
  explained step by step in the theorem docstring. No substitute axiom or
  duplicate shifted-unit definition is introduced.
- `def-weil-size-convention` is a metatheoretic convention; explicit u,w provide
  its Lean rendering, with no declaration required by that node's record.

Sources read: Stacks sites-cohomology.tex at lemma-sheafification-cohomology
(0BKV) and lemma-Leray-unbounded (0D6H), including both proofs. Also the current
blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, part (3),
for the inherited composition-of-direct-images ancestry. The nonflat edge identity
is the existing node's explicitly agent-stated shifted-unit argument; the blueprint
itself is not changed.

Searches (prescribed msearch.py wrapper, Q123 and the full item id):

- LeanFinder: `hypercohomology edge map compatible with derived pullback of sheaves
  of modules`: 8 hits, Mayer--Vietoris and hypercover maps, no matching statement.
- Loogle: `SheafOfModules.pullback, HomologicalComplex.homology`: 0 hits.
- Mathlib grep: `hypercohomology|edgeMap|edge_map`, `CategoryTheory`: 0 hits.
- LeanSearch: `hypercohomology edge map cocycle to cohomology sheaf naturality under
  derived pullback`: 8 hits (group-cohomology cocycle maps, injective-resolution
  comparison, homology connecting-map naturality and mapping-cone cocycles), no
  ringed-topos unbounded scalar-extension edge assertion.
- rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for `RingedHypercohomology|ringed.*hypercohomology|hypercohomology.*edge|edge.*hypercohomology`:
  the bounded-below `HypercohomologyLeftEdge` family, global-Hom comparisons,
  and the known zeroth-hypercohomology modules. Read the left-edge definitions
  and its naturality signature: they require bounded-below/nonnegative models
  and give no nonflat ringed-topos pullback comparison, so are not this statement.
- rg for the exact node id in `lean/WeilConjectures` and `lean/Sheaf`: no match.
- Read all recorded dependency signatures and docstrings and the additional
  landed interfaces listed above. Checked current server comparison-data source
  with `scompile.py --source Sheaf.SixFunctors.RingedDerivedComparisonData`.

Edge cases checked before finalizing: n=0 (no positive-degree assumption);
negative-degree and arbitrarily unbounded K and D; zero object and zero t; the
empty site and zero coefficient rings; identity g and t; a point with structural
map Z→F₂ and K=Z[0], Z/2[0], and the flat complex [Z --2--> Z] in degrees 0,1.
For the last example the cohomology pullback map can fail to capture all cohomology
of the derived pullback, and the statement correctly makes no isomorphism claim.
Cycles are formed in module sheaves and scalar extension is only used as a
right-exact functor, so no exactness of tensor pullback is smuggled in. In the
empty-site/zero-ring cases the compatible families and all equations still make
sense. No final object, enough-projectives hypothesis or extra site functor occurs.

Validation: scompile.py compiled both sandbox and library-path forms cleanly under
the normal 60-second per-file limit (5.0 s and 6.3 s after the sole long-line warning
was repaired). No warning remains. Dry run and delivery use deliver2.py below.
No STATEMENT-DISPUTED flag or source-based statement correction was needed.

## Second reading by Q123

A separate pass over the complete node and final module checked the correspondence
above. This was a second pass by this worker, not a separate agent: the dispatcher
brief expressly forbids starting another agent and assigns the independent review
to the maintainer. The check found and repaired one line over 100 characters.

The substantive checks were direction of r (ordinary pullback of Hⁿ to Hⁿ of derived
pullback, with no inverse); order of its composition with Hⁿ(t); forgetting only the
external scalar action of RΓ; normalization of both θ and the Leray isomorphism;
the n=0 case; naturality in both a map of K and postcomposition of t; and the fact
that the representative predicates are conclusions specifying the witnesses,
not hypotheses allowing an arbitrary map. All match the node's clauses. The
four added dependencies already have landed Lean records and are the exact
interfaces used. The original mathematical statement and its proof plan remain
unchanged. Every helper docstring carries the owning node id and source, and
the sole theorem docstring contains all four natural-language proof steps.
