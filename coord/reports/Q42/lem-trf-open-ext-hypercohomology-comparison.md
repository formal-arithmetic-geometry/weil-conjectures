## Worker report

The module `Sheaf.AlgebraicGeometry.OpenExtHypercohomologyComparison` states
`AlgebraicGeometry.openExt_hypercohomology_comparison`. Its only postponed theorem is
this node's theorem, with a six-step natural-language proof in its docstring.
All auxiliary definitions are the composition of existing functors, an abbreviation
for the shifted local Hom group, and canonical shift/restriction transport.

Clause-by-clause correspondence:

- A ringed space and its commutative structure sheaf are `X : RingedSpace.{u}`,
  `X.sheaf`, and the recorded `moduleRings X`. The open-covering site is
  `Opens.grothendieckTopology X`. No local-ring, scheme, separation, or finiteness
  hypothesis is imposed.
- The common size convention is explicit `universe u w`. Module values, rings, and
  the opens use `u`; `HasDerivedCategory.{w}` on X and every open chooses the common
  morphism size. No equality between `u` and `w` is imposed. The existing presheaf
  localization uses its standard size; the additive equivalence may relate group
  carriers in different universes.
- Arbitrary unbounded `K,L` are objects of `DerivedCategory (SheafOfModules.{u}
  (moduleRings X))`. There is no boundedness, perfection, or local-freeness binder.
- `A=RHom(K,L)` is the existing `CategoryTheory.derivedInternalHom` applied to the
  pair `(op K,L)`. It is publicly re-exported by the dependency's recorded module
  `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`; the ordinary-module
  abbreviation in that module is not used on sheaves.
- `K_U,L_U` are exactly the objects of `overFunctor.mapDerivedCategory`, using the
  standard exact-additive structures from the recorded restriction module.
  `localDerivedExt` is just an abbreviation for their shifted Hom group.
- `H^i(U,A)` and its open restriction are the existing
  `AlgebraicGeometry.RingedSpace.ringedSpaceHypercohomologyPresheaf X i`. This right derives
  the whole abelian presheaf of sections on one K-injective representative, then
  takes homology sectionwise. Thus `.obj (op U)` and `.map j.op` are the specified
  derived evaluation and its canonical restrictions, not ordinary sections of the
  cohomology sheaf. `internalHomHypercohomology` only composes these two functors.
- `i : ℤ` includes every degree. The existential `α`, quantified simultaneously
  over every pair and open, has type `H^i(U,A) ≃+ localDerivedExt ... i U`.
  `≃+` states bijectivity and additivity, including zero and negatives.
- The first conjunct is the displayed open-restriction square for each `j : W ⟶ U`
  and each `a`. `localDerivedExtRestriction` first uses the inverse shift comparison
  on U, applies the recorded `derivedOpenHomRestriction X j` to `(K,L[i])`, then
  uses the shift comparison on W. This is the node's exact conjugation formula.
- The second conjunct is contravariant naturality for every `t : K' ⟶ K` and
  covariant naturality for every `s : L ⟶ L'`. The left arrow is the actual map
  of the RHom/hypercohomology bifunctor. The right side is restricted `t`, then α,
  then the shift of restricted `s`.
- The third conjunct explicitly states successive restrictions for arbitrary
  `V ⟶ W ⟶ U`. Identity restriction follows also from the first square, because
  left restriction is a presheaf map and α is onto. These properties make the
  additive comparisons an isomorphism of the prescribed abelian presheaves.
- The theorem asserts one family of additive equivalences with all the stated
  naturality and restriction properties. Its docstring specifies the canonical
  cocycle construction, exactly as the DAG proof does. The existential family
  is not claimed unique from these naturality properties alone; the signature
  does not separately impose a representative-normalization equation. A fuller
  representative interface was explored but is not part of this delivery.

Dependency declarations read and used:

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `RingedSpace`,
  `LocallyRingedSpace.Hom` (only the general ringed-space portion is used).
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, with the project's Mathlib
  open-covering specialization. No different site is constructed.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules` and its canonical abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and the localization factorization;
  `HomologySequence` supplies `homologyFunctor` and its complex comparison.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; the source defines null-homotopy from every
  acyclic source. `DerivedCategory.KInjective` supplies `Qh_map_bijective`.
- The recorded derived-Hom module publicly imports
  `WeilConjectures.Algebra.Homology.DerivedInternalHom` with
  `CategoryTheory.derivedInternalHom`, `derivedInternalHom_inverts`, and
  `homComplexFunctor`. Its definition is localization of Hom into the fixed
  functorial K-injective replacement. The independent-universe companion is
  re-exported and is not restated.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `rightDerivedFunctorOfQuasiIsoResolutions`, its unit, and its universal property.
- `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`:
  `moduleRings`, all six exact-additive restriction structures, and
  `derivedOpenHomRestriction`; the full definition was read, including its
  inverse-composition comparison followed by `overFunctorMap`.
- `Sheaf.Topology.RingedSpaceHypercohomologyPresheaf`:
  `AlgebraicGeometry.RingedSpace.moduleAbelianPresheaf`,
  `AlgebraicGeometry.RingedSpace.derivedModuleAbelianPresheaf`, and
  `AlgebraicGeometry.RingedSpace.ringedSpaceHypercohomologyPresheaf`. These are owned
  by the existing definition node `def-trf-ringed-space-hypercohomology-presheaf`,
  now cited in `stmt_deps`. The source localization universe remains arbitrary;
  the target standard localization is supplied explicitly inside these definitions.
  The K-injective resolutions are actual functorial resolutions, not theorem-chosen
  data or a parameter supplied to the comparison.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`; the
  published small-site construction and fixed resolution are available through
  the imports. It remains a proof dependency.
- `WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparison`:
  `homComplex_sections_canonical_comparison`, including the full projection
  formula and the cocycle-to-shifted-chain-map formula. It remains a private
  proof-dependency import.

All remaining recorded proof-dependency modules are imported privately, as the
stage requires: K-flat resolution, Hom-complex invariance, K-injectivity of Hom
from K-flat complexes, sectionwise quasi-isomorphism, K-injective open restriction,
and derived two-variable naturality. Their full signatures and proof docstrings
were read. The new imports do not introduce a dependency cycle (a traversal from
the presheaf node through both dependency lists does not reach this item).

Sources read: `literature/stacks-project/cohomology.tex`, lines 10581ff (08DK)
and 10640ff (08DL). The former gives degree zero on every open using K-flat and
K-injective representatives; its proof and the Hom-complex formula give all
integer shifts. The latter states restriction compatibility. The node's six
steps supply the explicit naturality and canonical representative formula.

Edge cases checked: empty open and empty ringed space; K=0 or L=0; i=0, i<0,
and i>0; identity open inclusion; a chain of three equal or distinct opens;
U=top; a one-point ringed space, recovering ordinary derived Hom; arbitrary
unbounded complexes. No cover or vanishing hypothesis, and no restriction to
nonempty opens, occurs in the signature. The proof uses products in the unbounded Hom complex, never a finite sum or a
bounded representative.

Searches actually executed with `msearch.py Q42 <item>` (raw outcomes also appear
in `searches.jsonl`):

- LeanFinder: “For unbounded complexes of module sheaves hypercohomology of derived
  internal Hom equals local derived Hom compatibly with open restriction”:
  8 hits, including `Sheaf.H`, ordinary section naturality, and
  `CohomologyClass.toSmallShiftedHom_mk`; none is this statement.
- Loogle: `SheafOfModules, DerivedCategory`: 0 hits.
- Mathlib grep: `hypercohomology|derivedInternalHom|derivedOpenHomRestriction`:
  0 hits.
- LeanSearch: “Local Ext of unbounded complexes of sheaf modules is
  hypercohomology of derived internal Hom”: 8 hits, on ordinary sheaf Ext,
  injective/projective resolutions, and localization size; no exact match.
- `rg` in both project roots for `hypercohomology`, `derivedInternalHom`,
  derived sections/evaluation, and `derivedOpenHomRestriction`: found the existing
  RHom construction, the precise hypercohomology presheaf, the canonical restriction,
  and more specialized global/coefficient results. Reused the first three.
- The prescribed node-id search in `lean/WeilConjectures` found no match.
  Full-name search found no existing `openExt_hypercohomology_comparison` or
  `localDerivedExt` declaration.

No statement correction, new DAG node, dependency-record repair, or
STATEMENT-DISPUTED flag is needed. Auxiliary comparison definitions belong to this
node and are listed in `lean.declarations`.

## Second reading by Q42

A separate sequential reading by the same worker (the dispatcher forbids spawning
another agent; this is not a claim of an independent reviewer) checked the node
against the final signature and helper bodies. In particular, it checked that the
left side is hypercohomology on a common K-injective representative, not sections
of H^i(A), and that the right restriction uses the recorded conjugation on
(K,L[i]) with both shift comparisons. It checked every variable in the naturality
square, the order of composition for successive restrictions, the independent
morphism universe w, and the six-step canonical construction against proof steps 2–3.
The final signature records the simultaneous additive family and its exact
restriction and two-variable naturality equations. The canonical construction is
specified in the proof docstring; it is not a uniqueness claim about natural
families. Helpers contain no proof placeholder. The only theorem
has proof `by sorry`. The maintainer's independent delivery review remains the
independent mathematical reading required by the dispatcher's workflow.

Initial-delivery validation: the module compiled cleanly through scompile.py in both sandbox
and library module modes (53.6 s and 18.8 s respectively); no warning or error.
Only the expected postponed theorem uses sorry.

## Returned-delivery repair (H2)

The immutable delivery `3cf63b51d89c` cited the theorem node
`lem-trf-unbounded-direct-image-section-presheaf` solely for auxiliary definitions.
Its theorem conclusion was not used. On current main the reviewed definition node
`def-trf-ringed-space-hypercohomology-presheaf` now owns precisely the required
unbounded hypercohomology presheaf. Its Lean source and complete signatures were
read, including the underlying presheaf functor, actual K-injective resolutions,
standard target localization, homology composition, and unit construction.

The repaired module imports `Sheaf.Topology.RingedSpaceHypercohomologyPresheaf`
and composes RHom with `ringedSpaceHypercohomologyPresheaf` instead of the duplicated
`localHypercohomologyPresheaf`. The item's `stmt_deps` replaces the theorem node
with this owning definition node. This meets the requested definition ownership
without creating a second node for the same notion. The existing owning node was
already independently reviewed on main; it is reused and not modified. The theorem
signature, restrictions, naturality, universes, and six-step proof docstring retain
the mathematical statement accepted in the return.

Repair searches: `rg` over `dag/nodes` and `lean/Sheaf` found the owning definition
node and its module; their full contents establish that it is the same notion.
Comparison of the sandbox node with current main found only the intended `lean`
record and extra hypercohomology definition dependency. No unrelated node fields
are changed. All clauses and edge cases above were reread with the owning API.
A traversal of both dependency lists from the owning definition reached 155 nodes
and did not reach this item. The theorem signature was checked against the Lean
record verbatim, and the obsolete module import and API name are absent.

Repair validation: `scompile.py Q42 lem-trf-open-ext-hypercohomology-comparison`
completed successfully for the repaired file in sandbox and library modes, with
no errors or warnings (reported elapsed times including server waiting: 2125.7 s
and 14.3 s). No direct local compilation or project build was run.
