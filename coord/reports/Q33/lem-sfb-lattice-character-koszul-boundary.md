## Worker report

`Sheaf.CategoryTheory.LatticeCharacterKoszulBoundary` states the original node without
changing its statement. Its only postponed theorem is
`Profinite.DiscreteLattice.CharacterBoundary.lattice_character_koszul_boundary`.
The docstring contains all six proof steps, including the positive sign and edge cases.
Supporting records specify, rather than replace, the exact extension and inclusions.
Definitions construct the specified short complex and transport the existing character
class through the existing normalized action equivalence and localization-universe map.

Hypotheses and introduced objects:

- `R : Profinite.CondensedRing.{u}` and `[IsCommMonObj R.X]` render an arbitrary
  commutative condensed ring on the coherent profinite site, allowing the zero ring.
  The source module `Sheaf.Topology.ProfiniteCondensedRing` was read in full.
- `Modules R` is the recorded internal module category, `CategoryTheory.Mod` over this
  ring object. Its tensor unit `𝟙_ (Modules R)` is the regular module R. This is the
  existing module definition, not a new copy. The full Mathlib structure, regular-module
  definition and morphism structure were read.
- Ordinary derived categories use `DerivedCategory.{u + 2}` and `modulesDerived R`.
  The restriction calculus uses u+1. `RestrictionCup.raise`, `raiseFactors`, and
  `cohomologyIso` transport between these localization universes without identifying
  universes or changing coefficients. `raiseCommShift` unfolds `raise` to expose the
  existing exact identity functor's canonical shift comparison.
- `r : ℕ` and `i : Fin r` render the rank and coordinate. `Group r` is precisely
  `Multiplicative (Fin r → ℤ)` with its discrete topology; section actions use its
  existing `ULift.{u}` presentation in the site's universe.
- `a : CondensedDerivedRestriction.Character (RestrictionCup.ring R) (ULift (Group r))`
  is the introduced coordinate character. `ha` fixes its value to n times the unit on
  every section whose ith coordinate is constantly n. A continuous map from a profinite
  space to the discrete lattice has a finite clopen fibre cover, so these equations
  uniquely specify its values on all sections. This is exactly the existing
  `Profinite.DiscreteLatticeCup.coordinateCharacter_exists` specification in
  `Sheaf.CategoryTheory.DiscreteLatticeCupExterior`, which was discovered and read.
  That downstream module is not imported, avoiding a reverse dependency cycle. No
  duplicate character is defined. `a` and `ha` specify the node's introduced d_i;
  they impose no additional assumption on R. `transportCharacterClass` uses the
  existing `characterClass a`, with its positive connecting normalization.
- `K : KoszulModel R r` is the recorded finite subset-coordinate functor; its regular
  trivial-action specialization is the K of the node. `Subsets r a` labels its terms,
  and the dependency's `differentialEntry` fixes exactly the node's signs.
- `M : TriangulatedCup.TriangulatedModel R r K`, `c : Comparison R r K`, and
  `hc : TriangulatedCup.ComparisonProperties R r K M c` give any triangulated and
  invariant-normalized comparison. The `normalization`, `extendsModules` and
  `connecting` fields were read in full. No flat-algebra cup hypothesis is imposed.
- `B : RestrictionCup.Bridge R r` is any recorded normalized equivalence between the
  sectionwise and discrete-action categories. Its underlying, constant-section,
  invariant-inclusion, derived computation-unit, and regular-module normalizations
  identify exactly the same R and its trivial coefficient object.

Conclusions, clause by clause:

- `E : Extension R r i` has the actual underlying biproduct R ⊞ R. Its `action` is a
  monoid homomorphism from the group lattice to internal R-linear endomorphisms.
  `formula` specifies every vector n as `𝟙 _ + n_i • (biprod.snd ≫ biprod.inl)`,
  namely (x,y) ↦ (x+n_i y,y). At `generator j` this is the displayed T_j.
  The first two conjuncts explicitly state invertibility and pairwise commutation.
- `E.inclusion_hom` and `E.projection_hom` fix the equivariant arrows to `biprod.inl`
  and `biprod.snd`. `sequence R r E` constructs their short complex. The witness `hE`
  asserts it is short exact, with both endpoints the regular trivial-action module.
- `hK` asserts short exactness of its image under the actual K functor. `σ` supplies
  a splitting in each underlying internal-module degree, including degrees outside
  [0,r]. The fourth and fifth conjuncts fix its matrices to diagonal `biprod.inr`
  and `biprod.fst`, zero off the subset diagonal. These are graded maps, without
  any requirement of equivariance or compatibility with the middle differential.
- The third conjunct states zero endpoint differential in every pair of degrees.
  `U : Inclusions R r K` supplies all subset chain inclusions, with the source the
  single complex in degree a. `U.coordinates` fixes coefficient 1 on its own subset
  and 0 elsewhere. The canonical `singleFunctors.shiftIso` identifies its source
  with R[-a]; no arbitrary map or shift identification is chosen.
- The sixth conjunct identifies the **canonical** `DerivedCategory.triangleOfSESδ hK`
  with `ShiftedHom.map` of `CochainComplex.homOfDegreewiseSplit` under Q, including
  Q's canonical shift comparison. It does not merely assert some distinguished triangle.
- The seventh conjunct is `(σ n).s ≫ d ≫ (σ (n+1)).r`, i.e. pi^(n+1) d s^n in
  functional composition. The eighth evaluates its empty-subset input and singleton-j
  output to `if j = i then 𝟙 _ else 0`, the positive coefficient 1_{j=i} 1_R.
- The ninth conjunct shifts `Q(U.map 0 empty) ≫ triangleOfSESδ hK` by -1 and cancels
  the target shifts with `shiftFunctorCompIsoId`. Its result is the localized
  singleton-i inclusion, using the canonical
  `(DerivedCategory.singleFunctors _).shiftIso (-1) 1 0` at the source.
- The final conjunct is `transportCharacterClass R r B a` equal to that localized
  singleton inclusion followed by `c.iso.hom.app` of the regular trivial module.
  This is delta_i = lambda_R Q(u_{i}) as actual derived morphisms, not merely an
  equality of cohomology classes, with the original positive character convention.

Dependency declarations used (full signatures and docstrings read):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and `Mod.regular`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `singleFunctor`, `singleFunctors`. Size convention is metatheoretic, as its DAG
  record states, and is expressed using explicit universes, not a new object.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.Modules`,
  `ActionModule`, and its sectionwise equivariance and trivial inflation.
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`: `Modules`, `Group`,
  `Equivariant`, `generator`, `Subsets`, `KoszulModel`, `Comparison`,
  `derivedInvariants`, `modulesDerived` and `equivariantDerived` in
  `Profinite.DiscreteLattice`. Its full matrix and augmentation specification was read.
- `Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison`:
  `TriangulatedCup.TriangulatedModel`, `ComparisonProperties` and its canonical
  connecting equality, not a mere choice of distinguished triangles.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus` and public dependency
  `CondensedUnipotentClass`: `Character`, `extensionSequence`, `extensionExact`,
  `extensionPositive`, `classShifted`, `characterClass` in
  `CategoryTheory.CondensedDerivedRestriction`. These fix the positive convention.
- `Sheaf.CategoryTheory.LatticeRestrictionCupComparison`: `ring`, `regularAlgebra`,
  `Bridge`, `smallModulesDerived`, `raise`, `raiseFactors`, `cohomologyIso`.
- Proof-only import `WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison`:
  `DerivedCategory.triangleOfSESδ_eq_degreewiseSplit`, together with Mathlib's
  `homOfDegreewiseSplit` and `homOfDegreewiseSplit_f`.

Edge cases checked before writing: at r=0 there is no i, exactly as in the node.
At r=1 the middle differential is (x,y) ↦ (y,0), giving +id. At r=2 both initial
singleton coefficients are positive and the inherited higher-degree signs alternate
as prescribed. For the zero ring every displayed object and map is zero and its
unique endomorphism is invertible. Characteristic two uses the same integral formulas,
without division. The empty profinite test object has its unique sheaf section, so
ha remains consistent for all n. No flatness, completeness or characteristic
restriction is present.

Searches (msearch.py, Q33, this item, 2026-10-24):

- LeanFinder query "A coordinate character of a discrete integer lattice has connecting
  class equal to the singleton Koszul inclusion, computed by projection differential
  splitting": eight hits, cotangent-complex/resolution results, no match.
- Loogle query `"Koszul", "connecting"`: zero hits.
- Mathlib grep `(koszul.*(character|boundary)|(character|boundary).*koszul)`:
  one LocalCohomology.lean characterization hit, not this statement.
- LeanSearch query "A split unipotent extension for a coordinate homomorphism of an
  integer lattice has connecting class the singleton Koszul inclusion": eight ordinary
  group-extension/splitting hits, none states the internal condensed boundary.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for the item id and lattice/character/Koszul names:
  no existing theorem. The search for `coordinateCharacter_exists` found the downstream
  coordinate-character construction, so it is not duplicated. Its specification is
  reused as a parameter, avoiding an import cycle.
- Read `groupCohomology.H1IsoOfIsTrivial` and `H1π_comp_H1IsoOfIsTrivial_hom`:
  ordinary representation H1 identification, not the derived internal Koszul boundary.
  Read the generic split-boundary API, already represented by the proof dependency.

The blueprint source was opened in `literature/blueprint/latest/`. Its paragraph (3)
is the direct-image context; as the inherited source record says, this detailed
lattice calculation is an agent expansion, and the exact internal-module reference
remains WANTED. No mathematical statement correction, new node, dependency repair,
or STATEMENT-DISPUTED flag is introduced. Only the item's `lean` record changes.

Validation: the initial compile found a missing canonical CommShift instance on the
transparent `raise` definition; this was repaired by unfolding the existing exact
identity functor. An implicit-use binder warning was fixed by naming it `_I`.
During the following server queue wait, the assigned sandbox directory disappeared
externally. The entire packet was restored in the same authorized path before
rerunning delivery validation; no live source or launcher tool was edited.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
