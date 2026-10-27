## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceNaiveCotangentCoherent` states
`AlgebraicGeometry.AlgebraicSpace.naiveCotangent_coherent_of_locallyOfFinitePresentation`.
Its only proof is `sorry`. It introduces no new definition and changes no mathematical
statement. The node gains three already-landed statement dependencies to name the
existing chartwise local-finite-presentation, module finite-presentation, and derived
module interfaces; no existing record is repaired.

Hypotheses and conclusions, in order:

- `S : Scheme.{u}` is the arbitrary base scheme. `X Y : AlgebraicSpace S` and
  `f : X ⟶ Y` are exactly the spaces and morphism in the node. There are no assumptions
  on S, no separatedness, flatness, projectivity or properness assumptions on f, and
  no characteristic or field restriction.
- `[HasDerivedCategory.{w} X.SmallModules]` specifies the localization size, with w
  independent of the scheme/section universe u. This is the prescribed size-parametric
  derived category, rather than a finiteness hypothesis.
- `hY : ∃ V : Y.EtaleSite, IsSurjective V.obj.hom ∧
  IsLocallyNoetherian (Y.etaleForget.obj V)` is precisely the required locally
  Noetherian scheme atlas. Membership in EtaleSite already states representable
  etaleness; the separate `IsSurjective` requires the atlas to cover Y. Mathlib's
  scheme `IsLocallyNoetherian` is equivalent to the stated Noetherian affine open
  cover condition.
- `hf : MapIsLocallyOfFinitePresentation f` tests the scheme property on every
  compatible pair of etale charts, exactly as the node requests.
- The first conjunct gives an atlas U of X with the same etale, surjective and
  locally Noetherian conditions: X is locally Noetherian.
- `(SheafOfModules.unit X.smallStructureRings).IsFinitePresentation` states coherence
  of the actual regular-functions structure module.
- The next conjunct states finite presentation of every cohomology sheaf of
  `naiveCotangent f`, using the existing `DerivedCategory.homologyFunctor` in the
  same small module category as the cotangent construction.
- `∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (...)` states zero cohomology outside -1,0.
- The final conjunct quantifies over K equal to either `naiveCotangent f` or
  `X.derivedStructure`. For each, it asserts coherent cohomology in all degrees
  and an integer interval [a,b] outside which cohomology vanishes. This spells out
  membership in the full subcategory D^b_Coh of the specified ambient derived
  category. Both equality alternatives are retained, including when they coincide.

Coherence translation was checked directly against `spaces-cohomology.tex`,
`lemma-coherent-Noetherian` (Stacks 07UB), which equates coherent, quasi-coherent
finite type, and finite presentation on the small etale ringed site. This is also
exactly the convention in the landed AlgebraicSpaceCoherentAbelian module. Over a
Noetherian affine chart, finite presentation is association to a finitely presented
module, equivalently a finitely generated module. The associated etale sheaf has
sections B tensor_R N, as in the node, by the existing tilde functor and the
Zariski/etale quasi-coherent comparison and affine tensor-section formula. Thus the
Lean predicate does not replace the stipulated association by a merely pointwise
finite-generation condition. Passing to the equivalent small affine ringed model
preserves these local finite presentations and the actual structure sheaf. No
second notion of coherent module or bounded derived category is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `etaleForget`, `IsSurjective`, and the structure sheaf.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; its scheme atlas condition
  is used through `Mathlib.AlgebraicGeometry.Noetherian.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocallyOfFinitePresentation`, whose definition explicitly
  uses the preceding scheme property on compatible charts.
- `Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex`:
  `AlgebraicSpace.naiveCotangentComplex`, `naiveCotangent` (image under Q).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `DerivedCategory.homologyFunctor` is its existing cohomology.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`:
  `AlgebraicSpace.DerivedModules`, `derivedStructure`, based on SmallModules.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation` (local cokernels of maps between finite free
  sheaves); its node also records `IsFiniteType` in the Generators module.

All available proof-dependency modules are imported with plain `import` unless
already public statement imports. The two currently unstated proof prerequisites
`lem-sfb-space-naive-cotangent-finite-local-model` and
`lem-sfb-scheme-etale-module-exact-finiteness-comparison` have no recorded Lean module
to import; they remain proof dependencies. Mathlib leaves
`pqf-lem-locnoeth-lft` and `lem-trf-noetherian-submodule-finitely-presented` are covered
by the Noetherian and Module.FinitePresentation imports, respectively. No unavailable
proof declaration is assumed as data or added as a hypothesis.

Sources read: spaces-more-morphisms.tex, lemma-netherlander-quasi-coherent and
lemma-netherlander-fp (0D0Y, 0D0Z); spaces-morphisms.tex,
lemma-locally-finite-type-locally-noetherian (04ZK); quot.tex, the naive-cotangent
paragraph in the tangent-space proof (0D1K); and the coherence equivalences in
spaces-cohomology.tex, lemma-coherent-Noetherian (07UB).

Edge cases checked before drafting: the empty space and zero rings are allowed
(the empty scheme is a locally Noetherian atlas of the empty space); identity
morphisms have zero cotangent cohomology; singular maps can have nonzero H^-1,
which the signature permits; no uniform Noetherian global ring or global finite
presentation is imposed; arbitrary characteristic and disconnected/non-quasi-compact
spaces are allowed. In the boundedness conclusion intervals [-1,0] and [0,0]
suffice for the two objects, respectively; the theorem only asks existence of bounds.

Searches made before writing:

- msearch.py, LeanFinder: "The naive cotangent complex of a locally finitely presented
  morphism of algebraic spaces over a locally Noetherian base has bounded coherent
  cohomology". Eight ring-level cotangent/smoothness and scheme-lfp hits; no matching
  algebraic-space theorem. In particular the finite H1Cotangent hit additionally
  assumes projective differentials and is not a match.
- msearch.py, Loogle: "Algebra.H1Cotangent, IsLocallyNoetherian,
  SheafOfModules.IsCoherent". Zero hits; unknown identifier IsLocallyNoetherian.
- msearch.py, LeanSearch: "Coherent cohomology naive cotangent complex algebraic space
  locally Noetherian". Eight ring-level cotangent/smoothness hits, no space theorem.
- msearch.py, grep: "naiveCotangent|IsCoherent|LocallyNoetherian" in AlgebraicGeometry.
  Twenty-five scheme Noetherian hits, no cotangent-coherence theorem.
- rg in lean/WeilConjectures and lean/Sheaf for naiveCotangent, naive.cotangent,
  coherent/Coherent, and LocallyNoetherian. Found the canonical cotangent and derived
  module constructions and the finite-presentation coherence convention in
  AlgebraicSpaceCoherentAbelian. No existing theorem states this item's conclusions.
- rg of the item id in lean/WeilConjectures found no attached declaration.
- DAG searches for definitions with coherent, locally Noetherian and finite
  presentation titles found the already-landed morphism-properties, derived-module
  and module-finite-type/presentation nodes. Their declarations are reused directly.

No STATEMENT-DISPUTED flag, missing mathematical object, or statement correction.
The statement compiled through scompile.py in both sandbox and library modes with
no errors or warnings. Final compilation and delivery preflight are recorded below.

## Second reading by Q04

Author's self-check; independent review is the maintainer's, as required by this
worker's direct-delivery brief. Reopened the node and final module together. The
existential atlas hypothesis and source conclusion include surjectivity, while
etaleness is carried by the site objects. The source condition has no accidentally
added finiteness or separation hypothesis. All cohomology degrees are integers;
vanishing excludes exactly -1 and 0. The final disjunction names both specific
objects, and the interval condition is global boundedness, not merely chartwise
boundedness. Rechecked 07UB(1)-(3): finite presentation is exactly coherence here,
including the structure sheaf. The module keeps the prescribed actual structural
ring and arbitrary derived localization universe. No mismatch or mathematical
statement change was found. One missing explicit Mathlib proof import for the
Noetherian submodule finite-presentation leaf was added before final verification.

Final verification: scompile.py compiled the final file separately in sandbox and
library modes (4.3 s and 4.1 s), with no compiler diagnostics. The prescribed
`deliver2.py Q04 lem-sfb-space-naive-cotangent-coherent --no-push` printed
`OK (dry run)` for commit 260a39a7dd3: server preflight and compilation passed.
