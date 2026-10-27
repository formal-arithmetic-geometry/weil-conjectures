## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFppfQCohDescent` states
`AlgebraicGeometry.AlgebraicSpace.space_fppf_qcoh_descent` with `sorry`.
It uses the node's explicitly equivalent formulation: every specified datum is
effective, and compatible morphisms between restrictions descend uniquely. It
also constructs two canonical comparison helpers with real data. No auxiliary
theorems or new mathematical notions are postulated. The node statement,
proof and proof dependencies are unchanged. Its statement dependencies gain
only the two already landed definition owners used in its signature:
`def-sfb-space-module-tensor-composition` and
`def-sfb-space-sheaf-fibre-product`.

Hypothesis and clause correspondence:

* The base scheme is `{S : Scheme.{u}}`. `{X : AlgebraicSpace S}` and
  `{Xᵢ : I → AlgebraicSpace S}` are the dependency's existing fppf-sheaf
  algebraic spaces over that same base. `universe u w` and `{I : Type w}`
  express the size convention with arbitrary set-indexed covers. Module
  sections remain in universe `u`, as in the recorded module categories;
  there is no added equality of site object and morphism universes.
* `q : ∀ i : I, Xᵢ i ⟶ X` and `hq : IsFppfCover q` give exactly chartwise
  flatness, local finite presentation and joint extension-lifting surjectivity
  on field-valued point classes, using the covering-calculus definition.
* The first conjunct quantifies over `Mᵢ : ∀ i, (Xᵢ i).QCoh`, the existing
  full subcategories for Mathlib's local-presentation quasi-coherence.
  Its `φ i j` are isomorphisms from first-projection tensor pullback of
  `Mᵢ i` to second-projection tensor pullback of `Mᵢ j` on the actual
  `enlargedFibreProduct (q i) (q j)`. The first projection is the recorded
  `enlargedFibreProductFst`; the second is the underlying sheaf's actual
  `pullback.snd`, bundled by `ObjectProperty.homMk`, without a replacement
  fibre-product construction.
* The cocycle premise is precisely `φ_ik = φ_ij ≪≫ φ_jk` after canonical
  pullback identifications. It quantifies over all spaces `T`, their three
  legs `a,b,c`, and maps `rᵢⱼ,rⱼₖ,rᵢₖ` into the overlaps with all six leg
  equations. This is equality after arbitrary maps into the triple product,
  and includes the triple product itself; conversely its universal property
  factors every such compatible triple. No etaleness condition on `T` or
  its legs is imposed. `qcohDescentTransitionOn` transports a pulled-back
  isomorphism using the exact recorded `moduleTensorComposition` and the
  supplied leg equalities.
* Effectivity is `∃ (M : X.QCoh) (α : ∀ i, q_i^* M.obj ≅ (Mᵢ i).obj), ...`.
  The equation following it says that canonical transition followed by
  second-projection pullback of `α j` equals first-projection pullback of
  `α i` followed by `φ i j`. Thus it recovers the given transitions on the
  original unrefined family, rather than just the component objects.
  `qcohCanonicalDescentTransition` is composition comparison, transport
  along the actual pullback square, and inverse composition comparison.
  It cannot be replaced by an arbitrary natural isomorphism.
* The second conjunct takes `M N : X.QCoh` and every family `a i` of linear
  module-sheaf maps between their `q i` pullbacks. Its premise is exactly
  `φ^N ∘ pr_i^* a_i = pr_j^* a_j ∘ φ^M`, with Lean's left-to-right `≫`
  composition. The conclusion `∃! f : M.obj ⟶ N.obj, ∀ i, ...map f = a i`
  gives both fullness and faithfulness of the canonical restriction functor.
  Since `QCoh` is full, this is exactly its morphism type. Together with the
  first conjunct this states essential surjectivity and full faithfulness.
  Given arbitrary effective data, conjugating by the effectivity isomorphisms
  gives the same unique descent assertion for maps between those data.
* No additional hypotheses occur: there is no quasi-compactness,
  separatedness, Noetherianity, finite presentation of modules, finite
  generation, or nonempty index assumption.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom` (local affineness and locally ringed-space maps).
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.structureSheaf`, `AlgebraicSpace.Modules`. The latter is
  the existing `ringedSiteModules.{u}` on the regular-functions small etale site.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`, with its sectionwise linear maps.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh`, the full subcategory for
  `SheafOfModules.isQuasicoherent`; both named slice sheafification instances
  are supplied by the existing module. The Mathlib definition's full
  signature and local-presentation docstring were read.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus`:
  `AlgebraicSpace.IsFppfCover`. The covering permanence and empty-family
  signatures and docstrings in that module were also read.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `AlgebraicSpace.moduleTensorPullback`, the specified left adjoint of the
  chart-limit direct image; its `moduleTensorAdjunction` and tensor-section
  normalization were read. No replacement adjoint is selected.
* `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`:
  `AlgebraicSpace.moduleTensorComposition`, with its unique local-tensor
  characterization `moduleTensorComposition_existsUnique`. Only this
  construction is used, not the flat-base-change theorem.
* `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicSpace.enlargedFibreProduct`, `enlargedFibreProductFst`, the existing
  definitions owned by `def-sfb-space-sheaf-fibre-product`.

The statement dependencies are public imports, either directly or through
these dependency modules. Already stated proof dependencies are plain imports:
module-pullback quasi-coherence, representable etale scheme tests, scheme
Zariski/etale comparison and `WeilConjectures.AlgebraicGeometry.Descent`.
The scheme fppf-to-fpqc comparison is Mathlib's
`Scheme.fppfPrecoverage_le_fpqcPrecoverage`, already accessible through
covering calculus. The cartesian-chart-family proof dependency has no Lean
record in the read clone; it introduces no object needed to type this
statement, so there is no private substitute or missing signature dependency.
Its mathematical use remains in the theorem's complete proof docstring.

Source reading: local `literature/stacks-project/spaces-descent.tex`,
proposition-fpqc-descent-quasi-coherent (Tag 04W8), including all seven
proof steps; `spaces-topologies.tex`,
lemma-zariski-etale-smooth-syntomic-fppf-fpqc (Tag 0DFQ), including the affine
refinement proof. Also read the current blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), at
`literature/blueprint/latest/`. This item is an ordinary-module prerequisite
in the inherited alteration/moduli chain, rather than that unit's statement.
No source or statement defect was found; no statement correction is made.

Edge cases checked before construction and again on the final signature:

* Empty `I` is allowed: the cocycle and map families are vacuous. The covering
  predicate forces the target to be empty, so existence of its zero module
  and uniqueness of its map give precisely the two conclusions.
* An empty member contributes only its zero module and unique map. Neither
  the first nor the second conjunct demands nonzero sections or a point.
* The singleton identity cover has a self-overlap. Invertibility and the
  triple equation imply its diagonal transition is identity; adding a
  separate identity hypothesis would be redundant and is avoided.
* Repeated indices are included in the triple quantifier, so the cocycle
  also enforces inverse and diagonal conditions. No indices are assumed distinct.
* Zero modules and arbitrary infinite covers and arbitrary presentations are
  included. The separate index universe does not restrict the ring/scheme
  test universe or impose an accidental lower-universe test quantifier.

Searches (2026-10-24 UTC; results reported by the prescribed msearch wrapper):

* LeanFinder, query "Effective fppf descent for quasi coherent modules on
  algebraic spaces, fully faithful essentially surjective canonical functor":
  eight hits, all local quasi-coherent presentation data or scheme module
  colimit instances; no algebraic-space descent theorem.
* Loogle, query `CategoryTheory.Pseudofunctor.DescentData,
  CategoryTheory.Pseudofunctor.isEquivalence_toDescentData`: one hit,
  `CategoryTheory.Pseudofunctor.isEquivalence_toDescentData`, which assumes
  the relevant pseudofunctor is already a stack. It does not supply this
  geometric descent theorem or the required algebraic-space tensor pseudofunctor.
* LeanSearch, query "Effective faithfully flat descent of quasi coherent
  module sheaves on algebraic spaces": eight hits, quasi-coherence definitions,
  local presentation constructors and faithfully flat module facts; no match.
* msearch grep, query `structure DescentData|def toDescentData|structure.*Descent`
  in Mathlib `CategoryTheory`: 11 hits in generic pseudofunctor descent APIs.
  Read `DescentData.lean`: the definitions require an existing coherent
  pseudofunctor. They do not state this specialization. The equivalent
  object/map statement avoids inventing or assuming one.
* `rg` in `lean/WeilConjectures` for the item id: no hits. Searches for
  fppf/QCoh and descent/quasi-coherence combinations give scheme descent,
  module sections, and derived QCoh results, not this theorem.
* `rg` in `lean/Sheaf` for fppf/descent and QCoh/descent combinations:
  invertible atlas descent is etale-only with scheme source modules;
  scheme big-fppf equivalence concerns schemes; higher vanishing concerns
  cohomology. None is effective descent of ordinary QCoh modules for the
  arbitrary algebraic-space fppf family in the item. Searches of transition
  helpers found ordinary-scheme `atlasTransitionOn` only, whose types do not
  accept the recorded algebraic-space modules; the new helper just applies
  the existing algebraic-space composition iso and equality transports.

Validation: `scompile.py Q40 lem-sfb-space-fppf-qcoh-descent
<...>/SpaceFppfQCohDescent.lean` compiled the sandbox probe and actual module
cleanly (3.5 s and 2.7 s). Only the main theorem has a postponed proof; the
comparison helpers contain actual compositions of existing isomorphisms.

## Second reading by Q40

I reopened the node and the completed module for a separate second pass; no
other agent was started, as instructed. I checked the direction of every
comparison: `qcohDescentTransitionOn` starts with the inverse transport of
`ha`, undoes the comparison for `r,p`, pulls back `φ`, then uses comparison
for `r,q` and transport `hb`. The canonical transition starts at `pr_i^*q_i^*M`
and ends at `pr_j^*q_j^*M` via the pullback square. Thus both the effectivity
square and the map-compatibility square have exactly the directions in the
node. The triple equation is equality of isomorphisms, with composition
`φ_ij ≪≫ φ_jk`, which is the node's `φ_jk ∘ φ_ij`. All three pairs allow
repeated indices and all six leg equations are present.

I checked each hypothesis and clause against the correspondence above:
same base and cover, recorded QCoh and tensor pullback, actual sheaf overlaps,
full cocycle, given-data effectivity, and unique descent of compatible maps.
No mathematical mismatch was found. The statement uses the node's explicitly
permitted equivalent formulation rather than building a new descent category.
I added the two already landed definition-owner ids to `stmt_deps` so the
record tracks the comparison and sheaf-product constructions it uses.
The source statement itself did not change.
