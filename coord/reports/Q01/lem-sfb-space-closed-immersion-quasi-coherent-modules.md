## Worker report

Item: lem-sfb-space-closed-immersion-quasi-coherent-modules, group Q01, stage 2.

The new module is
`Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedImmersionQuasiCoherentModules`.
It states `AlgebraicGeometry.AlgebraicSpace.closedImmersion_quasiCoherent_modules`
with a single `sorry`, and defines the helper
`AlgebraicGeometry.AlgebraicSpace.quasiCoherentDirectImage` with real functor data.
The helper is Mathlib's `ObjectProperty.lift` of the existing `moduleDirectImage`,
precomposed with the inclusion of the existing `QCoh Z`. Its object and morphism
maps are exactly the specified direct image. Its preservation proof is a parameter;
the main theorem supplies that proof in its conclusion. There is no arbitrary
functor, comparison, scalar structure, or choice of an unknown object.

The source was read in `literature/stacks-project/spaces-morphisms.tex`,
`lemma-closed-immersion-ideals` (03MB), first sentence, and
`lemma-i-star-equivalence` (04CJ), part (3) and its proof.
The node statement, all six proof steps, and the stated dependencies were read.
No statement correction and no disputed mathematical statement are needed.
The node changes only in `lean` and `stmt_deps`, which gains the two already-landed
owners `def-sfb-space-module-structure-map` and
`def-sfb-space-quasi-coherent-ideal`. No new nodes or dependency repairs are needed.

Clause-by-clause correspondence:

- Base scheme: `{S : Scheme.{u}}` uses the recorded Mathlib scheme.
- Algebraic spaces over that scheme: `{Z X : AlgebraicSpace S}` uses the existing
  full subcategory of fppf sheaves with representable diagonal and an etale atlas.
- Morphism: `(i : Z ⟶ X)` is a natural transformation in that category.
- Closed immersion on every scheme base change:
  `hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`.
  Unfolding the existing predicate tests every scheme map into X and supplies a
  scheme pullback with a closed-immersion projection. This is not a topological
  closedness condition and does not impose an additional finiteness assumption.
- The size convention is the explicitly bound `universe u` and the recorded
  dependency interfaces: scheme and ring sections in u, etale chart objects in
  u+1, module sections in u. There are no automatic implicit variables.
- Small etale structure sheaves and modules are `X.structureSheaf`, `Z.structureSheaf`,
  `X.Modules` and `Z.Modules`; their definitions and signatures were opened.
- Direct image and its scalar action are the existing `moduleDirectImage i`, whose
  compatible-chart-section limit uses the regular-function pullbacks as scalar maps.
  The helper merely attaches quasi-coherence proofs to these same objects and maps.
- Preservation of quasi-coherence, making the restricted functor well-defined:
  the conclusion supplies `hqc : ∀ M : Z.Modules, M.IsQuasicoherent →
  ((moduleDirectImage i).obj M).IsQuasicoherent`.
- The structure direct image is quasi-coherent: the first conjunct is
  `((moduleDirectImage i).obj (SheafOfModules.unit Z.structureSheaf)).IsQuasicoherent`.
- The canonical structure map is sheaf-surjective: `Epi (moduleStructureMap i)`.
  The existing map is uniquely characterized by regular-function pullback after
  every chart projection. Epimorphy of this module-sheaf map is local surjectivity;
  it does not assert surjectivity on the rings of every nonaffine chart.
- The quasi-coherent ideal: `(I : QuasiCoherentIdeal X)` means a subobject of
  `SheafOfModules.unit X.structureSheaf` whose module is quasi-coherent. The equation
  `I.val = kernelSubobject (moduleStructureMap i)` identifies it with the actual
  kernel subobject, including its inclusion up to the unique subobject isomorphism.
  A submodule of the commutative structure ring is an ideal, not arbitrary data.
- Exactness of the canonical QCoh functor: the two conjuncts are
  `PreservesFiniteLimits (quasiCoherentDirectImage i hqc)` and
  `PreservesFiniteColimits (quasiCoherentDirectImage i hqc)`. For the abelian QCoh
  categories these together are precisely exactness (including the zero object,
  kernels and cokernels). No chosen Abelian instance or stronger preservation of
  arbitrary colimits is imposed.
- Full faithfulness: `.Full` and `.Faithful` for that same canonical functor.
- Essential image: for every `F : QCoh X`,
  `(∃ G : QCoh Z, Nonempty (F ≅ (quasiCoherentDirectImage i hqc).obj G)) ↔ ...`.
  This is the categorical essential image, not equality of representatives.
- Annihilation is fully explicit on every small etale object `V`, every ideal
  section `a : (I.val : X.Modules).val.obj (op V)` and every module section
  `m : F.obj.val.obj (op V)`: `(I.val.arrow.val.app (op V) a) • m = 0`.
  Thus it covers every local section, not only global sections or geometric points.
- No nilpotence, finite-type, finite-presentation, Noetherian or separation binder
  appears. Quasi-compactness and separatedness of the given closed immersion are
  consequences used in the proof plan, not additional hypotheses.

Dependency declarations used (the source signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `EtaleSite`, `structureSheaf`, `Modules`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, used on each scheme projection.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the recorded Mathlib `SheafOfModules` and module morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  etale slice sheafification interfaces; the predicate remains Mathlib's
  `SheafOfModules.IsQuasicoherent`, with arbitrary local coproduct presentations.
- `Sheaf.CategoryTheory.SiteCoveringAxioms` supplies the recorded general site
  interface `CategoryTheory.Precoverage.IsSiteForCoverings`. The existing etale
  topology and sheaf categories specialize this background; no new site is defined.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImageModel`, `moduleDirectImage`,
  `moduleTensorPullback`, `moduleTensorAdjunction` and `moduleTensorSection`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`:
  `existsUnique_moduleStructureMap`, `moduleStructureMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`: `QuasiCoherentIdeal`.
- Mathlib's `ObjectProperty.lift` and `kernelSubobject` supply the standard
  restricted functor and kernel subobject, with no duplicate definition.

All stated proof dependencies are imported with ordinary imports when used only
for the postponed proof: `SpaceQCSeparatedEtaleLocal`,
`AlgebraicSpaceQuasiCoherentPushforward`,
`AlgebraicSpaceEtaleModulePushforwardRestriction`,
`AlgebraicSpaceClosedPushforwardStalks`, `SpaceStalkIdealPullback`, and
`AlgebraicSpaceModulePullbackQuasiCoherent`. The node's
`lem-sfb-space-qcoh-kernels-colimits` and
`lem-sfb-space-geometric-stalk-tensor-calculus` have no Lean record in the read
repository, so have no module to import yet; they are only proof dependencies,
not missing objects needed to state this theorem. The six-step docstring retains
both of them in the proof plan, including the identity-thickening specialization,
the ordinary-complex stalk formula, the unit and counit inverses, and detection
of exactness by stalks.

Edge cases checked before the final statement:

- Identity immersion: I=0, the direct image is naturally the identity, and every
  quasi-coherent module is annihilated by the zero ideal.
- Empty closed subspace: I=O_X, the essential image consists of zero modules,
  since its unit section kills every local section. Exactness and full faithfulness
  still hold for the zero source category.
- Empty ambient space: both module categories are zero categories; all clauses
  remain meaningful, with no nonempty chart or point assumption.
- Nonreduced and nonnilpotent ideals are allowed, for example an affine quotient
  by a general ideal J and k[t]→k. No flatness of the quotient is asserted.
- Non-finitely-generated ideals and arbitrary module presentations are allowed.
- Nonaffine chart sections need only lift locally. The initial exploratory
  section-surjectivity draft was removed; the final theorem uses sheaf epimorphy.
- The zero module is included in the essential-image equivalence and the helper
  does not need a nonzero object or a chosen generator.

Searches for an existing statement and helper:

- `msearch.py ... leanfinder`, query
  `Closed immersion of algebraic spaces exact fully faithful pushforward quasi coherent modules annihilated by the defining ideal`:
  8 hits, led by `AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData`,
  `instIsClosedImmersionInclusion`, `Scheme.Modules.instFaithfulPushforward`,
  and `IsClosedImmersion.spec_of_quotient_mk`. These concern schemes, and the
  module pushforward full/faithful hits assume an open immersion. No match.
- `msearch.py ... loogle`, query `"AlgebraicSpace", "Quasicoherent"`:
  0 hits.
- `msearch.py ... grep`, query
  `AlgebraicSpace|[Cc]losed[Ii]mmersion.*[Qq]uasi[Cc]oherent|annihilat.*pushforward`
  in `AlgebraicGeometry`: 0 hits.
- `msearch.py ... leansearch`, query
  `Closed immersion algebraic spaces exact fully faithful quasi coherent direct image defining ideal`:
  8 hits, on scheme closed immersions, including `IsClosedImmersion`, its
  constructor and `isClosedImmersion_iff_isAffineHom`. No small-etale
  algebraic-space exact/fully-faithful/annihilator theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item ID and
  closed-immersion/quasi-coherence patterns found downstream docstring references
  and scheme results, not this statement. The existing structure-map and ideal
  modules were found, opened, and reused.
- `rg` for `quasiCoherentDirectImage|closedImmersion_quasiCoherent_modules` in
  `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and `dag/lean_names_upstream.json`:
  no existing declaration with either name. Searches for definitions combining
  quasi-coherence/QCoh with direct image/pushforward found no ordinary
  algebraic-space QCoh restriction functor; derived or scheme-only operations do
  not provide this one. The helper simply specializes the already existing
  `ObjectProperty.lift`; it introduces no independent mathematical notion.

Validation: `scompile.py Q01 lem-sfb-space-closed-immersion-quasi-coherent-modules`
compiled the final module in both sandbox and library module names, cleanly and
within 60 seconds, with no errors or warnings. Only the prescribed wrappers were
used for compilation. No live source was edited and no direct Git command run.
The prescribed deliver2.py --no-push dry run passed preflight and compilation
(OK, provisional commit cb68ceceae7); the final push repeats these checks.

## Second reading by Q01

Independent second reading by the maintainer's review service (reviewer NT-cc), replacing the
worker's self-review. The node, its source place (Stacks 03MB first sentence, 04CJ(3)), every
statement dependency record and declaration, and the module were read.

Node statement as a list, with the Lean and the verdict:

1. Base scheme S [def-pc-scheme]: `{S : Scheme.{u}}`. Correct.
2. Algebraic spaces Z, X over S [def-trf-algebraic-space]: `{Z X : AlgebraicSpace S}`. Correct.
3. Size convention [def-weil-size-convention]: one bound universe u, as the landed space,
   module and QCoh interfaces use it. No extra universe equality. Correct.
4. i a closed immersion, i.e. representable by closed immersions of schemes after every base
   change to a scheme [def-weil-closed-immersion]:
   `hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`. Unfolded:
   every T : Over S and every T → X has a pullback square with a scheme U → T that is a
   Mathlib closed immersion. This is the encoding the landed space modules already use
   (AlgebraicSpaceClosedSubspace, SpaceCoherentAdicSystem, AlgebraicSpaceCoherentSupportIdealPower,
   SpaceUniversalConormal). There is no finiteness, Noetherian or nilpotence assumption. Correct.
5. Small étale module sheaves and quasi-coherence [def-weil-sheaf-of-modules-category,
   def-trf-space-quasi-coherent-module]: `Z.Modules`, `X.Modules`, `IsQuasicoherent`, `QCoh`.
   Correct.
6. i_* with scalar action through i^♯ [def-trf-space-etale-module-functors]:
   `moduleDirectImage i` (chart limit, scalars via moduleChartScalar). The helper
   `quasiCoherentDirectImage` is `ObjectProperty.lift` of `ι ⋙ moduleDirectImage i`. It has
   real data, and since `hqc` is a proposition the functor does not depend on any choice.
   No existing QCoh direct-image functor exists in lean/Sheaf or Mathlib (grep for
   `QCoh _ ⥤ QCoh`, `quasiCoherentDirectImage`, `qcohDirectImage`), so H4 is clear.
7. i_*O_Z is quasi-coherent: first conjunct. Correct.
8. i^♯ is surjective: `Epi (moduleStructureMap i)`, where moduleStructureMap is the landed
   ∃!-pinned owner of def-sfb-space-module-structure-map. Epi in the sheaf category means
   local surjectivity, which is what 03MB states. Correct.
9. Its kernel I is a quasi-coherent ideal: `∃ I : QuasiCoherentIdeal X` (landed owner of
   def-sfb-space-quasi-coherent-ideal: a subobject of O_X with quasi-coherent module), pinned
   by `I.val = kernelSubobject (moduleStructureMap i)`. Correct and not arbitrary.
10. i_* on QCoh is exact: `PreservesFiniteLimits` and `PreservesFiniteColimits` of the
    restricted functor. Both are true (QCoh is closed under finite limits and colimits in
    Modules, 03M1; i_* is a right adjoint and is exact for closed immersions). Correct.
11. Fully faithful: `.Full ∧ .Faithful`. Correct.
12. The essential image is exactly the F with I F = 0, where this means that every local
    section of I times every local section of F is zero: for every F : QCoh X,
    `(∃ G, Nonempty (F ≅ i_* G)) ↔ ∀ V a m, (I.val.arrow.val.app (op V) a) • m = 0`. The
    quantifier runs over all étale objects V and all sections, as the node says. Correct.

Records: the item node differs from live only in `lean` and in two added stmt_deps,
def-sfb-space-module-structure-map and def-sfb-space-quasi-coherent-ideal. Both are landed
def nodes whose own deps do not reach this item, so there is no cycle. They are needed
because
the statement uses their declarations. `lean.statement` is verbatim the signature in the file.
The imports all exist in live, including the private proof-dependency imports.

Edge cases: i = id (I = 0, every module is killed); Z = ∅ (I = O_X, the image is zero
modules); X = ∅; non-finitely-generated and non-nilpotent ideals. All are covered, with no
nonemptiness hypothesis.

Docstrings carry the source place, `(blueprint: …)` and the six-step proof. The only proof is
`sorry`, and the helper is a term. There is no pro-étale substitute and no hollow definition.

Finding: the delivered "Second reading" was a self-review by the worker (H11). This section
replaces it. No mismatch in the Lean or the records was found.
