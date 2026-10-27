## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeEtaleHigherImageComparison` states Stacks
071N for the small etale topology. All mathematical theorem proofs are `sorry`.
The constructions of the two canonical comparison maps contain real data: they
use Mathlib's mates equivalence and the existing derived-base-change construction.
No definition node, dependency repair, or statement correction is needed.

Clause-by-clause reading of the node against the main declaration:

- Schemes X and Y and their morphism f: `(X Y : Scheme.{u}) (f : X ⟶ Y)`.
- Quasi-compact and quasi-separated f: `[QuasiCompact f] [QuasiSeparated f]`.
  There is no separatedness, noetherian, or quasi-compactness assumption on Y.
- A module M on the small etale structure sheaf: `M : SmallEtaleModules X`.
  This is the dependency's actual `SheafOfModules.{u} (smallEtaleModuleRing X)`.
- Site quasi-coherence: `[M.IsQuasicoherent]`, Mathlib's local-presentation predicate.
- M_Zar obtained by restriction to opens:
  `(c X).toZariskiEtaleModuleContext.restriction.obj M`.
  The first conjunct asserts its quasi-coherence. The context extends the exact
  recorded `ZariskiEtaleModuleContext`; it does not choose new module functors.
- Every integer q >= 0: `∀ q : ℕ`, including zero.
- Zariski higher image: `((pushforward f).rightDerived q).obj M_Zar`.
  This resolves in ALL Zariski modules. The recorded ringed-space direct image
  specializes to this same sectionwise pushforward and its derived cohomology;
  the upstream `higherDirectImage f q` is defined as this very rightDerived.
- Its quasi-coherence: the first conjunct under `∀ q`.
- Associated small etale module: the canonical context's `extension.obj` applied
  to that Zariski higher image, which is the source of higherComparison q.
- Etale higher image: `(smallEtaleModulePushforward f).rightDerived q`, resolving
  in ALL small etale modules with injectives supplied by the context. The scheme
  pushforward is the specialization of the recorded chart-limit definition:
  for an etale U -> Y the base change X times_Y U is a terminal chart, so its
  sections are evaluation at that chart. We import the chart-limit module too.
- Canonical isomorphism and naturality in M:
  `IsIso ((s.higherComparison q).app M)`. The source is the associated Zariski
  higher image and the target is the etale higher image; invert this specified
  map for the direction displayed in the node. `higherComparison q` is a natural
  transformation on all modules, so naturality on quasi-coherent modules is
  built into its type, rather than a separately chosen family of isomorphisms.
  It is the derived mate of `s.comparison.inv` followed by the canonical
  extension/restriction counit. `s.onOpens` specifies the ordinary square on
  every module and every Zariski open using gabberPreimageEtaleIso; no arbitrary
  automorphism of an isomorphism can alter the comparison.

Following the 2026-10-21 convention, the file first gives
`scheme_etale_derived_image_comparison`: the concrete derived comparison is
invertible on the restricted module placed in degree zero. The main per-degree
statement is a separate corollary, with its own source and proof docstring. The
proof of the derived theorem carries all five DAG steps, the resolution and
slice calculation, affine vanishing/Leray/flat-base-change identification, and
restriction compatibility/gluing. Its final step explains identification with
the derived mate and conservativity of homology. The corollary takes homology.

The helper `EtaleHigherImageContext` contains only proof obligations: continuity
and right adjoint existence inherited from the recorded context, enough
injectives, and exactness/additivity of the canonical flat tensor extension.
These are existentially supplied by the theorem, never additional hypotheses
on X, Y, f, or M. The `EtaleHigherImageSquare` contains the already canonical
restriction isomorphism together with its complete open-section normalization.
Both belong to this node's comparison construction, as permitted for canonical
map helpers in brief-stage2 section 1. No new coefficient universe is introduced;
the site still has objects in u+1, morphisms in u, and sections/modules in u.
Standard derived categories are used inside the definitions and disappear from
the per-degree type. Definitions install proof instances using letI internally;
there is no let binder in a theorem statement or file-local notation/instance.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Morphism conventions: Mathlib `QuasiCompact`, `QuasiSeparated` (the convention
  node explicitly directs citers to these original predicates).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the node records
  `AlgebraicSpace.QCoh`; its retained general Mathlib match
  `SheafOfModules.IsQuasicoherent` applies here directly to scheme etale modules.
  The full signatures and local-presentation docstrings were read.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `SmallEtaleModules`, `ZariskiEtaleModuleContext`, its `restriction`, `extension`,
  `adjunction`, `smallEtaleModulePushforward`, and the normalized equivalence
  `scheme_zariski_etale_quasiCoherent_equivalence` used by the proof plan.
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`:
  `RingedSpace.moduleDirectImage` and `derivedModuleDirectImage`, whose
  full definitions and resolution-computation statements were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, chart-limit projections and
  their naturality; specialization to schemes is the already recorded
  `smallEtaleModulePushforward`, not another pushforward definition.
- `Sheaf.AlgebraicGeometry.QcohCohomologyEtalePullbackNaturality`:
  existing additivity instance `qcohEtalePushforward_additive` and canonical
  cohomology/pullback proof input. No second additivity obligation is stated.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`:
  `Functor.rightDerivedBaseChange` and `rightDerivedFunctorPlusBaseChange`;
  their full signatures, unit normalization and homology construction were read.

Every proof-dependency module with a recorded module is imported, privately
unless it also supplies a public construction. Proof dependencies without a
recorded module (module-sheafification interface, qcqs permanence, affine-opens
basis, flat base-change stability) have no guessed imports. Their cited DAG
proof steps remain in the docstring.

Edge cases checked against the source and definitions:

- q=0 gives the canonical underived mate composed with the counit, hence the
  ordinary sectionwise comparison; q>0 uses injective resolutions as required.
- Empty schemes and the zero module are permitted; sections and positive
  derived cohomology are zero, and the comparison is the unique zero-object iso.
- Identity morphisms give the normalized extension/restriction counit.
- No separatedness of f is introduced, and no assumption that intersections of
  affine opens are affine occurs in the proof; overlaps are refined by affines.
- Non-quasi-compact Y is covered by the local argument exactly as in 071N.
- The original small module universe is retained, without equating the site
  object universe u+1 with its hom/section universe u.

Searches (all via msearch.py with Q40 and this item, plus repository rg):

- LeanSearch: `higher direct image quasi coherent small etale Zariski comparison`.
  Eight topology/site hits (smallEtaleTopology, smallEtalePretopology,
  zariskiTopology_le_etaleTopology, AffineZariskiSite.sheafEquiv, etc.); no 071N.
- LeanFinder: `quasi coherent modules higher direct images comparison small etale
  Zariski schemes`. Eight hits: pushforwardCongr, Scheme.Modules.pushforwardComp,
  pushforwardNatIso, isQuasicoherent, pushforwardComp and its component lemmas;
  none is the higher-image comparison.
- Loogle: `CategoryTheory.Functor.rightDerived, SheafOfModules.pushforward`.
  Zero hits for this combined search.
- Mathlib grep through msearch: `higher.*[Ee]tale|[Ee]tale.*[Hh]igher|rightDerived`
  in AlgebraicGeometry: zero hits.
- `rg` of rightDerived/higher-etale combinations in project AlgebraicGeometry:
  found general derived functors and constant-coefficient etale higher images,
  not the structure-sheaf comparison. Read and reused the recorded scheme
  equivalence and QcohCohomologyEtalePullbackNaturality instead of duplicating
  their ring sheaves, module categories, functors or additivity instances.
- Exact item-id grep of `lean/WeilConjectures`: no hits. Exact searches for
  `EtaleHigherImageContext`, `EtaleHigherImageSquare`, and both new theorem names
  in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json: no hits.

Sources read locally: descent.tex, proposition-equivalence-quasi-coherent(2),
lemma-higher-direct-images-small-etale, and lemma-compare-etale-zariski-flat.
There is no mathematical dispute or statement fault to record.

Validation: scompile.py compiled the module in sandbox and library module modes
with no errors or warnings. No local lake/global build was run.

## Second reading by Q40

I re-opened the node and the completed module for a separate checking pass.
This is the dispatcher's sole worker, not a claim of an independent second agent;
the maintainer's independent review remains the review of this delivery.
The hypotheses are precisely schemes, qcqs f, a site quasi-coherent M, and q >= 0.
The two original module categories and canonical extension/restriction functors
are used. The source and target of higherComparison elaborate to exactly the
two higher images in the node, in reverse direction, so IsIso yields its stated
isomorphism. Naturality is the NatTrans type and quasi-coherence is explicit.
No arbitrary comparison is hidden in a bare Nonempty statement: the open-square
normalization and mate/base-change recipe determine it. During this rereading
I separated the derived theorem from the per-degree corollary so both have their
own declaration and docstring, as the current convention requires. No hypothesis
or clause of the node was changed. Helpers were checked for genuine construction
data and all variables/universes are explicitly bound.
