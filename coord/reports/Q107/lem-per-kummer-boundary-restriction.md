## Worker report

Q107 states lem-per-kummer-boundary-restriction in
`Sheaf.AlgebraicGeometry.KummerBoundaryRestriction`, with four named theorems, each
having exactly `by sorry` as its proof. Every proof docstring carries the matching
DAG id and the relevant steps of the node's eight-step proof. Nothing is proved.
All three delivered files compiled cleanly and individually through scompile.py
after the repair. The repaired packet also passed deliver2.py --no-push
(preflight and per-file compile, commit b5b0e7f3ade); the staged paths contain no
change to either restored dependency record.

Source read: ILO, Travaux de Gabber, PDF in literature/, VI 2.1--2.3 and 3.1--3.3
(printed pp.71--74), VIII 5.3.8--5.3.10 (printed pp.125--126). VI 2.1 defines
Kummer and finite Kummer etale covers; VI 2.2 gives the canonical fs G-diagonal;
VI 2.3 gives the character action, invariant sheaves, and stratum computation.
VIII 5.3.8 expressly replaces the enlarged boundary by the smaller boundary using
IX 2.1. The latest blueprint ancestor and its proof were read at
literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/.
No correction of the item statement is made and no statement is disputed.

The hypothesis and clause correspondence is as follows.

* Noetherian regular Y: `[IsNoetherian Y.scheme]` and `hY : IsRegularScheme Y.scheme`.
  The recorded regular scheme predicate includes local Noetherianity and stalkwise
  regularity. Normal V: `hVnormal` requires each stalk to be a domain and integrally
  closed. This is normality allowing disconnected schemes. The upstream
  `IsNormalScheme` additionally requires integrality and is consequently unsuitable
  here; no duplicate normal-scheme predicate was introduced. Both endpoints are
  locally Noetherian, which adds no restriction: V is finite over Noetherian Y.
* The normal crossings boundary is `hB : B.IsNormalCrossingsDivisor`, using the
  existing ordinary normal crossings definition, allowing global self-intersections.
  `hD : D.IsReducedComponentUnion B` says D is radical and its support is the union
  of a selection of the irreducible components of the B subscheme. In particular
  D is contained in B. No assumption that each global component is regular is made.
* The finite group is `{G : Type v} [Group G] [Finite G]`, with independent group
  universe. The original quotient map and log action are `q` and `a`.
  `hcover` includes finiteness, surjectivity, Kummer etale charts, the action laws,
  invariance of q, and the canonical fs G-diagonal. `horbits` is exactly the orbit
  assertion on geometric fibres. `hinvariants` identifies the image of every map
  on sections with the invariant sections and requires injectivity. Its equations
  use the actual action pullbacks and restrictions on a common subopen.
* `htame` and `hfree` use the existing `a.IsTame` and `a.IsGenericallyFree`.
  They test geometric inertia and a dense invariant open, respectively; they do
  not require invertibility of the order of G.
* The given larger divisorial structures are `hV` and `hlogY`.
  `IsDivisorialFor` identifies the whole monoid presheaf with the existing
  `divisorialLogPresheaf` and commutes with `divisorialStructuralMap`.
  Thus the identification is over functions, not just an abstract log isomorphism.
  The inverse image boundary is represented by `q.base ⁻¹ᵁ B.support.compl`.
  Divisorial structures depend only on reduced boundary support, so this also
  implements the instruction to reduce inverse image boundaries.
* The unramified smaller complement is exactly
  `hetale : Etale (q.base ∣_ D.support.compl)`.
* The conclusion of `kummer_boundary_restriction` supplies log structures MV, MY
  on the same schemes, proofs of fine saturation, a log morphism f and action b.
  The two `IsDivisorialFor` clauses specify precisely the smaller boundary log
  structures. `f.base = q.base` and `b.baseAction = a.baseAction` preserve the
  given morphism and action. The remaining clauses give the smaller Kummer etale
  G-cover, source log regularity, and `b.IsVeryTame`. Uniqueness of structural
  inclusions into functions means the existential presentations cannot substitute
  an unrelated log map or action.
* `kummer_cover_fs_baseChange` handles an arbitrary fs morphism b, including a
  non-Noetherian base Y'. It asserts existence of the fs pullback square, the
  pulled-back Kummer G-cover, and the two equations defining the induced action.
  It assumes no product exists in advance. The categorical pullback quantifies
  over all fs log objects, since the category has no Noetherianity field.
* `kummer_cover_logRegular_veryTame` uses the original locally Noetherian bundle,
  the given action, and `hY : Y.IsLogRegular`. Its first two conclusions are
  source log regularity and very tameness. For every open in the base's
  triviality locus it gives finite etale surjectivity and the simply transitive
  action on every geometric fibre, exactly an ordinary finite etale G-cover.
  At any geometric point with trivial inertia it supplies an open neighbourhood
  where the underlying scheme morphism is etale. Its neighbourhood formulation
  describes the entire trivial-inertia locus without assuming it is affine.
* `kummer_cover_logBlowup_normalization` takes the saturated log blowup b and its
  nonempty coherent ideal I, the explicit birational condition (an isomorphism
  on a dense open), and the actual fs pullback square. On the trivial-log open U,
  the original generic cover after pullback to Y' is the scheme
  `pullback f.base ((b.base ⁻¹ᵁ U).ι ≫ b.base)`. Its composite to Y' is normalized
  using Mathlib `Scheme.Hom.normalization`. The conclusion supplies the qc and qs
  proofs required to construct that normalization and an isomorphism over Y'.
  The further map j commutes with both original generic projections and satisfies
  `j ≫ e.hom = Scheme.Hom.toNormalization ...`; this fixes the identification on
  the given generic cover, instead of selecting an unnormalized isomorphism.
* Finite disjoint unions: all theorems quantify over arbitrary schemes without
  integrality, connectedness, or nonemptiness hypotheses, so they apply to the
  whole union and each relevant component. The group may permute components.
  The normalization is Mathlib's relative normalization, which also permits
  disconnected schemes; no function field of a disconnected scheme is used.

Recorded dependency declarations used:

* Sheaf.AlgebraicGeometry.IsRegularScheme: AlgebraicGeometry.IsRegularScheme.
* Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian and IsNoetherian.
* Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary:
  IsStrictNormalCrossingsBoundary (the node's stipulated strict special case).
* WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible:
  Scheme.IdealSheafData.IsInvertible, used in the existing normal-crossings predicate.
* Sheaf.AlgebraicGeometry.NormalCrossingsDivisor:
  Scheme.IdealSheafData.IsNormalCrossingsDivisor.
* Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup: EtaleLogStructure,
  IsFineSaturated, FineSaturatedLogScheme, EtaleLogHom, IsLogRegular,
  IsSaturatedLogBlowup, ideal and characteristic constructions.
* Sheaf.AlgebraicGeometry.LogIdealChartPresentation: EtaleLogMap and toLogMap;
  Sheaf.AlgebraicGeometry.LogMorphismOperations: its real identity/composition
  and their already proved laws. These are publicly imported by KummerEtaleGCover.
* Sheaf.AlgebraicGeometry.FSLogSmoothEtale: EtaleLogStructure.chartToSpec.
  Compatible charts and canonical comparisons use this precise construction.
* Sheaf.AlgebraicGeometry.FSLogGroupAction: FSLogGroupAction, IsTame,
  IsGenericallyFree. Sheaf.AlgebraicGeometry.VeryTameFSLogAction: IsVeryTame.
* Mathlib.AlgebraicGeometry.Normalization: Scheme.Hom.normalization,
  fromNormalization and toNormalization. The affine integral closure and gluing
  constructors were read, including their qc/qs arguments.
* All currently recorded proof modules are imported without public:
  AssociatedLogUniversalStalks, TraceFormula.LogRegularDivisorialStructure,
  TraceFormula.FiniteBaseStrictLocalization, FiniteGroupInertiaInvariantsEtale,
  LogBlowupNormalization. Unstated proof nodes have no module to import.
  VeryTameFSLogAction is already a public statement dependency.

Edge cases checked before writing and on rereading: empty component selection,
empty boundary, empty scheme, trivial group, characteristic zero, residue
characteristic dividing |G| but not inertia orders, self-intersecting global NC
components, nonintegral finite disjoint unions with permuted components, identity
log blowup, and non-Noetherian fs base change. Chart monoids may have units and
need not be sharp. No equality between the scheme and finite group universes is
imposed. Empty covers of an empty base are permitted. No construction chooses
undetermined data from a sorry theorem; all new definitions have full real bodies.

Searches: msearch.py leanfinder, query 'Kummer etale covers stable under fine saturated
log base change removing unramified boundary', returned ordinary etale base-change
results; loogle '"Kummer"' returned field Kummer theory, not log geometry; Mathlib
grep 'Kummer|Abhyankar|VeryTame' in AlgebraicGeometry returned no hits. Further real
LeanSearch, LeanFinder and grep searches for the new notions are saved verbatim in
each new node's mathlib_searches from this sandbox's searches.jsonl. Their results
were ordinary etale rings, normalization, and ordinary scheme diagonals, with no
matching logarithmic cover or boundary-selection definition. Repository rg searches
in WeilConjectures and Sheaf found the recorded log structures, Kummer morphisms,
actions and normal-crossings predicate, all reused here. No existing G-cover
predicate or named divisorial-presentation/component-selection predicate was found.
`rg -n 'lem-per-kummer-boundary-restriction' lean/WeilConjectures` gave no match.
DAG searches and `tools/blueprint_refs.py search 'Kummer etale'` and `search 'divisorial'`
found no definition node for the combined notions. The ancestor tool returned
lem-per-artin-gabber-affine-curve. The old CompactObject example is now withdrawn;
its node now records the upstream WeilConjectures.CategoryTheory.CompactObject
module, so the current module header conventions in brief-stage2.md were followed.

## New nodes

`def-per-kummer-etale-g-cover` owns KummerEtaleGCover.lean. It defines the exact finite
surjective cover with the actual canonical fs G-diagonal of ILO VI 2.1--2.3. A
coproduct cocone and a pullback cone with specified summand projections express
that diagonal without assuming existence of a chosen fs product. The action is
prescribed and obeys all group laws. The existing KummerLogMorphism module only
gives the Kummer-on-characteristics predicate and strict-local charts, not this
G-cover notion or an unrestricted-base compatible-chart cover. Its
`EtaleLogHom.IsKummer` explicitly takes `FineSaturatedLogScheme` endpoints, so it
cannot be applied to the potentially non-Noetherian fs base changes in the item.
ILO VI 2.1--2.2 gives the injective positive-power compatible-chart criterion used
by `FSLogScheme.IsKummerEtale`; on locally Noetherian objects this is the same
Kummer-etale condition, and it also applies to the arbitrary fs base changes.
There is no second characteristic-stalk Kummer predicate here.

This new node also owns the unrestricted `FSLogScheme`, its category, forgetful
functor, the conversions `toFSLogScheme` and `locallyNoetherian`, and the entire
`FSLogScheme.Chart` family. The category uses the original `EtaleLogMap` identity,
composition and laws. Chart maps reuse the original `chartToSpec`, and comparison
uses the actual scheme pullback. Kernel, cokernel, torsion and local order tests
are the same formulas as the recorded locally Noetherian chart interface. The new
node statement spells out these constructions and the smooth/etale covering tests.
These helpers now live in KummerEtaleGCover.lean; every helper docstring carries
this owning node's id, and lean.declarations records all fifteen declarations.
Searches described above found no unrestricted category/chart interface in the
DAG or library; the two original nodes give locally Noetherian bundles.

`def-per-divisorial-log-cover-boundary` owns DivisorialLogCoverBoundary.lean. It
names the structural-compatible divisorial presentation and reduced component
selection used by ILO VI 1.4 and VIII 5.3.8. It reuses the actual divisorial
presheaf, structural inclusion, ideal radicals and irreducible components.
No log sheaf is reconstructed or chosen. Existing LogRegularPair gives the real
presheaf and a stronger log-regular-pair predicate, not the two predicates needed
here before log regularity has been established. The searched DAG and libraries
had no corresponding standalone definition.

## Returned delivery repaired

The return on immutable head 9bcc31487f37 reported H13: the packet had rebound
two landed dependency records to generalizations of their interfaces. The saved
packet passed the initial mechanical dry run (2ae1363f60d), but rereading confirmed
that this review finding remained. It has now been repaired by the option the
maintainer specified: consolidate the category and chart helpers in the new
`def-per-kummer-etale-g-cover` module. No dependency record is rebound.

* `def-trf-fs-log-blowup.json` is restored byte-for-byte from live, preserving Q49's
  primary `IsSaturatedLogBlowup` and its full original declarations list.
* `def-per-fs-log-smooth-etale.json` is restored byte-for-byte from live, preserving
  NG's primary `EtaleLogHom.IsLogSmooth`, `FSLogChart` and all original declarations.
* The separate FineSaturatedLogCategory.lean and FSLogChartGeneral.lean files are
  removed from the packet. The new cover module publicly imports the original
  dependency modules, and owns all unrestricted helpers itself. Its new node still
  cites exactly `def-trf-fs-log-blowup` and `def-per-fs-log-smooth-etale`.
* The minor Kummer-interface point is addressed in the cover module docstring,
  its new node's lean.note, and the New nodes section above: arbitrary fs base
  change may be non-Noetherian, so the old locally Noetherian Kummer predicate
  cannot type this assertion. The chart criterion is ILO VI 2.1--2.2.

The four main theorem signatures and their hypotheses and conclusions remain
unchanged; the consolidation changes ownership and imports, not their mathematics.

## Second reading by Q107

A separate manual rereading checked the node, every signature and every new body.
The dispatcher explicitly forbids starting another agent; this section records
Q107's own rereading, not an invented independent worker review. The maintainer's
independent delivery review remains required.

The reading caught and repaired the overly restrictive use of the original fs
bundle for arbitrary base change, a nonexistent normal-scheme class, and the need
to fix the normalization isomorphism on the prescribed generic cover. The final
normality predicate allows disconnected schemes. The fs G-diagonal uses both
universal properties and both prescribed projections, and includes the identity
and multiplication action laws. It is consequently stronger than just a finite
Kummer map and precisely the cover clause in the node. The four theorems together
cover every clause listed in Worker report. No theorem was proved and no part of
the natural-language statement was silently corrected.

The repair self-check reread the original live dependency records and their source
interfaces, the consolidated new definition node, all fifteen helper declarations,
and all four theorem signatures. Both restored node files match live bytes. Every
new helper is listed under the cover node, with matching blueprint docstrings;
there is no declaration lost by the consolidation. The new node explicitly covers
unrestricted fs objects and chart tests, while the original dependency statements
and records still describe their locally Noetherian objects. This repairs H13
without restricting arbitrary base change or changing the cover's fs G-diagonal.
