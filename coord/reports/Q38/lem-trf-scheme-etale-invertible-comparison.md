## Worker report

Repair of the empty delivery returned at immutable head 77c120af76ab. The retained
sandbox initially contained only dispatcher marker files: no Lean file, node copy,
or report. This packet supplies the implementation and documentation requested in
all return findings H1–H3 and H11. It changes only the item's `lean` record against
the current node; the delivery wrapper rebases the packet on current newtargets-dag.
No mathematical statement, dependency list, proof plan, or target is changed.

Module: `Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison`.
Main declaration:
`AlgebraicGeometry.Scheme.scheme_etale_invertible_comparison`.
The module also contains the explicitly constructed ring, full subcategories,
section-sheaf abbreviations, postcomposition functor, canonical tensor comparisons,
and maps needed to state that theorem. All are listed in `lean.declarations`.
The ring has fixed section data and a separately named sheaf-condition theorem;
no definition obtains its data from an existence theorem or a `sorry`.

Source reading: `literature/stacks-project/descent.tex`, labels
`proposition-equivalence-quasi-coherent` (03DX), part (2),
`lemma-equivalence-quasi-coherent-properties` (05VG), finite locally free property,
and `proposition-equivalence-quasi-coherent-functorial` (03LC), part (1).
03DX concerns the actual associated functor, 05VG restricts it to rank-one locally
free modules, and 03LC supplies the pullback comparison. No quasi-compactness,
separatedness, Noetherian, connectedness, or nonempty hypothesis occurs.
The docstring expands all eight proof steps of the item, including the frame
calculation and fpqc descent; the structure-ring helper has its own proof docstring.

Clause-by-clause match:

- A general scheme is `X : Scheme.{u}`. The theorem chooses a coherent family over
  all such schemes, so that its restriction clauses use the same comparison on X
  and Y. Universes are explicitly bound. Sites are exactly `X.Etale` and
  `X.smallEtaleTopology`; there is no independent smaller test-scheme universe.
- `trfEtaleStructureRing X` has underlying presheaf
  `X.etaleStructurePresheaf ⋙ forget₂ CommRingCat RingCat`. This evaluates to
  `Γ(U.left, ⊤)` and restricts by pullback of functions. The named theorem
  `trfEtaleStructureRing_isSheaf` postpones only the sheaf proof. Its data are
  the existing structure presheaf, without sheafification or arbitrary ring choice.
- Ordinary invertible modules use the recorded `Scheme.Modules.IsInvertible` in
  `TrfInvertibleModules X`. Its full subcategory has every ordinary module map.
  `trfInvertibleSections L` calls the recorded `etaleTensorSectionsSheaf L.obj`,
  using the existing quasi-coherence consequence of invertibility. Thus the groups
  and restriction maps are exactly Γ(U,u*L) and the canonical normalized restrictions.
- `TrfIsEtaleLine M` says there are a family of étale objects covering the final
  object and isomorphisms `M.over (U i) ≅ unit (R.over (U i))`. This is the node's
  precise localized-site definition. `GrothendieckTopology.CoversTop` is Mathlib's
  covering-final-object predicate; here it is equivalent to joint surjectivity.
  The index universe is u+1, the universe of the site objects; repetitions in any
  larger set-indexed family can be removed, so this loses no covering case.
  `TrfEtaleLineModules` is again a full subcategory, retaining all module morphisms.
- `E X : TrfInvertibleModules X ≌ TrfEtaleLineModules X` states the equivalence,
  rather than a bijection only on isomorphism classes or a groupoid equivalence.
  In particular its counit gives essential surjectivity onto every line module;
  its functor's fully faithful Hom equivalence gives the stated Hom bijection.
- The isomorphism `α X L` identifies the underlying additive sheaf of the functor's
  value with that exact recorded associated sheaf. The first equation requires
  α to intertwine its scalar action with the usual multiplication endomorphism
  `((tensorPullback U.hom).obj L.obj).smul r`. Thus these identifications also fix
  the sectionwise module action; the theorem cannot choose an unrelated equivalence.
- The next equation, for every `h : L.obj ⟶ K.obj`, fixes the functor's component
  at U to `((tensorPullback U.hom).map h).app ⊤` in the α coordinates.
  `trfComparisonMap` applies the functor to `ObjectProperty.homMk h` and forgets
  the full-subcategory wrapper. No invertibility assumption on h is imposed.
- `trfStructureInvertible X` is the ordinary structure module, with the existing
  invertibility proof. The existential ε is an isomorphism from its image to
  the actual étale structure module. Its equation pins ε to α followed by the
  canonical `trfTensorUnit U.hom`. This tensor-unit isomorphism uses the recorded
  unit-normalized adjunction and Mathlib's `pullbackObjUnitIso`, so the structure
  identification has its canonical normalization, not an arbitrary unit automorphism.
- The proof family p records preservation of ordinary invertibility under the
  étale tensor pullbacks used below. It is asserted in the conclusion, not supplied
  as an added hypothesis, and quantifies only over étale morphisms.
- `trfEtaleCompose v` sends `w:W→Y` to `w≫v` and preserves the underlying scheme
  map on morphisms. `PresheafOfModules.pushforward₀` is literal precomposition by
  this functor. Its coefficient presheaf is definitionally the structure ring on Y.
  Thus β is a module-presheaf isomorphism from the restriction of A_X(L) to
  A_Y(v*L). Both ends are sheaves: the target is a sheaf and β transports its
  sheaf condition to the restricted presheaf. No extra sheafification is inserted.
- The first β equation is precisely sections of the inverse normalized
  `tensorSectionsComp W.hom v` in the α coordinates. It fixes the comparison at
  every étale W, including empty objects and the identity object.
- The next β equation is the naturality square for every module morphism h,
  using `tensorPullback v |>.map h`. This is the required identification of
  A_X(h) restricted to Y with A_Y(v*h).
- The following equation treats `v=𝟙 X`: comparison followed by the image of
  the canonical `trfTensorId X` is the presheaf restriction along the identity
  structure-arrow comparison `trfEtaleIdArrow W`.
- The last equation treats arbitrary composable étale w and v. Successive β's
  followed by the image of `tensorSectionsComp w v` equal β for `w≫v`, with
  the explicitly constructed identity-on-W associativity arrow
  `trfEtaleCompArrow v w W`. Hence composition compatibility is a stated equation,
  including its structure-arrow transports, not only prose or a claimed property.

Dependency declarations actually used:

| Node / role | Module | Declaration |
| --- | --- | --- |
| schemes | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme |
| small étale site | Mathlib.AlgebraicGeometry.Sites.Etale | Scheme.Etale; Scheme.smallEtaleTopology |
| ordinary invertibility | WeilConjectures.AlgebraicGeometry.Modules.Invertible | Scheme.Modules.IsInvertible; isInvertible_tensorUnit |
| quasi-coherence of invertible modules | WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula | Scheme.Modules.IsInvertible.isQuasicoherent |
| associated additive sheaf | Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf | Scheme.Modules.etaleTensorSectionsSheaf |
| module pullback | WeilConjectures.AlgebraicGeometry.TensorPullback | Scheme.Modules.tensorPullback |
| canonical adjunction | WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction | Scheme.Modules.exists_tensorPullbackAdjunction |
| normalized restrictions / composition | Sheaf.AlgebraicGeometry.EtaleTensorSections | tensorSectionsComp; etaleTensorSectionsPresheaf |
| general ringed-site modules | Sheaf.CategoryTheory.RingedSiteModules | CategoryTheory.ringedSiteModules |
| étale structure functions | WeilConjectures.AlgebraicGeometry.Sites.Gm | Scheme.etaleStructurePresheaf; isSheaf_etaleStructurePresheaf |
| restriction and local units | Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous | SheafOfModules.over; SheafOfModules.overFunctor |
| literal site precomposition | Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward | PresheafOfModules.pushforward₀ |

The recorded size convention has no Lean object; explicit universe binders implement
it. Stated proof-dependency modules are imported, including Descent,
ZariskiEtaleInclusionMorphismOfSites, FpqcFinerThanEtale, and SiteCoveringAxioms.
The remaining proof APIs (étale covering composition and open restriction) are
available through the site and module imports. No dependency record is replaced.

Searches for existing declarations:

- msearch LeanFinder: `invertible modules line modules etale site equivalence`.
  Eight results concerned étale loci and ring maps; no comparison theorem.
- msearch Loogle: `Scheme.Modules.IsInvertible, smallEtaleTopology, SheafOfModules`.
  No results; Loogle did not recognize the project-only first name.
- msearch grep: `invertible.*etale|etale.*invertible`, Mathlib AlgebraicGeometry.
  No results.
- msearch LeanSearch: `invertible sheaves equivalent to rank one modules on the small
  etale site`. Eight hits included Scheme.smallEtaleTopology, Scheme.Modules,
  SheafOfModules, and algebraic Picard groups; none states this comparison.
- msearch grep: `etaleStructure|IsInvertible|over_unit`, Mathlib AlgebraicGeometry/Sites.
  No results. Direct rg of the project found the genuine existing structure
  presheaf, which is reused rather than copied.
- Direct rg of WeilConjectures and lean/Sheaf for `etaleTensorSectionsSheaf`,
  `etaleStructurePresheaf`, invertibility, and étale comparisons found the dependencies
  listed above. Searches of the new full declaration names in Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json found no collision.
- The generic upstream `SheafOfModules.IsInvertible` was opened. Its local-generators
  interface requires sheafification on every localized site in the module universe.
  Those additional assumptions cannot be added here. The explicit localized-unit
  condition introduced by the item itself avoids that restriction and exactly states
  its line-module notion, using Mathlib's existing modules and localization API.

Edge cases checked: the empty scheme, empty étale objects, empty covering families
(on the empty scheme), arbitrary infinite covers, zero/noninvertible module maps,
identity étale maps, composites including identities, and disconnected schemes.
On a nonempty scheme the zero module is not an ordinary invertible object; on the
empty scheme the structure module may be zero and remains included. No finiteness,
nonempty index, or ambient inverse assumption is introduced. No STATEMENT-DISPUTED
or statement correction is required.

Compilation: prescribed scompile.py command on
`lean/Sheaf/SixFunctors/TraceFormula/SchemeEtaleInvertibleComparison.lean` passed
for both the sandbox probe and the exact library module path. Most recent completed
run: sandbox 5.7 s, exact module 36.6 s; exit 0; no errors or warnings. The only
postponed proofs are the named structure-ring sheaf theorem and the main comparison,
both with source/proof docstrings and this DAG node's blueprint reference.

## Author validation pass

Author's separate second pass against the node and source, not a claim of an
independent agent review. This dispatcher task forbids starting other agents;
the maintainer's review is the independent reading.

Opened the final module and the current JSON node together and checked every clause
listed above. Fixed the first incomplete draft by replacing its missing morphism and
restriction clauses with actual equations; the delivered theorem contains no True
placeholder. Checked that both subcategories retain all maps. Replaced a generic
local-free API requiring unavailable size assumptions by the node's exact localized
unit condition. Separated the ring sheaf proof from its fixed data. Narrowed the
pullback-preserves-invertibility conclusion to étale arrows so that it adds no
arbitrary-morphism clause. Added the canonical normalization of the structure-unit
isomorphism, and the explicit naturality, identity, and associativity equations for β.

Read the β equation in the forward direction: restricted A_X(L) → A_Y(v*L);
its α-coordinate formula uses the inverse of tensorSectionsComp, as required.
Read the composition equation: β_v then β_w then A(c_w,v), versus β_(w≫v) after
restriction along the site associativity arrow. Both sides have the same target.
Read the identity equation with the adjunction-normalized identity comparison.
Checked ε against actual ordinary and étale structure modules, rather than only
asking for some object isomorphic to a unit. Checked that the scalar equation turns
α into a linear identification and that the module-map equation gives its exact
naturality, eliminating any unconstrained functor choice.

There are no new definition nodes or dependency modules: these helpers implement
notions and canonical comparisons explicitly introduced by this item's statement,
as permitted by the human's helper-declaration rule. No data is chosen from an
unconstrained existence theorem. Definitions and exact declaration names were
rechecked, all binders and u were inspected, line lengths are at most 100, and the
node signature is copied directly from the theorem. The prescribed delivery
preflight remains the final mechanical check.

## Second reading by Q38

Independent maintainer second reading, 2026-10-18, of immutable delivery
`e0922bbf7a6f4272e322ed6f035439284d0315fb`. This reader did not author the
module or perform the author validation pass preserved above. Read the packet,
the actual snapshot module and node, all seven statement dependency records and
their exact declarations, and the source text. The only correction is this report:
the original section explicitly described an author self-check, not an independent
second reading. The Lean module and node need no correction.

Clause checks, independently verified:

- General schemes: `Scheme.{u}` is unrestricted; `X.Etale` and
  `X.smallEtaleTopology` are the recorded small étale site. There is no qcqs,
  Noetherian, separated, nonempty, or field hypothesis. Explicit `universe u`
  and `autoImplicit false` bind the entire statement.
- Structure ring: `trfEtaleStructureRing` reuses `etaleStructurePresheaf`, with
  sections exactly `Γ(U.left, ⊤)` and the scheme restriction maps, then forgets
  commutativity. Its named sheaf theorem postpones only a property of fixed data.
- Ordinary objects: `TrfInvertibleModules` uses the recorded
  `Scheme.Modules.IsInvertible`. Its local rank-one condition implies the
  required quasi-coherence by the existing `IsInvertible.isQuasicoherent` instance.
  `trfInvertibleSections` uses the recorded `etaleTensorSectionsSheaf`, whose
  underlying groups and normalized tensor-pullback restrictions were opened.
- Target objects: `TrfIsEtaleLine` requires local unit isomorphisms on `J.over U`
  and `CoversTop U`. At the terminal étale object this is the covering sieve
  of the family, equivalent to joint surjectivity. Both categories are full
  subcategories, so zero and noninvertible morphisms are retained.
- Comparison: `E` is an equivalence of these full categories. Its essential
  surjectivity and fully faithful Hom maps give both particular conclusions.
  The additive-sheaf isomorphisms `α`, scalar equation, and equation for every
  `h` specify the actual associated module-sheaf functor up to the stated
  canonical identifications; an unrelated equivalence cannot satisfy them.
- Structure comparison: `ε` is a module-sheaf isomorphism to the actual structure
  module. Its component formula uses `trfTensorUnit`, obtained from the canonical
  tensor adjunction, uniqueness of left adjoints, and `pullbackObjUnitIso`.
  The chosen adjunction's theorem fixes its unit sectionwise; this is not a
  choice from an unconstrained existence statement.
- Étale restriction: `trfEtaleCompose v` evaluates at `w ≫ v`.
  `pushforward₀` is literal precomposition of module presheaves. The coefficient
  presheaf is the structure presheaf on Y. The module-presheaf isomorphism `β`
  transports the target sheaf condition to its source, so a separate assumed
  continuity or sheafification hypothesis is unnecessary.
- The first β equation specifies sections of the inverse composition comparison.
  The next equation is naturality for every ordinary module map. The last two
  equations give identity and composition coherence with the required site-object
  transports. The source and target of each composite agree. The existential
  proof family `p` states preservation of invertibility; it is not a hypothesis.

Source checks: Stacks `descent.tex`, labels
`proposition-equivalence-quasi-coherent` (03DX), part (2),
`lemma-equivalence-quasi-coherent-properties` (05VG), finite local freeness,
`proposition-equivalence-quasi-coherent-functorial` (03LC), part (1), and
`remark-change-topologies-ringed-sites`. These assume arbitrary schemes for
these clauses. The rank-one specialization and the eight-step frame/descent
proof match the node. In particular 05VG's caveats for general locally free or
coherent modules do not restrict finite locally free rank one.

Edge cases: empty schemes, empty étale objects, empty covers of an empty scheme,
arbitrary infinite covers, disconnected schemes, zero and noninvertible maps,
identity morphisms, and composites involving identities are included. The cover
index `Type (u + 1)` is the site-object bound; larger repetitive families reduce
to the image family without losing local trivializations. No extra equality of
independent site universes or sheafification assumption was imposed.

Independent searches in Mathlib, WeilConjectures and lean/Sheaf for étale line
modules, invertibility comparisons, structure-ring sheaves, and the delivered
names found no exact existing comparison or usable duplicate of the local-unit
predicate. Opened the upstream generic `SheafOfModules.IsInvertible`: its
localized sheafification hypotheses are absent here, so it is not a replacement
interface at these universes. Existing structure functions, ordinary
invertibility, tensor pullback, and associated additive sheaves are reused.

Both theorem bodies are exactly `by sorry`; definitions have real data. The
three short proof terms inside site-arrow constructions establish their
commutative triangles, not additional mathematical theorem proofs. All 15
declarations are recorded, have source/blueprint docstrings, and the main
docstring follows all eight proof steps. Lines are at most 100 characters.
The node's `lean.statement` equals the complete theorem signature verbatim.
The immutable diff changes only `lean` in the item node, plus the new module
and report. There are no new nodes, dependency repairs, or statement corrections
requiring a citer audit. No dropped route-pivot dependency or pro-étale
substitute occurs, and no route-pivot repair note exists for this item in the
inspected shared reference.

Reproduced the exact snapshot file with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q38 \
  lem-trf-scheme-etale-invertible-comparison \
  snapshot/lean/Sheaf/SixFunctors/TraceFormula/SchemeEtaleInvertibleComparison.lean
```

The installed wrapper used its server side overlay and confirmed both the
sandbox probe (5.6 s reported) and exact library-module check (93.1 s reported).
Exit code 0, empty diagnostic streams, no errors or warnings. The latter number
is the wrapper's reported elapsed time; it did not report a Lean timeout.
No global build, direct SSH command, delivery, merge, Git mutation, or live Lean
write was performed. Full independent review and source/API locations are also
recorded in the maintainer review.md. Verdict: FIX, solely to replace the
self-check section with a real independent reading while preserving its history.
