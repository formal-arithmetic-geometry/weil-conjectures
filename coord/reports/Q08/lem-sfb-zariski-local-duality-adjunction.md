## Worker report

Stage 2, Q08, lem-sfb-zariski-local-duality-adjunction, 2026-10-23.
The earlier worker ending was a stage-1 split refusal, not a stage-2 blocker.
The current node is split and reviewed PASS with no Lean record. The handoff
paragraph of coord/brief-stage2.md §0 explicitly authorizes this stage-2 delivery.
The accepted mathematical statement and proof are preserved.

The module Sheaf.AlgebraicGeometry.ZariskiLocalDualityAdjunction states
AlgebraicGeometry.zariskiLocalDualityAdjunction, with exactly one sorry.
Its three helper definitions construct G, the canonical projection mate, and the
canonical pullback unit identification. No theorem is proved and no definition
contains sorry. Helpers belong to this node's trace-adjunction construction and
are all recorded in lean.declarations. No new node or dependency repair is needed.

Clause-by-clause correspondence:

- Arbitrary schemes and a morphism f:X→S: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Quasi-compact separated morphism: `[QuasiCompact f] [IsSeparated f]`.
  There are no CompactSpace or QuasiSeparatedSpace binders on either scheme,
  and no properness, finite-type or Noetherian assumption.
- Unbounded derived categories of modules with quasi-coherent cohomology:
  `schemeDerivedQCohCategory`, the recorded full subcategory of
  `schemeDerivedCategory`. Its objects are unrestricted in cohomological degree.
  The uniform HasDerivedCategory binder chooses representations for the derived
  categories of all schemes, including every open under consideration, as the
  imported canonical-comparison API requires. It is category-existence data,
  not a geometric assumption or an equality between different site universes;
  standard derived localizations supply such data. Universes u and w are explicit.
- K∈D_QCoh(X): `(K : schemeDerivedQCohCategory X)`; its underlying object is K.obj.
- The trace Rf*K→O_S: `τ : (schemeDerivedDirectImage f).obj K.obj ⟶ 𝟙_ ...`.
  The tensor unit is the recorded K-flat derived tensor unit O_S[0].
- G(M)=Lf*M⊗^L K: `zariskiTraceTensorFunctor f K.obj` is literally
  `derivedPullback f ⋙ tensorRight K.obj`. It is defined on the full module
  derived categories and evaluated on the QCoh inclusion. Pullback/tensor
  preservation of QCoh makes this the stated QCoh functor without adding data
  or hypotheses asserting preservation.
- Trace-defined natural ε: the binder ε is a natural transformation from
  QCoh inclusion followed by G and Rf* to QCoh inclusion. The binder hε says
  `zariskiTraceProjectionMap f M.obj K.obj ≫ ε.app M =
  M.obj ◁ τ ≫ (ρ_ M.obj).hom` for every QCoh M.
  The canonical projection map has direction M⊗Rf*K→Rf*(Lf*M⊗K).
  It is the transpose under `canonicalPullbackAdjunction` of the fixed
  K-flat tensor comparison followed by the pullback/direct-image counit.
  It is invertible by unbounded projection formula 08EU. Thus hε is exactly
  ε = inverse projection followed by 1⊗τ and the unit identification.
  It specifies the counit supplied by the node; it is not an arbitrary ε or an
  added adjointness assumption. This equation also avoids choosing an arbitrary
  isomorphism from a bare Nonempty projection-formula statement.
- Every affine open V⊂S: `∀ V : S.Opens, IsAffineOpen V → ...` in hlocal.
  X_V and f_V are `(f ⁻¹ᵁ V).toScheme` and `f ∣_ V`; no cover is selected.
- Restricted coefficient: `(derivedPullback (f ⁻¹ᵁ V).ι).obj K.obj` is K|X_V,
  since open derived pullback is exact restriction (08DW).
- Exactly the restricted trace: hlocal supplies τV satisfying
  `schemeDerivedBaseChangeMap ... K.obj ≫ τV =
  (derivedPullback V.ι).map τ ≫ (zariskiTracePullbackUnitIso V.ι).hom`.
  This is the canonical cartesian open square, with commutativity witnessed by
  `(morphismRestrict_ι f V).symm`. Its base-change map is invertible (08FE),
  so this equality uniquely specifies τV as the restriction of τ, without
  assuming an arbitrary trace. The unit identification is constructed from
  `canonicalPullbackTensor_monoidal_realization` applied to the same normalized
  tensorator; the tensorator fixes the unit by the monoidal unit laws.
- Local G_V: `zariskiTraceTensorFunctor (f ∣_ V) (K|X_V)` uses that exact
  restricted coefficient. The second local conjunct normalizes εV by its
  projection mate and τV just as hε does globally.
- G_V right adjoint to Rf_V* with this counit: the last local conjunct is
  bijectivity of `a ↦ (schemeDerivedDirectImage (f ∣_ V)).map a ≫ εV.app M`
  for every local QCoh E and M. Since εV is a natural transformation and G_V
  is a functor, these bijections are natural in both arguments and are exactly
  the Hom-bijection definition of this adjunction. This does not presume a
  global adjunction. Quantifying the fully normalized local counit is a way
  to state the local adjunction, not an extra local compatibility assumption.
- Global conclusion: for every QCoh E and M, bijectivity of
  `a ↦ (schemeDerivedDirectImage f).map a ≫ ε.app M`, with source
  `E.obj ⟶ (zariskiTraceTensorFunctor f K.obj).obj M.obj`.
  The target is inferred as `(schemeDerivedDirectImage f).obj E.obj ⟶ M.obj`.
  Naturality in E is Functor.map_comp and associativity; naturality in M is
  precisely ε.naturality. Thus the stated concrete family of bijections is
  natural, without independent choices of inverse Hom maps or a weakened
  bare existence of some adjunction.
- No qcqs assumption on individual schemes, finite cover, or boundedness:
  none occurs in the signature. All opens and all derived objects are retained.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- WeilConjectures.AlgebraicGeometry.DerivedCategory: schemeDerivedCategory,
  schemeDerivedQCohProperty and schemeDerivedQCohCategory, with the shared
  SheafOfModules module category and Mathlib's abelian structure.
- WeilConjectures.AlgebraicGeometry.DerivedPullback: derivedPullback and its
  K-flat derived-counit specification; exact restriction for open immersions.
- WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage:
  schemeDerivedDirectImage, the ringed-space K-injective construction.
- WeilConjectures.AlgebraicGeometry.DerivedTensorStructure:
  schemeDerivedTensorMonoidal, the global K-flat tensor, not a new tensor.
- def-pur-derived-internal-hom occurs only in the proof narrative; the unused
  OrdinaryModuleDerivedInternalHom import was removed following advisory H9.
  No RHom is redefined.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: IsSeparated and QuasiCompact
  (through its imports), as recorded by def-weil-proper-morphism and
  def-weil-finite-type-morphism. IsProper and LocallyOfFiniteType are not assumed.
  The unused explicit FiniteType import was removed following advisory H9.
- WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso:
  mixedHomTensorPullbackIso and exists_mixedHomTensorPullbackIso, including
  the chosen tensorator and its canonical normalization certificate.
- Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap (compatibility reexport
  of WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap):
  canonicalPullbackAdjunction, the canonical normalized pullback/direct-image
  adjunction. This definition is owned by def-pc-affine-global-hom-base-change-map;
  it is not an assumption that G is a right adjoint.
  Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso and MixedHomTensorPullbackIso
  are compatibility modules reexporting this exact source; the smaller source
  import is preferred under the brief's duplicate-declaration guidance.
- WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization:
  canonicalPullbackTensor_monoidal_realization fixes the monoidal unit from the
  specified canonical tensorator, rather than choosing an unspecified unit.
- WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap:
  schemeDerivedBaseChangeMap, the counit-normalized cartesian mate.
- Mathlib.AlgebraicGeometry.Restrict: morphismRestrict_ι, the actual open square.

The four already landed canonical-interface nodes are added to stmt_deps:
def-pc-derived-base-change-map, def-pc-affine-global-hom-base-change-map,
lem-sc-mixed-hom-tensor-pullback-iso, and
lem-pc-canonical-pullback-tensor-monoidal-realization. This is the explicitly
permitted addition of landed statement dependencies, not a statement correction.
Their full source signatures and docstrings were read. No dependency node changes.

Available proof dependencies are plain imports: DerivedPullbackTensorQCoh,
DerivedDirectImagePreservesQCoh, Cohomology.DirectImage.Sections,
DerivedPullbackOpenRestrictionUniverses, DerivedTensorOpenRestrictionNatural,
DerivedDirectImageOpenRestriction, and UnboundedDirectImageSectionPresheaf.
The separated-implies-quasi-separated Mathlib leaf is provided by Proper.
The direct-image-Hom-open-Ext and open-Ext-hypercohomology nodes currently have
no Lean record, so there is no module to import yet. They are proof dependencies,
not missing notions needed for this statement.

Interface observation: lem-pc-projection-formula's recorded primary declaration,
Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso in Sections,
is a module/higher-direct-image specialization. It does not itself define the
canonical unbounded projection inverse needed here. The delivery therefore uses
the canonical derived projection mate built from the existing normalized
adjunction and tensorator; the main statement normalizes ε against that mate.
No inadequate module-level theorem is used as unbounded definition data.
The intended unbounded projection-formula node remains the mathematical proof input.

Sources opened: literature/stacks-project/duality.tex, equation-sheafy-trace
and section-trace (including the explicit u↦Tr∘Rf*u formula);
perfect.tex Tag 08EU; cohomology.tex Tags 08DK, 08FE, 0B69 and 0D5X.
The statement is the accepted agent local-to-global consequence, not the
qcqs right-adjoint existence theorem in duality.tex assumed globally.
No source-based correction is required; no STATEMENT-DISPUTED issue was found.

Edge checks:

- Empty schemes and the empty affine open are included. Their module derived
  categories are zero categories, so the unique normalized counit gives bijections.
- Identity morphism, K=O_S, identity trace: G is canonically the identity and
  the normalized maps are the expected identity adjunction maps.
- A zero trace over a nonempty affine scheme with nonzero structure ring does
  not accidentally satisfy the local hypothesis: the map on Hom from a unit
  with a nonzero identity cannot be bijective when its counit is zero.
- K=0 or E=0 or M=0: zero arguments are retained. A local adjunction for K=0
  forces the stated vanishing of all tested pushforward Hom groups; nothing
  removes this case through a nonzero or nonempty hypothesis.
- S need not be quasi-compact or quasi-separated; all its affine neighbourhoods
  occur, and their inverse images are qcqs by the morphism hypotheses.
- E and M may have cohomology in arbitrarily many positive and negative degrees.
- There is no independent test-object universe making the affine test vacuous;
  opens are the actual opens of S, and coefficients use its own derived category.

Searches for an existing exact statement (outputs retained in searches.jsonl):

- msearch.py leanfinder: “A global trace defines a derived adjunction if its
  counit is an adjunction on every affine open of the base”. Eight hits, all
  scheme/global-sections adjunctions, no trace-defined local-to-global criterion.
- msearch.py loogle: “CategoryTheory.Adjunction, AlgebraicGeometry.Scheme”.
  Six hits: opensFunctorAdjunction, ΓSpec.adjunction, kerAdjunction,
  algΓAlgSpecAdjunction, Modules.pullbackPushforwardAdjunction and
  Modules.restrictAdjunction. All are underived/different adjunctions.
- msearch.py grep: “local.*adjunction|adjunction.*local”, Mathlib/AlgebraicGeometry.
  Zero hits.
- msearch.py leansearch: “Derived pushforward has trace defined right adjoint
  if this holds on every affine open subset”. Eight underived pushforward or
  site pullback-adjunction hits, no exact match.
- rg of lean/WeilConjectures and lean/Sheaf for trace-defined/traceDefined,
  zariski_local_duality, Zariski local adjunction, counit/trace combinations:
  no matching theorem. Sibling global-Hom and QCqsDerivedProjection modules
  were inspected; their global qcqs/right-adjoint hypotheses differ.
- rg of the item ID in lean/WeilConjectures: zero hits.
  The DAG itself is the already existing owner; no new definition node is created.

Validation: scompile.py Q08 lem-sfb-zariski-local-duality-adjunction compiled
this module in sandbox and library modes with no errors or warnings (8.3 s and
9.7 s). All variables and universes are explicit; autoImplicit is false.
The final delivery preflight and recompile results are appended below.

## Second reading by Q08

Author's separate clause check, not an independent review: no other agents were
started, as the dispatched brief forbids delegation. The maintainer supplies the
independent review. I reopened the live node and compared its full statement
with the final Lean signature and the bodies of all three helpers.

The main traps were using a bare Nonempty projection isomorphism, forgetting
which local trace defines the counit, and accidentally requiring qcqs schemes.
The final definitions pin the projection mate to the existing normalized
pullback adjunction and K-flat tensorator; hlocal pins τV to the actual open
base-change mate and requires the identical projection normalization locally.
There are only morphism-level quasi-compactness and separatedness instances.
QCoh binders are the full unbounded categories. The natural transformations ε
and εV ensure that the concrete Hom bijections are natural in both variables.
No statement hypothesis, conclusion clause, or zero/empty case was dropped.

All three helper definitions have real data and their own source/blueprint
docstrings. The monoidal witness used for the unit has a fixed tensorator,
so its unit is determined by the unit axioms, as the dependency node explicitly
records. The only sorry is the named theorem, with the accepted four-step
natural-language proof in its docstring. The accepted stage-1 split is unchanged.

## Return repair R1 and advisory H9

The saved packet was inspected first and deliver2.py --no-push passed on
2026-10-23 (commit 0f42e500124). That mechanical pass did not repair the
independent reader's ownership objection at returned head e4ed26a821ae.
The current live node still has no Lean record; comparison of its JSON with
the saved packet found only lean and the four added stmt_deps as differences.
The accepted statement, proof, proof_deps and stage-1 review remain unchanged.

R1: replaced the added theorem dependency lem-pc-global-hom-adjunction with
the already landed definition node def-pc-affine-global-hom-base-change-map.
Read its lean.declarations ownership and source signature/docstring. Its
canonicalPullbackAdjunction and schemeHomPullbackAdjunction have literally the
same body: Classical.choose of exists_schemeDerivedAdjunction with the three
fixed exists_derivedPullbackComposition choices. Neither adds scheme qcqs,
right-adjoint existence, or global Hom assumptions. The projection-map helper
now uses canonicalPullbackAdjunction for both its Hom equivalence and counit,
and publicly imports its recorded compatibility module. The tensorator still
comes from mixedHomTensorPullbackIso, with its choose_spec normalization.
The normalized unit construction, theorem signature, and all local/global
clauses are unchanged. No new definition node or dependency repair is needed.

H9: removed the two identified unused public imports,
OrdinaryModuleDerivedInternalHom and Morphisms.FiniteType. Proper still provides
the needed QuasiCompact and IsSeparated definitions. The retained proof imports
are the proof plan, as required by stages/2-statements.md §3.7.

Self-check on repair: reopened the node and complete module; only the projection
helper's adjunction name and imports changed. All hypotheses and clauses checked
above still match verbatim, and zero/empty and unbounded cases are retained.
The definition chosen is exactly the same normalized adjunction term; no new
mathematical assumption or theorem is used. Validation results follow below.

Repair validation: scompile.py compiled the repaired module cleanly in sandbox
mode (34.7 s) and library mode (13.3 s), with no errors or unexpected warnings.
The exact signature matches lean.statement; line widths are at most 100,
autoImplicit is false, and the only sorry is the main named theorem.
A fresh absolute-path comparison with the live node confirms differences only
in lean and stmt_deps (the four added landed interfaces listed above).

Final repaired dry run: deliver2.py --no-push returned
“OK (dry run): commit 20fed4d7b48 passes the preflight and compiles; nothing pushed”.
