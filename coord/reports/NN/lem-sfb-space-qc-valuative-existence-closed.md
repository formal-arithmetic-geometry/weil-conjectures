## Worker report

Module `Sheaf.AlgebraicGeometry.AlgebraicSpaceValuativeExistenceClosed` states
`AlgebraicGeometry.AlgebraicSpace.universallyClosed_of_quasiCompact_of_valuativeExistence`.
Its sole proof is `sorry`. There are no new definitions, new nodes, dependency repairs,
or statement corrections. Source read in full: `literature/stacks-project/spaces-morphisms.tex`,
Tag 03KA, `lemma-quasi-compact-existence-universally-closed`, and Tag 03IX,
`definition-valuative-criterion` (including its explanatory paragraphs).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Scheme S; algebraic spaces X,Y over S; morphism f | `{S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)` |
| Sheaf fibre products and usual point topology | Imported existing `AlgebraicSpaceMorphismProperties`, whose definitions use the sheaf pullback and `pointTopologicalSpace` |
| Every affine scheme T → Y has quasi-compact pullback point space | `hqc : MapIsQuasiCompact f.hom.hom`; its definition quantifies over `T : Over S`, its Yoneda map, and `IsAffine T.left`, concluding `CompactSpace (Point (Limits.pullback ...))` |
| Every valuation ring A | `∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]` |
| Its fraction field K | `(K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]` |
| Maps Spec A → Y and Spec K → X over S | `s : Spec (.of A) ⟶ S`, the Yoneda maps `b` from `Over.mk s` and `a` from `Over.mk (Spec.map (algebraMap A K) ≫ s)` |
| fu equals v restricted to Spec K | The antecedent `a ≫ f.hom.hom = yoneda.map (Over.homMk (Spec.map ...) rfl) ≫ b` |
| An extension field K' | `∃ (K' : Type u) (_ : Field K') ... (e : K →+* K')`; any unital homomorphism of fields is injective |
| A valuation ring A' with fraction field K' | Existential `A'`, its commutative-ring/domain/valuation-ring instances, and `[Algebra A' K']`, `[IsFractionRing A' K']` |
| A' contains A compatibly with K ⊆ K' | Ring map `i : A →+* A'` with `Function.Injective i`; `j.left = Spec.map (.ofHom e)` and the subsequent commuting square of scheme maps identify the restrictions of `e` and `i` on A |
| A' dominates A: maximal ideal contracts to maximal ideal | `IsLocalHom i`. For valuation rings, Mathlib supplies `ValuationRing.isLocalRing`; `IsLocalRing.local_hom_TFAE` and `maximalIdeal_comap` identify exactly this condition with the specified equality of maximal ideals |
| Lift w : Spec A' → X | `∃ w : yoneda.obj (Over.mk (Spec.map (.ofHom i) ≫ s)) ⟶ X.obj.obj` |
| fw equals v composed with Spec i | First equation in the existential conclusion for `w` |
| Restriction of w to K' equals u composed with Spec e | Last equation, using the canonical generic morphism on its left and `yoneda.map j ≫ a` on its right |
| Universally closed after every algebraic-space Y' → Y | `MapIsUniversallyClosed f`, defined as `∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y), IsClosedMap (mapPoint (Limits.pullback.snd f.hom g.hom).hom)` |

`j` is not an arbitrary substitute for the field-extension map: its underlying scheme map
is required to equal `Spec.map (.ofHom e)`. Its source and target are the specified field
spectra over S. The next equation is precisely the commuting square over Spec A, so it
also fixes compatibility of the embeddings into the fraction fields. Such a `j` exists
uniquely for every ordinary extended valuation diagram. Thus its explicit slice-category
packaging adds no hypothesis or mathematical clause. Every `rfl` supplies only the defining
equality for a canonical slice morphism; no theorem or construction proof is postponed
inside a definition.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, with its full-subcategory
  morphisms and underlying sheaf/presheaf.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, the existing sheaf-pullback interface used in the
  universal-closedness definition and in proof step 1; read all three recorded declarations.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `PointRepresentative.map`, `pointImage`; its point classes and scheme map are the
  existing `Point` and `schemePointMap` of `AlgebraicSpacePointClasses`.
- `Mathlib.RingTheory.Valuation.ValuationRing`: `ValuationRing`, `ValuationRing.TFAE`.
  These give the exact fraction-field notion of the valuation-ring dependency.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, `mapPoint`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsUniversallyClosed`.
  The last two defining nodes were already landed and are added to `stmt_deps`, using
  brief-stage2 §5's authorization to add already-landed definition dependencies.
- Proof-only import `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`:
  `exists_affine_etale_cover_and_point_topology` (continuity and surjectivity in steps 2–3).
- Proof-only import `Mathlib.RingTheory.Spectrum.Prime.Topology`:
  `PrimeSpectrum.isClosed_image_of_stableUnderSpecialization` (the exact recorded Mathlib
  match of lem-sfb-affine-spectrum-specialization-stable-image-closed).

The remaining proof nodes (qc affine atlas, prescribed-field specialization probe, and
universally-closed affine tests) currently have no recorded Lean modules; hence there is
no module of those proof-only dependencies to import. The docstring retains all four
accepted DAG proof steps and names every dependency needed for stage 3.

Edge cases checked before writing: empty X gives a closed empty image after every base
change; an empty affine test has compact empty point space. Empty S creates no forbidden
nonempty test requirement. A can itself be a field. The extension K'=K, A'=A is permitted:
identity embeddings and the canonical generic map satisfy all normalizations. Neither
separatedness nor quasi-separatedness, finite type, a discrete/rank-one valuation, a
nontrivial extension, or uniqueness of the lift is imposed. The zero ring is excluded
exactly by the required domain/field conditions. All test rings and fields live in the
same arbitrary universe u as the big site (there is no smaller independent test universe).

Searches actually run with `msearch.py NN lem-sfb-space-qc-valuative-existence-closed`:

- LeanFinder: “A quasi compact morphism of algebraic spaces satisfying valuative existence
  after a dominating extension of valuation rings is universally closed”: 8 results,
  led by `AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion`; this concerns schemes
  and existence without an extension, so is not the node's general algebraic-space theorem.
- LeanSearch: “quasi compact algebraic space morphism valuative existence universally
  closed”: 8 results, the same scheme criterion and related scheme properties; no match.
- Loogle: `AlgebraicGeometry, ValuativeCriterion, UniversallyClosed`: unknown identifier
  `AlgebraicGeometry`. Retried with
  `AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion`: one result, the scheme-only
  theorem; read its source at Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:237.
- Mathlib grep: `valuative|Valuative` in `AlgebraicGeometry`: hits on scheme valuative
  criteria and Proj; no algebraic-space version.
- `rg` in `lean/WeilConjectures` for `ValuativeCriterion`, `valuative`, and the item id:
  scheme criteria in Compactification and Mathlib supplements; no item attachment.
- `rg` in `lean/Sheaf` for `ValuativeCriterion`, `Has.*Valuative`, valuative closedness,
  and quasi-compact/universally-closed definitions: existing full valuative lifting for
  individual presheaves, dense-open stacked valuations, and the exact existing qc/closed
  definitions above. None gives this theorem. The new declaration's full basename was
  also searched in Mathlib, WeilConjectures and Sheaf with no existing declaration.

No STATEMENT-DISPUTED finding or mathematical node fault.

## Second reading by NN

Reopened the node and the completed module for a separate clause-by-clause rereading.
The five original statement dependencies use their recorded interfaces. The qc hypothesis
uses affine tests of the actual pullback point space, rather than the different
quasi-compact-atlas predicate. The existence hypothesis keeps both A and K, the field
extension e, the injective local valuation-ring extension i, and all three commuting
squares. The auxiliary slice morphism j has its underlying map fixed, and its square over
Spec A enforces compatibility of the two ring embeddings. The conclusion quantifies over
all algebraic-space base changes. No generic-point identity case or empty test case is
excluded. The only elaboration repair changed the valuation-spectrum square from an
equality of slice morphisms to the identical equality of their underlying scheme maps;
this resolved inference of an intermediate slice object without changing its meaning.
The added statement dependencies point to existing landed definitions; no definition was
copied or weakened. This is the author's rereading under the dispatcher's instruction
not to start agents; the maintainer supplies the independent review.

Validation: `scompile.py NN lem-sfb-space-qc-valuative-existence-closed` compiled both the
sandbox copy and its actual library module path successfully (1.6 s each). No errors or
unexpected warnings. Only the named theorem has the stage-2 `sorry`.
