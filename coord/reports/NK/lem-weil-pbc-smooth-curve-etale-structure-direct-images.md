## Worker report

The module states `AlgebraicGeometry.Etale.smooth_curve_etale_structure_direct_images`.
Its only postponed theorem is that declaration, with whole proof `sorry` and a six-step
proof docstring following the node. Four helpers specify local coefficients and the
natural scalar action; they construct their actual data and contain no postponed proofs.
There are no new DAG nodes and no dependency-interface replacements.

Source read: Stacks `curves.tex`, `lemma-genus-in-nodal-family-of-curves`, Tag 0GKA,
lines 5018–5061, assertions (a),(b) and their proof; `etale-cohomology.tex`,
`theorem-zariski-fpqc-quasi-coherent`, Tag 03P2, lines 2280–2308 and the start of its proof.
The first source allows nodal curves; the node requests the smooth specialization and
only the first two conclusions. No universal base-change clause or higher vanishing
clause is added to the signature.

Hypotheses, matched individually:

- Schemes X,S: `{X S : Scheme.{u}}`, with no field or reducedness assumption.
- Noetherian S in the node's specified sense: `[CompactSpace S]` and
  `[IsLocallyNoetherian S]`. CompactSpace means quasi-compact here, without Hausdorffness.
- The named morphism: `(f : X ⟶ S)`.
- Properness: `[IsProper f]`. Mathlib's universally closed condition supplies
  quasi-compactness, so its locally finite type convention is the node's finite type.
- Smoothness: `[Smooth f]`, the recorded definition.
- Nonempty geometrically connected fibres: `[GeometricallyConnected f]`. The recorded
  class uses ConnectedSpace on every geometric base change, including nonemptiness;
  Mathlib's fibre instance and its Surjective instance were read. It does not merely
  assert preconnectedness.
- Every fibre has dimension one: `hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1`.
  This is the whole fibre's Krull dimension as requested, not an extra equidimensionality
  hypothesis. Smooth proper geometrically connected curves satisfy the source convention.

Conclusions and coefficient conventions, matched individually:

- The structure sheaves are `X.etaleAdditiveSheaf` and `S.etaleAdditiveSheaf`: exactly
  ULift of the additive section groups of the existing etaleStructurePresheaf, with
  structural pullback restrictions. This is the associated structure module expressed
  in actual function coordinates, rather than a second structure-sheaf definition.
- All abelian coefficient categories are `AddCommGrpCat.{u + 1}`, exactly the category
  required by the recorded direct-image and Artin–Schreier interfaces. No equality of
  site object and morphism universes is imposed. `curveLocalFunction` returns
  `ULift.{u + 1} Γ(T.left, ⊤)`; both multiplication and the final scalar equation use
  ULift.up/down explicitly. The statement chooses the lift actually required by those
  interfaces; it makes no comparison of untransported cohomology groups across universes.
- The natural map is `Scheme.etaleAdditiveSheafToLowerStar f`, not an arbitrary arrow.
  Its component is pullback along `V ×_S X → V`. `IsIso` asserts exactly the first
  conclusion. Since the function-pullback map is ring-linear, its inverse is module-linear.
- `∃ (E : S.Modules) (_ : E.IsFiniteLocallyFree)` gives the Zariski module with variable
  finite local rank. The following quasi-coherence witness is used to form its recorded
  associated etale sheaf; it adds no condition beyond finite local freeness.
- The source of `e` is degree-one homology of `rightDerivedLowerStarPlus` on the
  degree-zero single of `X.etaleAdditiveSheaf`. Thus this is the recorded **abelian**
  derived direct image, not a replacement by derived O-module pushforward.
- The target of `e` is `Scheme.Modules.liftedCoherentEtaleSheaf E`, the existing
  `etaleTensorSectionsSheaf E` followed by the same sectionwise additive ULift.
- Module-linearity is specified explicitly, rather than dropping to an unqualified
  additive isomorphism. For every etale U over S and a in Γ(U,O), the conclusion supplies
  a local coefficient endomorphism μ. `IsCurveLocalScalar` prescribes its value on EVERY
  etale T over U×_S X and EVERY coefficient section: in the canonical localization
  coordinates, multiply the function by `(T.hom ≫ pullback.fst U.hom f).appTop a`.
  These formulas uniquely determine μ, and its existence is a conclusion, not an
  assumed arbitrary map or a potentially vacuous universally quantified witness.
- `curveLocalCohomologyMap` is the actual functorial map obtained from μ by the
  single-complex functor, localization Q and abelian etale cohomology. The final equation
  says that `e` carries its action to `a • s` on tensor sections of E (with ULift).
  `rawRestrictedCohomologyComparison` is invertible, so every local cohomology class
  is covered by the quantified raw classes z,z'. `abelianHigherDirectImageClass` is the
  actual derived-adjunction comparison into R¹, not an isomorphism chosen from Nonempty.
  These classes locally generate R¹ by Tag 03Q8. Thus the equation is equivalent to
  linearity for its natural scalar action, on every object and every local base function.
  The assertion includes exactly the module isomorphism requested by the node.

The helpers belong to this scalar specification: `curveLocalStructure` reuses inverse
image; `curveLocalFunction` reuses the canonical localization isomorphism;
`IsCurveLocalScalar` gives the sectionwise multiplication formula;
`curveLocalCohomologyMap` applies existing cohomology functors. No independent notion,
second sheaf construction, free-standing postponed theorem, or scalar action chosen
from an unconstrained existence statement is introduced.

Dependency declarations used (the recorded declarations and full docstrings/signatures
were read; the geometric definitions were read in the pinned Mathlib source):

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`; `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`; `AlgebraicGeometry.IsProper`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; `AlgebraicGeometry.Smooth`.
- `def-pc-geometrically-irreducible`: `Mathlib`; `AlgebraicGeometry.GeometricallyIrreducible`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`; `topologicalKrullDim`.
- `def-sc-etale-qcoherent-module`: `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`; `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf`.
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; `AlgebraicGeometry.Etale.lowerStar`.
- `def-sc-etale-additive-structure-restriction`: `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf`; `AlgebraicGeometry.Scheme.etaleAdditiveSheafToLowerStar`.
- `def-sc-finite-locally-free-sheaf`: `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`; `SheafOfModules.IsFiniteLocallyFree`.
- `def-sbc-raw-affine-restricted-cohomology`: `Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomology`; `AlgebraicGeometry.Etale.rawAffineRestrictedCohomology`.
- `def-sbc-raw-restricted-cohomology-comparison-map`: `Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap`; `AlgebraicGeometry.Etale.rawRestrictedCohomologyComparison`.
- `lem-sbc-abelian-higher-direct-image-class-compatibility`: `Sheaf.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility`; `AlgebraicGeometry.Etale.abelianHigherDirectImageClass_pullback`.
- `lem-sbc-abelian-higher-direct-image-natural-comparison`: `Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison`; `AlgebraicGeometry.Etale.exists_abelianHigherDirectImage_natural_comparison`.
- `def-pbc-canonical-coherent-etale-comparison`: `Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison`; `AlgebraicGeometry.Scheme.Modules.canonicalCoherentEtaleComparison`.

From those modules the signature additionally uses the recorded helpers
`liftedCoherentEtaleSheaf`, `etaleAdditiveSheaf`,
`abelianHigherDirectImageRawPresheaf`, and `abelianHigherDirectImageClass`.
Proof-dependency modules already stated are imported without `public`; statement
constructions are public imports. The added statement dependencies are already recorded
nodes; none is duplicated or changed. `def-sc-etale-qcoherent-module` is used through
its exact lifted sheaf, not through the proper-over-field specialization of a comparison.

Edge cases checked mathematically:

- Empty S: no fibre or dimension condition is imposed on an absent point. U and its
  pullbacks are empty; all section and cohomology groups vanish. E may have rank zero.
- Genus zero: E is the zero module; no positive rank is required.
- Disconnected S: IsFiniteLocallyFree allows different local ranks on different pieces.
- Nonreduced Noetherian S: no reducedness hypothesis was inserted.
- Every characteristic, including characteristic zero and residue characteristics
  varying on S: the statement contains no prime/characteristic restriction.
- Nonaffine etale U and all local coefficient sections: the scalar specification
  quantifies over them as well as affines; no global-function-only weakening occurs.
- Site/coefficients: schemes have universe u; coefficients and sheaf morphisms use the
  required u+1. The common lift transports all scalars; it does not identify two
  cohomology groups just because their unlifted carriers look alike.

Searches actually run:

- msearch leansearch, query `smooth proper curves first higher direct image structure
  sheaf locally free`: service unavailable (HTTP Internal Server Error), not no match.
- msearch leanfinder, query `proper smooth geometrically connected curve structure sheaf
  first higher direct image finite locally free`: eight hits including
  `finite_appTop_of_universallyClosed`, `Hom.normalizationDiagram`, and `Hom.finite_app`;
  none is this family-cohomology assertion.
- msearch loogle, query `AlgebraicGeometry.Etale.lowerStar`: no hits, unknown identifier
  in the Mathlib index; the project definition was read directly and reused.
- msearch grep, query `structureSheaf|structureModule|FiniteLocallyFree` in
  AlgebraicGeometry: hits on structure-sheaf constructions and unrelated geometry;
  no smooth proper curve direct-image theorem.
- rg of upstream WeilConjectures and lean/Sheaf for the item id and the proposed names
  `smooth_curve_etale_structure_direct_images|curveLocalStructure|IsCurveLocalScalar`:
  no existing declaration before this delivery.
- rg for `structureSheaf|structureModule|FiniteLocallyFree|finiteLocallyFree` found the
  existing locally-free sheaf API, which is reused. DAG searches identified the existing
  finite-locally-free-sheaf, additive-structure-restriction, raw comparison and canonical
  coherent comparison nodes; their recorded source declarations were then read.

No statement correction and no STATEMENT-DISPUTED issue is asserted.

Validation: scompile.py completed successfully on 2026-10-15. The delivered module
compiled in 6.6 seconds, nice 19, two threads, limit 60 seconds, with no errors or
warnings. The first compiler pass diagnosed two missing type annotations and a
public-import visibility issue; the final signature uses explicit identity casts for
function rings and tensor-section modules and imports the derived direct-image API.
No mathematical hypothesis or conclusion changed in these elaboration repairs.
No local Lean command or library build was invoked.

Delivery dry run: `deliver2.py NK lem-weil-pbc-smooth-curve-etale-structure-direct-images
--no-push` printed OK for temporary commit `85fcba413c`: the module compiles and all
preflight checks pass except the intentionally absent independent second reading.
Nothing was pushed. The first dry run stopped on a transient server connection closure
during git fetch; retrying the unchanged delivery succeeded.


## Second reading by NK

Independent second reader, 2026-10-15. Read the node and its six proof steps,
the complete delivered Lean module, every statement-dependency node and its recorded
interface, and the actual constructions used by the signature. Read Stacks curves.tex,
lemma-genus-in-nodal-family-of-curves (0GKA), assumptions, conclusions and proof,
and etale-cohomology.tex, theorem-zariski-fpqc-quasi-coherent (03P2), including its
objectwise formulation at the start of the proof. The node deliberately requests
only the smooth specialization of (a),(b), over Noetherian bases. It does not request
the source's arbitrary-base-change and higher-vanishing conclusions. No source-wide
extra field, characteristic, reducedness or nonemptiness of the base is assumed.

Object/hypothesis/conclusion inventory, matched to Lean:

- Objects X,S are arbitrary schemes: `{X S : Scheme.{u}}`. Verdict: exact;
  the common scheme universe is the recorded category's convention, not a restriction
  relating the site object universe to its morphism universe.
- S is quasi-compact and locally Noetherian: `[CompactSpace S]` and
  `[IsLocallyNoetherian S]`. Read Mathlib Noetherian.lean's every-affine-open class.
  Verdict: the node's stated meaning of Noetherian; no Hausdorffness is required.
- Named morphism f:X to S: `(f : X ⟶ S)`. Verdict: exact.
- f proper: `[IsProper f]`. Read Proper.lean; it extends separated,
  universally closed and locally finite type. Universal closedness gives quasi-compactness,
  recovering finite type as in the dependency record. Verdict: exact.
- f smooth: `[Smooth f]`. Read Smooth.lean's smooth affine ring-map definition.
  This is the recorded smooth notion, equivalent to the source's convention. Verdict: exact.
- Fibres nonempty and geometrically connected: `[GeometricallyConnected f]`.
  Read Connected.lean: all field-valued base changes have `ConnectedSpace`, not merely
  `PreconnectedSpace`; the fibre instance and surjectivity instance explicitly confirm
  nonemptiness. Verdict: exact. The broad geometric-properties dependency records this
  connected variant alongside its primary irreducibility declaration; no irreducibility
  assumption was substituted.
- Every fibre dimension one: `hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1`.
  Read topologicalKrullDim's chain definition with codomain `WithBot ℕ∞`.
  Verdict: the whole-fibre dimension in the node. For smooth connected fibres the
  locally constant relative dimension is constant on each fibre; this agrees with
  the source's relative-dimension-one specialization.
- Structure coefficients: `X.etaleAdditiveSheaf`, `S.etaleAdditiveSheaf`.
  Read EtaleAdditiveStructureSheaf.lean: actual etale function rings, forgotten to
  additive groups and lifted by `AddCommGrpCat.uliftFunctor.{u+1,u}`; restrictions
  are function pullbacks. Verdict: exact lifted structure coefficients, no second
  structure-sheaf definition and no field-only specialization.
- Natural degree-zero map is invertible: `IsIso
  (Scheme.etaleAdditiveSheafToLowerStar f)`. Read its actual whiskered structural
  pullback formula. Verdict: canonical map, not an existential arrow. It respects
  multiplication by base functions, so invertibility on additive sheaves is precisely
  the asserted structure-module isomorphism.
- Finite locally free Zariski module: `∃ (E : S.Modules)
  (_ : E.IsFiniteLocallyFree) (_ : E.IsQuasicoherent) ...`.
  Read LocallyFree.lean's local generator definition: the finite number of generators
  varies with the cover member. Verdict: exact variable rank, including zero.
  Quasi-coherence follows from finite local freeness; its witness only permits forming
  the dependency's associated etale sheaf and imposes no extra hypothesis on f.
- R1 is computed in abelian sheaves: source of `e` is degree-one homology of
  `rightDerivedLowerStarPlus` on `Plus.singleFunctor ... 0` of X's additive structure
  sheaf. Read the actual lowerStar definition and its rightDerivedFunctorPlus alias.
  Verdict: exact abelian higher image; no derived ringed-module substitute.
- Target of `e` is `Scheme.Modules.liftedCoherentEtaleSheaf E`. Read the abbreviation
  in CanonicalCoherentEtaleComparison.lean and etaleTensorSectionsSheaf's definition.
  It is the recorded tensor-section sheaf followed by the same additive universe lift.
  Verdict: exact E_et. This abbreviation has no field/properness requirement even
  though other declarations in its owning module concern proper schemes over fields.
- The isomorphism is linear for the natural local scalars: the remaining quantifiers
  run over every `U : S.Etale` and every `a : Γ(U.left, ⊤)`, then assert existence of
  μ with `IsCurveLocalScalar f U a μ`. That predicate prescribes μ on every etale
  T over U times_S X and every section, by multiplication by the structural pullback
  of a. `curveLocalFunction` uses the genuine localization isomorphism, which is
  componentwise invertible, so μ is uniquely determined. Verdict: canonical scalar
  multiplication, not an arbitrary action and not a vacuous universal condition.
- Linearity on higher-image classes: all raw `z,z'` satisfying the displayed
  `rawRestrictedCohomologyComparison` equation are carried by `e.hom` to multiplication
  by a on E's tensor sections. Read RawAffineRestrictedCohomology,
  RawRestrictedCohomologyComparisonMap and the actual derived-adjunction formula for
  `abelianHigherDirectImageClass`. Also read the existing comparison-is-iso and
  natural-comparison modules: the raw comparison is invertible on every U, and the
  canonical class map sheafifies to an isomorphism. Thus z' exists for every z and
  scalar, and raw classes locally generate R1. The equation forces linearity on
  every local section by sheaf locality; conversely natural module-linearity gives
  this equation. Verdict: equivalent to the node's module-isomorphism conclusion,
  with the same order E, e, then all local scalars. No extra base-change clause.

Edge cases: empty S satisfies the fibre condition vacuously and admits the zero E;
empty X over nonempty S fails the required nonempty-fibre condition, as it should.
Genus zero and rank zero are allowed; disconnected S permits variable rank.
Nonreduced bases and every characteristic remain covered. Empty etale test objects
and nonaffine etale test objects are included. There is no index-set binder, no
positive-genus hypothesis and no n-dependent restriction; the requested cohomology
degree is exactly one and the degree-zero clause is separate. All scheme universes
are bound by u; coefficient categories and both sheaf lifts consistently use u+1.
No independent small test universe or site-universe equality is imposed.

Independent searches: leanfinder query "For a smooth proper family of connected
curves, R1 of the sheaf of regular functions is a vector bundle" returned eight
unrelated hits (affine space, differential-topological vector bundles and smooth
relative-dimension charts), none the family-cohomology assertion. Loogle query
`SheafOfModules.IsFiniteLocallyFree` returned unknown identifier in its Mathlib index;
the existing upstream definition was read directly and reused. LeanSearch query
"The structure sheaf of a proper smooth relative curve has locally free first higher
direct image" returned service unavailable, not a negative search result.
Independent rg searches in Mathlib AlgebraicGeometry, upstream WeilConjectures and
lean/Sheaf for combinations of genus/smooth curve with direct image/cohomology/locally
free found projective-curve cohomology over fields, constant-coefficient curve
cohomology and relative Cartier divisor results, none this family theorem. Searches
for the item id and helper names in upstream declarations, upstream source and
project Lean found no preexisting declaration of this theorem or its scalar helpers.
Existing function sheaves, tensor-section sheaves, inverse image, direct image,
localization and raw cohomology constructions are reused rather than duplicated.

No mathematical mismatch found; no Lean or node change was needed. The four helpers
have real data and are recorded in lean.declarations; their docstrings carry sources
and the item's blueprint id. No new definition nodes or dependency modules are
present, so no H12/H13 additions need review. The sole postponed theorem has whole
proof `sorry` and the six-step source proof in its docstring. No file-local notation,
private definition, extra theorem proof, hidden let/show binder or unbound universe
occurs. A direct textual check confirms lean.statement equals the file signature
verbatim, and every Lean line has at most 100 characters. No statement_change exists
or is required, and no unit statement is changed.

Second-reader validation: the prescribed scompile.py wrapper succeeded, exit 0;
the delivered file compiled in 6.5 seconds with nice 19, two threads and the
60-second limit. No errors or warnings. The wrapper also compiled its required
side dependencies. An initial invocation from the read-only clone could not find
the sandbox-relative file; rerunning from the sandbox succeeded without edits.
