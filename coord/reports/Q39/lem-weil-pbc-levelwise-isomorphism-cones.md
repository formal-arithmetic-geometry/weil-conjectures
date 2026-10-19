## Worker report

The main module is `Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones`, declaring
`AlgebraicGeometry.Scheme.completedAdic_levelwise_isomorphism_cones`. It states the
node's three assertions as a conjunction. Its proof is `sorry`. No statement, proof
plan, dependency list or other non-Lean node field is changed. There are no new nodes.
The two prerequisite definition modules are supplied under the human's authorization
to state missing existing prerequisites in the same delivery.

Hypothesis and conclusion correspondence:

- `T : Scheme.{t}` is the scheme with small pro-etale site `T.ProEt`, with object
  universe t+1 and morphism universe t. These universes are never equated.
- `A : Type t`, `[CommRing A]`, and `d : AdicCoefficientDatum A` give precisely the
  coefficient datum. Its inherited `CompleteCoefficientDatum` has `ideal`,
  `noetherian`, `finitelyGenerated`, `quotientTorsion`, and `quotientPerfect`;
  `quotientFinite` supplies finiteness of every positive quotient as a set. No
  completeness of A, regular-sequence hypothesis, or boundedness is imposed.
- `r`, `a : Fin r → A`, `ha : Ideal.span (Set.range a) = d.ideal` specify the displayed
  generators of I, including the empty list. This is presentation data for the node's
  I=(a_1,...,a_r), not an additional restriction on the finitely generated ideal.
- `completedAdicFiniteRing T d n` is the recorded continuous-function coefficient
  sheaf for the quotient A/I^(n+1), lifted to the site's coefficient universe and
  given the discrete topology. The presheaf step is actual postcomposition by the
  quotient homomorphism; sheafification gives `completedAdicFiniteStep`.
- `completedAdicRing T d` is `limit (completedAdicRingSystem T d)`, not the constant
  sheaf of A. `CompletedAdicModules T d` is Mathlib's `SheafOfModules` over that
  ring, and `CompletedAdicTowers T d` is its inverse-sequence functor category.
  Naturals index positive levels by n ↦ n+1, a bijective reindexing preserving order.
- `completedAdicEvaluation T d n` is ordinary evaluation extended termwise by
  `Functor.mapDerivedCategory`. In the first conjunct, M,N,u and the hypothesis
  `∀ n, IsIso ((completedAdicEvaluation T d n).map u)` are exactly a tower-derived
  morphism whose evaluations are isomorphisms; `IsIso u` is the first conclusion.
- The second part of that conjunct is `IsIso (RF.map u)` for a universal total
  right derived inverse-limit pair `(RF, η)`. `RF.IsRightDerivedFunctor η` fixes
  Rlim through its comparison with ordinary strict inverse limit. Quantification
  over its realizations is a way of naming the specified derived functor without
  choosing a noncanonical triangulated cone. It imposes no condition on M,N,u and
  introduces no arbitrary comparison map or arbitrary functor as a surrogate for Rlim.
  The existence and Roos computation of such pairs belong to the node's existing
  proof dependency `prop-weil-pbc-rlim-functoriality`, which is not restated here.
- `completedAdicOrdinaryTower` is tensor with each quotient module restricted to A_T,
  with transition tensor with the actual quotient map. `completedAdicReduction` is
  its universal left derived functor with a counit invertible on K-flat models.
  `completedAdicFiniteReduction` is evaluation of that functor, hence exactly the
  derived tensor reduction read as an A_T-module, including on arbitrary morphisms.
  The quotient-valued version and its exact scalar restriction are also supplied;
  `completedAdicFiniteReduction_comparison` states the natural isomorphism between
  the two presentations without selecting any data from a mere Nonempty statement.
- `IsCompletedAdicDerivedComplete T d r a ha C` unfolds to invertibility of the
  explicitly constructed Koszul unit. The Koszul complex uses the existing exterior
  complex, its exterior power transitions, and actual scalar extension to A_T.
  The scalar map is uniquely characterized by its residues, and the degree-zero
  Koszul unit is uniquely characterized by its tensor-of-units section formula.
  The product has coordinates C tensor Q_(m+1), with the specified 1-s map.
  `mappingCone (-(1-s))` shifted by -1 has differential (dx,(1-s)x-dy) in the
  source's coordinate order. The chain-level unit is (u_C,0). The derived unit is
  its localization, transported along the localization representative isomorphism.
  The comparison theorem states independence of every representative with this unit.
- In the middle conjunct, completeness and `∀ n, IsZero (...obj C)` are the two
  hypotheses, and `IsZero C` is precisely C=0 in the derived category. Literal
  equality to a selected zero object would be inappropriate categorical equality.
- In the last conjunct C,D,u, completeness of both endpoints, and
  `∀ n, IsIso (...map u)` are exactly the hypotheses of the final assertion;
  `IsIso u` is exactly its conclusion.

Dependency declarations read and used:

- `Sheaf.Paper.CompletedAdicCoefficientDatum`: `AdicCoefficientDatum`,
  `CompletedAdicModules`, `CompletedAdicTowers`, `completedAdicEvaluation`,
  `completedAdicFiniteReduction`, and the explicit supporting constructions listed
  in that node's `lean.declarations`.
- `Sheaf.Paper.CompletedAdicIntrinsicCompletion`: `IsCompletedAdicDerivedComplete`,
  `completedAdicIntrinsicUnit`, and its supporting constructions and proof obligations.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle`, `CategoryTheory.IsDerivedLimit`, read
  from the current server source. This is the exact recorded Roos-triangle notion
  specialized to derived evaluated A_T-module towers; no new definition was written.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `finiteCoefficientPresheaf`, `finiteCoefficientRingSheaf`,
  `finiteCoefficientScalarMap`; these keep the connected-components quotient topology.
- `Sheaf.Paper.CompleteCoefficientDatum`: `CompleteCoefficientDatum`,
  `adicQuotientMap`; its constant-coefficient category is not used as the new ambient
  category. Its ring-data fields are reused rather than privately copied.
- `Sheaf.Paper.IntrinsicKoszulCompletion`: `koszulPowerSheaf`,
  `koszulPowerTransition`, `koszulSheafUnitZero`, `koszulConstantUnit`,
  `koszulConstantFunctor`; only the actual Koszul constructions are reused and
  then extended to completed coefficients, not the old constant-coefficient completion.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `derivedChangeOfRingsIndependentCoefficients` supplies ordinary scalar extension
  with its exact object/map formulas and a universal derived pair.
- Mathlib's `DerivedCategory`, `HasDerivedCategory.standard`, `Functor.mapDerivedCategory`,
  `CochainComplex.mapBifunctor`, `HomologicalComplex.mapBifunctorMap`,
  `CochainComplex.mappingCone`, categorical limits, tensor and scalar restriction.

The stated proof-dependency modules for K-flat cones, resolutions and change of rings
are imported privately in the main module. The exact-functor and triangle-isomorphism
Mathlib modules are imported. The unrecorded reconstruction and Rlim-functoriality
proof dependencies are described in the proof docstring but are not needed to type
this statement; they are not silently replaced by new hypotheses on C or u.

Edge cases checked before writing: empty scheme; zero coefficient ring; I=A (all
finite coefficients and the completion ring are zero); I=0, including r=0 (the
Koszul unit is the identity under its constant-tower identification); redundant or
zero generators; unbounded complexes; zero objects and their identity maps; first
positive level n=0, meaning exponent 1. Every quotient level is included, and no
flatness of the quotients, regularity of generators, finiteness of A itself, or
comparison with a discrete constant A_T is assumed. Category structures use Mathlib's
actual instances, not chosen abelian structures.

Searches made:

- LeanFinder via msearch: "morphism in a derived category of towers detected as
  isomorphism at every level; derived complete object with zero finite reductions
  is zero". Eight generic derived-category/resolution/vanishing hits, none this
  completed-coefficient tower statement.
- Loogle via msearch: `CategoryTheory.IsIso, CategoryTheory.Functor.mapDerivedCategory`.
  Zero hits.
- Mathlib grep via msearch: `isIso.*eval|eval.*[Ii]so|[Ll]evelwise|[Cc]omplete`, under
  `Algebra/Homology/DerivedCategory`. Four generic evaluation occurrences in
  SingleTriangle/FullyFaithful, no matching theorem.
- LeanSearch via msearch: the levelwise/derived-complete vanishing statement.
  Service unavailable: Internal Server Error. This is recorded as unavailable,
  without treating it as a completed search or inferring a negative result.
- Source/DAG/project grep for the node id, `CompletedAdic`, `completedAdic`,
  `levelwise_isomorphism_cones`, `intrinsicCompletion`, `KoszulCompletion` and
  `IsDerivedComplete`; no existing exact theorem. Older intrinsic Koszul completion
  and adic modules concern constant coefficients and are not exact matches.
- `tools/blueprint_refs.py search 'adic coefficient datum'` found the existing
  adic and intrinsic definition nodes, so those nodes were supplied rather than
  duplicated as new nodes. `dag/lean_names_upstream.json` and the upstream namespace
  search found no declaration with the chosen new names.
- Current server sources checked using `scompile.py --source`; absent guessed
  completed-adic module paths were confirmed absent. Server delivery refs were
  inspected read-only: Q02's derived-inverse-limit delivery provides the exact
  existing Roos predicate. No delivered adic-coefficient or intrinsic-completion
  construction was found.

No statement correction or mathematical dispute was found. The main theorem and
all postponed helper theorems have whole proofs `by sorry`, source/blueprint docstrings
and natural-language proof plans. Definition data are actual limits, scalar tensor
constructions, total complexes, products and cones, or choices uniquely fixed by a
normalization/universal property. All declarations are recorded in their owning nodes.

## Dependency modules

`def-weil-pbc-adic-coefficient-datum`: its Lean record is absent on the current DAG.
The older constant-coefficient datum does not define A_T or incorporate finite quotient
sets. `Sheaf.Paper.CompletedAdicCoefficientDatum` supplies the completed datum and the
strict derived tensor tower needed here, using the existing finite sheaf construction.
Its generic scalar-extension helpers retain exact tensor object/map formulas and the
universal derived comparison. The original node's non-Lean fields are unchanged.

`def-weil-pbc-intrinsic-completion`: no usable Lean record exists. The older intrinsic
Koszul completion is over constant coefficients. `Sheaf.Paper.CompletedAdicIntrinsicCompletion`
supplies the source's explicit mapping-fibre model over A_T, with the actual completion
unit and representative-independence assertion. Its residue-normalized scalar extension
reuses the existing exterior Koszul maps. The original node's non-Lean fields are unchanged.

`def-weil-pbc-derived-inverse-limit`: this is a record-only dependency repair, with
`existing: true`, using the exact published `CategoryTheory.IsDerivedLimitTriangle` and
`CategoryTheory.IsDerivedLimit` definitions. The node explicitly defines only an object
with a distinguished Roos triangle, and is this specialization without extra data.
The pending Q02 delivery was inspected and agrees with this same declaration match.
No module or duplicate declaration was added for this dependency.

The coefficient dependency also supplies `completedAdicBalance` and
`completedAdicNormalizationOnModel`: these are actual balancing chain maps fixed by
(s tensor z) tensor x ↦ s*q(z) tensor x, with their invertibility extracted from
that unique normalized witness. The generic helper retains both quotient coefficient
actions. Its formula gives naturality and the quotient cocycle (both triple products
are the same), and includes b=a. On K-flat representatives the derived counits
identify the localizations of these maps with the quotient-reduction normalizations.
Thus no bare Nonempty choice supplies a canonical map.

Validation uses only the prescribed `scompile.py` and `deliver2.py --no-push`
wrappers. An earlier three-module version passed cleanly. A later server attempt
hit temporary-overlay exhaustion (`No space left on device`); the first dry-run
attempt subsequently crashed with a missing temporary ExistingChecks.lean probe.
These are recorded tool failures, not mathematical changes; the final packet is
being retried with every file supplied together and compiled separately in order.

The latest `scompile.py` pass compiled the final three modules separately in dependency
order with no errors or warnings: coefficient datum 6.5 s, intrinsic completion 5.3 s,
main statement 1.8 s (each under the unchanged 60-second limit, two threads, nice 19).

## Second reading by Q39

I read the node `lem-weil-pbc-levelwise-isomorphism-cones`, its three statement
dependencies, the three supplied modules, and the cited Stacks places 099M, 099P,
and 099Q.  The source/node statement has one fixed completed coefficient datum, then
three assertions: levelwise isomorphisms detect an isomorphism in the derived tower
category and after derived inverse limit; a derived-complete object with all finite
reductions zero is zero; and a map between derived-complete objects is an isomorphism
when all finite reductions are isomorphisms.

Object and hypothesis matching:

* The node's scheme, coefficient datum, ideal generators, and generator equation are
  rendered by `(T : Scheme.{t})`, `{A : Type t}`, `[CommRing A]`,
  `d : AdicCoefficientDatum A`, `r : ℕ`, `a : Fin r → A`, and
  `ha : Ideal.span (Set.range a) = d.ideal`.  `AdicCoefficientDatum` inherits the
  Noetherian, finitely-generated-ideal, additive-torsion, and perfect-positive-quotient
  fields and adds finiteness of every positive quotient; no extra ring or finiteness
  hypothesis is present.
* The completed sheaf and coefficient categories in the node are exactly
  `completedAdicRing`, `CompletedAdicModules T d`, and
  `CompletedAdicTowers T d`.  The latter is `ℕᵒᵖ ⥤ CompletedAdicModules T d`, with
  level `n` denoting the positive quotient indexed by `n + 1`; this is a bijective
  reindexing of the node's `n ≥ 1` convention.
* In assertion one, `M N` and `u : M ⟶ N` range over
  `DerivedCategory (CompletedAdicTowers T d)`, and
  `∀ n, IsIso ((completedAdicEvaluation T d n).map u)` is precisely the node's
  levelwise hypothesis.  The first conclusion is `IsIso u`.  Its Rlim conclusion is
  represented by the established universal derived-pair form: every `RF` and
  comparison `η` satisfying `RF.IsRightDerivedFunctor η (...)` has
  `IsIso (RF.map u)`.  This is the project's encoding of the source's functor-free
  derived inverse limit, and does not introduce a chosen arbitrary cone or map.
* In assertion two, `C : DerivedCategory (CompletedAdicModules T d)` has the node's
  completeness predicate `IsCompletedAdicDerivedComplete T d r a ha C`, and each
  `completedAdicFiniteReduction T d n` is the derived tensor reduction regarded by
  restriction of scalars as an `A_T`-module object.  The conclusion `IsZero C` is the
  categorical zero-object formulation of `C = 0`.
* In assertion three, `C`, `D`, and `u : C ⟶ D` are in the same completed module
  derived category; both completeness hypotheses and the levelwise isomorphism
  hypothesis on `completedAdicFiniteReduction` occur, and the conclusion is exactly
  `IsIso u`.

No mismatch was found and no Lean or node statement was changed in this reading.  In
particular, there is no hidden flatness, regular-sequence, boundedness, completeness
of `A`, Noetherian scheme, characteristic, or universe-equality assumption.  The
dependency records were checked as well: the completed datum and intrinsic completion
modules provide their recorded constructions, while the derived-inverse-limit record
uses the published `CategoryTheory.IsDerivedLimitTriangle`/`IsDerivedLimit` notion;
the universal right-derived-pair encoding in the theorem is the same project convention
used by the Rlim functoriality statements.

Edge cases checked: `r = 0` (including the empty generator family), redundant or zero
generators, `I = 0`, `I = A`, the zero coefficient ring, the empty scheme, zero and
identity objects/maps, the first positive level (`n = 0`, exponent one), and unbounded
complexes.  Every case remains admitted by the binders and no quotient level is lost.

Independent searches were repeated with `rg` over Mathlib, the upstream
`WeilConjectures` sources, the shared `lean/Sheaf`, and all DAG records; with
LeanFinder/Loogle queries for levelwise derived isomorphisms and completed reductions;
and with `msearch.py` LeanSearch.  Only generic derived-category and universal-derived
functor declarations were found; no exact completed-adic levelwise-conservativity
statement exists.  The LeanSearch service again returned an internal error, recorded
as unavailable rather than as a negative result.  The current server source confirms
that `IsDerivedLimitTriangle` and `IsDerivedLimit` are the exact recorded Rlim notions.
