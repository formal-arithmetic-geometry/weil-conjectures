## Worker report

This repairs the independent review of f9df200ab151. The saved packet passed its
initial dry run (bfea439d11), but the required semantic self-check confirmed that
the returned defects remained. This delivery changes the Lean implementation;
the source statement is retained verbatim. The current shared node differs from
the saved node only in `lean`; its current non-Lean fields are retained.

Hypotheses and objects:

- `X X' : Scheme.{u}`, `g : X' ⟶ X`, and `A : CommRingCat.{u+1}` are used throughout.
  `etaleHomRing X A` is the constant commutative ring sheaf on
  `X.smallEtaleTopology`. `EtaleHomModule X A` is precisely its module category.
  The site has object universe u+1 and morphism universe u; module sections and
  coefficients have universe u+1. Thus `homComplex`'s output universe
  `max (u+1) u (u+1)` is u+1. No universe equality is imposed.
- `etaleHomRingMap g A` extracts the canonical constant-ring map gamma from
  `etaleConstantRingInverseImageComparison`, the normalization lemma used
  in `AlgebraicGeometry.etaleInverseImageModulesExact X' X g A`.
  Equality of the constant-section formulas identifies their ring maps.
  `etaleHomPullback g A` is Mathlib module pullback along this exact ring map,
  canonically identified with the dependency's LM by uniqueness of left
  adjoints. `etaleHomPushforward_isRightAdjoint` exposes that adjunction
  existence at the actual site universes, avoiding the native presheaf API's
  same-universe instance restriction. Additivity is the named transported-property lemma; the adjunction
  is `SheafOfModules.pullbackPushforwardAdjunction`. The dependency identifies
  LM with ringed-topos module pullback,
  specifies its scalar action and underlying abelian inverse image, proves its
  exactness, and fixes its unit and counit. `etaleHomUnit` uses that unit.
- `E I : EtaleHomComplex X A` are arbitrary unbounded integer cochain complexes.
  Termwise pullback is the existing `mapHomologicalComplex (ComplexShape.up ℤ)`.
  There are no flatness, injectivity, boundedness, finiteness, or product
  preservation hypotheses.

Clauses and canonical data:

- `homComplex` and `homComplexFunctor` are the dependency's existing product
  Hom complex and bifunctor. `homProjection` exposes its published projections
  via `homComplex_projections_exists`; no Hom complex is redefined.
- The tensor is `siteSheafTensorRight`, and its local tensor sections are
  `siteSheafTensorTmul`, both from the recorded tensor dependency.
  `etaleHomTensorEquiv_exists` exposes the tensor-closed adjunction at the
  actual site universes, incorporating symmetry by taking parameter first and
  argument second. Its equation on every local pure tensor uniquely fixes the
  equivalence. `etaleHomEval` is its inverse applied to the identity.
- `etaleHomTensorPullback_exists` exposes the canonical 03EL tensor comparison
  at these universes. Its unit/pure-tensor equation uniquely fixes the
  isomorphism. This supplies the missing comparison interface of
  `module_pullback_tensor_iso`, without equating site Hom and object universes.
- `etaleHomPullbackComparison` defines q by applying that canonical transpose
  to the inverse tensor comparison followed by F(evaluation). There is no free
  q parameter. `homComplexPullbackComparison_exists` states unique existence
  for this q alone, so the selected chain map has determined data.
- The first conjunct of `etaleHomComplexPullback` is the formula in every
  degree n and every factor p, with q and `hpq : p+n=q` making all degree
  transports explicit. It directly displays the transpose of the inverse
  tensor comparison followed by F(`etaleHomDegreeEval E I n p q hpq`),
  exactly F(ev_{n,p}). The assembly lemma uses the equivalent F(projection)
  followed by canonical q; tensor comparison naturality identifies these.
- The second conjunct quantifies over both chain maps a and b. The existing
  bifunctor maps a contravariantly and b covariantly, on X and X', giving the
  entire naturality square with the actual pullback functor.
- `etaleHomSourceShift_exists` fixes the isomorphism s, in the statement's
  orientation, by its degree-n, p-component `(-1)^(m*n)` times projection at
  p-m. `XIsoOfEq` explicitly identifies E^(p-m+m) with E^p. The same definition
  on X' supplies s'. The final conjunct is the equality of chain maps
  c(E[m],I), transport of F(E[m]) to (FE)[m], then s', versus F(s), the
  canonical shift transport on FH, then c[-m]. Both transports use
  `mapCochainComplexShiftIso`. It is not a bare existence of an isomorphism.

`etaleHomBaseChange_continuous` is the existing continuity instance with
`smallEtaleTopology` unfolded; it supplies the exact topology name required by
the native module-pullback API, rather than assuming a new geometric hypothesis.

The normalization/assembly lemmas are helpers for this node's own construction,
listed in `lean.declarations`; they are not independent notions or replacements
for dependency definitions. They have named postponed proofs and complete
source/proof docstrings, as allowed by the missing-helper rule. The tensor and
Hom constructions themselves are the recorded definitions. Every selection of
new comparison data is from an existence-and-uniqueness theorem with a local
normalization; no bare `Nonempty` comparison is selected.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.EtaleConstantRingInverseImageComparison`:
  `AlgebraicGeometry.etaleConstantRingInverseImageComparison`, the normalized
  constant-ring map used in the inverse-image proposition.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, full witness package.
- `Sheaf.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `CategoryTheory.homComplexFunctor`; `Sheaf.Algebra.Homology.HomComplexProjections`:
  `CategoryTheory.homComplex_projections_exists`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `SheafOfModules.homObjMap`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `SheafOfModules.siteSheafTensorRight`, `SheafOfModules.siteSheafTensorTmul`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`:
  `SheafOfModules.module_pullback_tensor_iso`; and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`:
  `SheafOfModules.tensorClosed`. Their same-universe comparison interfaces
  motivate the evaluation-normalized helpers above, retaining their notions.
- `Mathlib.Algebra.Homology.HomotopyCategory.Shift`:
  cochain shifts and `CategoryTheory.Functor.mapCochainComplexShiftIso`.
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` supplies the recorded
  abstract-derived-category dependency; this result is at the ordinary complex level.
- `def-weil-size-convention` is a recorded metatheoretic convention, rendered by
  the explicit universes rather than by introducing a second size object.

Edge cases checked: empty schemes; zero ring and zero complexes; identity g;
source shift m=0, positive and negative m; negative n and p; characteristic two.
All formulas use integer `negOnePow` and real index transports. At m=0 the shift
has sign 1. In characteristic two the sign disappears consistently. Pullback
only maps into the target product; neither c nor F of products is asserted invertible.

Searches: `msearch.py leanfinder` with "canonical pullback map of sheaf Hom
complexes commutes with signed source shift" found generic sheaf pullback
naturality and composition lemmas, not this comparison. `msearch.py loogle`
with "SheafOfModules.homObj, CochainComplex" found no indexed declaration
(the project name is not in its index). `msearch.py grep` with
"homComplex.*[Pp]ullback|[Pp]ullback.*homComplex" found no Mathlib match.
Reading/rg of the source's internal Hom, monoidal closed and cochain shift
files located the component constructions and showed the old closed API's
same-universe restriction. Searches in `lean/Sheaf` found the existing
independent-universe tensor, projection and shift interfaces, which are reused
or exposed with canonical normalizations. No statement correction or dispute.

## Second reading by Q43

The dispatcher prohibits subagents; this is the required final self-check,
with the node and revised file open. The returned free C,J,R,F,q interface
has been removed. X,X',g,A now determine both sites, rings, the functor and its
unit; there is no unused exactness hypothesis. q is evaluation-transposed,
with a uniquely normalized tensor comparison. The former false existence
claim for arbitrary q has become the genuine unique chain assembly for this
canonical q. The former bare `Nonempty` shift clause is replaced by defined s
and s', their exact signed component specification, and the whole transported
chain-map equation. The max-universe issue is resolved by explicit site
universes, not an extra equality. No node clause has been dropped, and the
node's statement and non-Lean fields have not changed.

Validation: `scompile.py Q43 lem-sf-etale-hom-complex-pullback` completed
with no errors or warnings: sandbox module 28.8 s, library module 31.5 s.
The earlier timeout was resolved by the explicit right-adjoint interface
at the actual site universes and the smaller normalized ring-map extraction.
