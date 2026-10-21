## Worker report

Statement-only delivery for sk-lem-as-properties. The unit statement, proof and proof
route are unchanged. Every theorem proof is `sorry`; every definition has actual data.
The module is Sheaf.Paper.FourierArtinSchreierProperties, with the lean-only dependency
repair Sheaf.Paper.FourierAdicCharacterOf for sk-def-as. Both files compiled separately
through scompile.py against the live library, with no errors or warnings.

Hypothesis and clause mapping:

- `F : FourierSetting.{u}` retains the primes, positive exponent, cardinality,
  arbitrary fixed finite field and algebraic closure, finite l-adic coefficient
  extension, and containment of mu_p. `fourierCoefficientStage F` and the existing
  `fourierIntegralCharacter F` retain that precise coefficient stage. No particular
  choice of nontrivial character is substituted for the given one.
- `Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar`, `hΨ : Ψ ≠ 1` express the given
  nontrivial prime-field character. Its values lie in the specified E by the published
  integral-lift construction; an E-valued character is thus represented faithfully by
  its inclusion into Qbar. `fourierIntegralTraceCharacter` is precisely composition
  with `Algebra.trace (ZMod p) k0`, with the canonical prime-field algebra. This is
  the general trace-composition declaration in def-fd-additive-character's mathlib_match,
  not its overly specific primitiveChar choice.
- `X.Over (Spec (.of F.field.k₀))`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`
  express a separated finite-type base scheme. Where realization needs `IsNoetherian X`,
  this is the inherited finite-type-over-field property, adding no mathematical
  restriction. On the affine line the actual Noetherian instances are constructed
  from `LocallyOfFiniteType.isLocallyNoetherian` and
  `QuasiCompact.compactSpace_of_compactSpace`, rather than assumed.
- `f g : Γ(X, ⊤)` are the two arbitrary global functions. No nonzero or nonconstant
  assumption is placed on either.
- `fourierPrimeCover_properties` uses the existing `artinSchreierFunctionProjection X p f`
  and `artinSchreierFunctionRoot`, hence the auxiliary cover is T^p-T=f, not T^q-T=f.
  Its first two conjuncts are finite etaleness. The specified monoid homomorphism σ
  has the coordinate formula T maps to T+a, and each geometric fibre is nonempty,
  has exactly p points, and has a unique translation taking any point to any other.
- The centralizer `Subgroup.centralizer (Set.range σ)` is exactly the automorphisms
  commuting with all translations, i.e. torsor automorphisms. Its group isomorphism
  with `LocallyConstant X (Multiplicative (ZMod p))` is Γ(X,Fp), with the additive
  group written multiplicatively for categorical automorphism groups. `ConnectedSpace`
  includes nonemptiness. Its two implications give the connected-base constant
  sections assertion and bijectivity of σ when the total cover is connected.
- `fourierPrimeCover_zero` supplies the actual root sections and their coproduct
  universal property for f=0. `fourierPrimeCover_three_aut` gives the precise S3
  counterexample over Spec F3, as the group of permutations of ZMod 3.
- `fourierPrimeCover_line` is the isomorphism over the coordinate line identifying
  its root cover with y maps to y^p-y.
- `fourierPrimeIntegralObject ... true` is the completed integral finite direct image
  in degree zero. `false` is its integral character projector image. The finite
  direct image is taken on O_E coefficients, completed through the published
  `fourierCompletedRealization`, then rationalized and included at E by
  `fourierPrimeObject`. Thus the direct image is the adic realization specified
  in the node, never discrete rational etale cohomology.
- `fourierPrimeCharacters_decomposition` gives a bilimit bicone whose point is
  isomorphic to that direct image. Its terms are the characters `Ψ.mulShift a`
  for a in Fp: a fixed nontrivial character of Fp parametrizes its full character
  group this way. Each completed integral summand is finite locally free of rank
  one, the a=0 summand is the actual common-stage unit, and f=0 makes every summand
  the unit. This includes the warning that nontrivial characters need not produce
  nonconstant sheaves.
- `fourierCharacterOf` uses the original DEGREE-q idempotent-image sheaf with the
  trace character and its actual pullback along f. `fourierCharacter_lisse_tensor_inverse`
  identifies this with the prime-degree summand; states finite local freeness of
  rank one of its integral lattice; states the tensor isomorphism for f+g;
  identifies the zero-function sheaf with the coefficient unit; and gives the
  tensor-inverse formula using -f. Rank-one integral local trivializations realize
  lissity and rank one at E and Qbar.
- `fourierCharacterWeil` gives the canonical descent Weil structure: pullback of
  the arithmetic sheaf to the geometric fibre, inverse of normalized pullback
  composition, followed by the equality that Frobenius fixes the model projection.
  No Frobenius isomorphism is supplied as an extra parameter or chosen arbitrarily.
- `fourierCharacter_closedFrobenius` quantifies over every closed point and every
  residue-field embedding into the fixed closure compatible with k0. It states
  equality of `localQbarClosedFrobeniusStalk` with scalar multiplication by
  `fourierClosedCharacterValue`, and equality with `fourierClosedPrimeValue`.
  These are respectively psi(Tr_(kappa/k0) f(u)) and Psi(Tr_(kappa/Fp) f(u)).
  The exact recorded local operator from def-weil-local-frobenius-trace is used.
- `fourierCharacter_linear_trace` states the trace function at all extension-field
  points, positive n, for every a including zero. `x.left.appTop coord` evaluated
  through ΓSpecIso is the coordinate u; the scalar is Psi(Tr_(Fq^n/Fp)(a*u)),
  equivalently psi(Tr_(Fq^n/k0)(a*u)) by the trace identity in the preceding clause.
- `fourierCharacterCohomology` is ordinary adic cohomology: shifted Hom from the
  actual common-stage coefficient unit into the actual geometric character complex,
  with its published Qbar-linear module structure. `fourierCharacter_affine_cohomology`
  states vanishing for i≠0 or a≠0 and the separate H0(unit)=Qbar and higher
  constant-coefficient vanishing. The zero-function/unit isomorphism gives the
  exceptional (i,a)=(0,0) group. The harmless ULift on Qbar places the regular
  one-dimensional vector space in the Hom-module universe.

Dependency declarations read and used:

- WeilConjectures.FourierTransform.ArtinSchreier:
  AlgebraicGeometry.Etale.artinSchreierTranslationAction, artinSchreierIdempotent,
  artinSchreierSheaf, artinSchreierSheafOf, artinSchreierSheafUpperStarIso,
  artinSchreierPushforwardIsoBiproduct and the existing tensor/inverse statements.
  The broad commutative-coefficient definition is reexported by the repaired sk-def-as.
- Sheaf.Paper.FourierSetting: WeilConjectures.FourierSetting.
- Mathlib.Algebra.Group.AddChar: AddChar.compAddMonoidHom; Mathlib.RingTheory.Trace.Defs:
  Algebra.trace; Mathlib.NumberTheory.LegendreSymbol.AddCharacter: AddChar.IsPrimitive.of_ne_one.
  Read primitiveChar's full signature as well: it makes a special choice, so it
  does not represent an arbitrary fixed Ψ. The node's mathlib_match supplies the
  required general declarations.
- Sheaf.Paper.LocalFrobeniusTrace: localQbarPullbackComposition,
  localQbarClosedFrobeniusStalk, localClosedPoint, localFrobeniusTrace.
- Sheaf.Paper.FourierAdicArtinSchreier: fourierIntegralCharacter,
  fourierIntegerPrimeInvertible, fourierCompletedRealization, fourierCoefficientStage.
- Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap:
  artinSchreierFunctionCover/Projection/Root, artinSchreierBaseConstants,
  artinSchreierFibreMap and artinSchreier_trace_cover_map.
- def-a1-common-stage-coefficient-unit, Sheaf.Paper.DerivedPullbackTensorIso:
  pullbackTensorCommonUnit;
  Sheaf.Paper.DerivedPullbackTensorHom: commonStageDerivedTensor and commonStageDerivedPullback.
- Sheaf.Paper.IntrinsicQbarCategory: intrinsicQbarLinear;
  Sheaf.Paper.WeilComplexTraceFunction: weilTraceFunction;
  Sheaf.Paper.SfWeilSheafComplex: sfWeilPrimeInvertible and sfCommonStageWeilComplex.
- Proof-dependency modules are imported, including FiniteEtaleAdicCohomology,
  IntegralPullbackComposition, FrobeniusPointTransportNatural, ArtinSchreierTrace,
  ArtinSchreierCohomology, FiniteEtaleEtaleLocalSplit and WeilFrobenius.

Edge cases checked before writing and again after compilation:

- X empty: all definitions use the given structure map; no CharP instance on its
  zero global-section ring is required. The fibre assertions quantify over existing
  geometric points, while the split-cover assertion has the empty coproduct value.
- X disconnected and f=0: full cover automorphisms may be permutations; only the
  centralizer is identified with Γ(X,Fp). The stronger full-group assertion requires
  connected total space, and ConnectedSpace retains nonemptiness.
- p=2 and p=3; q=p and q=p^r for r>1: the degree-q constructor and prime-degree cover
  remain distinct; neither q=p nor trace nonzero on 1 is assumed.
- f=0, g=-f, a=0, i=0 and positive i; nontrivial Ψ with f=0 gives a constant line.
- A point whose image f(u) has smaller degree: the local operator is the closed-point
  operator at u, not an incorrectly substituted lower-degree operator at f(u).
- Arbitrary universes u, arbitrary finite-field models and their chosen algebraic
  closures; geometric test fields have the scheme universe, not a smaller one.

Searches (all performed via the prescribed msearch.py and local read-only rg):

- leanfinder: "Artin Schreier sheaf lisse rank one tensor additive Frobenius trace
  affine line cohomology" returned eight unrelated Hilbert90, cotangent, Witt-vector
  and arithmetic-Frobenius declarations; no combined adic statement.
- loogle: "AddChar, AlgebraicGeometry.Scheme" returned zero hits.
- grep: "artinSchreier|ArtinSchreier" returned zero Mathlib hits via msearch.
- leansearch: "Artin Schreier adic character sheaf is lisse rank one and Frobenius
  acts by trace character" returned eight elementary Frobenius/finite-field character
  declarations; none stated the node.
- rg in WeilConjectures found the general ordinary-etale ArtinSchreier module,
  the genuine adic WeilSheaf.ArtinSchreierTrace, and finite-coefficient
  ArtinSchreierCohomology. Their interfaces do not jointly state this node's current
  adic common-stage degree-q sheaf and local operator.
- rg in Sheaf found FourierAdicArtinSchreier (prime-degree completion), the explicit
  trace-polynomial cover maps and the ordinary prime-character comparison. These
  are reused. No fourierCharacterOf or adic assembled properties declaration existed.

No STATEMENT-DISPUTED flag or unit-statement correction is needed.

## Dependency modules

sk-def-as: its attachment listed only four translation-action declarations. Those
are usable for the action but do not themselves supply the claimed image sheaf,
its function pullback, or its adic coefficient realization. The dependency repair
reexports the existing general upstream definitions and supplies their actual
DEGREE-q adic realization. It reuses the published integral prime-field character,
composes with trace, forms the existing degree-q idempotent image, pulls along f,
then completes and rationalizes at the specified E. Its named constructibility
proof is postponed, with full proof plan; all object data are explicit. This also
avoids the published prime-degree constructor's CharP-global-sections restriction
on the empty scheme. Only this dependency's lean record is changed.

The item cites the definition owners of the adic realization, function-cover
construction, common-stage tensor/unit interfaces, Weil-complex structures,
Qbar-linear category and trace function used in its signature. See the new-node
and returned-delivery repair sections below.

## Second reading by Q27

Self-check only: the dispatcher expressly forbids starting another agent and no
independent second worker is present. The maintainer's independent delivery review
is still required; this section does not claim that an independent review occurred.

Reopened the full node and both modules after the first successful compile. Checked
all hypotheses and clauses against the mapping above. Found and corrected an empty-X
exclusion in the candidate prime-field construction by retaining the structure-map
based degree-q construction. Kept the prime-cover full automorphism group distinct
from its centralizer; included the explicit S3 example. Replaced an oversized Fourier
transform import by the smaller pullback/unit interfaces after a published unrelated
compact-support module failed to build. Added the all-a extension-point trace formula;
removed an unnecessary affine-line Noetherian hypothesis by supplying its inherited
instance. Explicit module and field universes were checked by the compiler. All
auxiliary Prop instances are actual inherited structures, with no inline sorry.
The only postponed facts are named theorems corresponding to clauses or realization
properties of their owning DAG nodes, and each has its source and proof plan.

## New nodes

def-fd-artin-schreier-function-cover owns the five exact existing definitions
artinSchreierFunctionCover, artinSchreierFunctionProjection, artinSchreierFunctionRoot,
artinSchreierBaseConstants and artinSchreierFibreMap in
Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap. It defines the chosen pullback
of t^n-t along f, its projection and root, base constants from the supplied structure
morphism, and the functorial fibre map of a morphism over the base. Its source is
the unit's auxiliary cover in the first paragraph, with the existing explicit
construction following Laumon (1.1.3) and Stacks 01LX. The existing module is reused
unchanged (existing:true); no Lean declaration is introduced or duplicated.

Executed searches: LeanSearch for the function-cover/root/fibre-map construction
returned eight general scheme-fibre and scheme-cover pullback declarations; Loogle
for AlgebraicGeometry.AffineSpace and CategoryTheory.Limits.pullback returned only
AffineSpace.over_over; Mathlib grep for the four Artin–Schreier name stems returned
zero hits. Read-only rg of DAG/source/Sheaf found no definition owner, no exact
WeilConjectures construction, and exactly the existing ArtinSchreierTraceCoverMap
construction and its ArtinSchreierPrimeCharacterComparison consumer. Blueprint_refs
search Artin.Schreier.*cover returned zero blueprint nodes. The precise tool records
are retained verbatim in mathlib_searches. Checked empty X, arbitrary n (including
0 and 1), the zero function, and arbitrary base-change test schemes: the definitions
remain meaningful without claiming finiteness or etaleness outside their prime cases.

## Returned-delivery repair: L H2 at 155fabd72c24

Compared the retained packet with the current shared node records and the return's
specified declaration ownership. The initial saved-packet dry run passed as commit
a123864a46d; this established compilation and mechanical preflight only. The
independent return identifies ownership defects that still required repair.

1. Replaced the theorem lem-a1-artin-schreier-trace-cover-map in the item's added
   stmt_deps with def-fd-artin-schreier-function-cover, owning all five plain defs
   actually used in the statement. The theorem is retained in the original
   proof_deps and its module remains imported. No cover data is chosen from it.
2. Replaced lem-pur-derived-pullback-tensor-iso in the item's added stmt_deps with
   the already landed def-a1-common-stage-coefficient-unit. Its exact declaration
   is WeilConjectures.pullbackTensorCommonUnit, used for the unit and cohomology.
3. Added def-weil-derived-pullback-tensor-hom, owning commonStageDerivedTensor and
   commonStageDerivedPullback, and def-weil-weil-sheaf-complex, owning
   sfWeilPrimeInvertible and sfCommonStageWeilComplex. Read their current signatures,
   docstrings and node records. Their modules are already supplied by the imports.

All existing Lean files, their theorem signatures, and the sk-def-as lean-only
repair are retained. The unit's natural-language statement and original proof route
are unchanged. The two abstract group-isomorphism clauses mentioned in the advisory
are retained as reviewed; the explicit translation coordinate formula and torsor
simple transitivity remain in the same theorem. No new mathematical assumption is
added. The second-reading section remains expressly a self-check, as required by
the dispatcher's prohibition on starting another agent; independent review is the
maintainer's delivery review.

Repair self-check: reopened the unit, item node, both delivered modules and the
five existing cover definitions. Matched the new node's pullback, second projection,
pulled-back root, constants, and fibre map clause by clause to those five definitions.
Confirmed that the new node is in sec-fourier-transform, has only the prescribed
fields, cites each construction dependency, and has no theorem proof dependency.
Verified that the item now cites definition owners for each returned H2 occurrence,
that the trace-cover theorem remains in proof_deps, and that no current-main field
other than the authorized lean and added stmt_deps is changed on existing nodes.

Final preflight repair: because the item is itself a blueprint unit, the server
requires blueprint.from.via = [] for its new definition node. Updated that
provenance field to the exact preflight diagnostic; its ancestor remains the item.
Both delivered Lean files passed explicit scompile.py with no diagnostics
(7.6 and 14.5 seconds for their library checks).
