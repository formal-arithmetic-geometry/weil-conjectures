## Worker report

Item: lem-sfb-flag-line-equivariant-serre-pairing. Group Q02, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.GroupScheme.FlagLineEquivariantSerrePairing`.
Main declaration: `AlgebraicGeometry.FlagSerre.flagLine_equivariant_serre_pairing`.
Only the main theorem is postponed, with `sorry`. Every helper has actual data or is a
predicate spelling out the normalization of a construction in this same statement.
No statement correction, new DAG node, dependency repair, or disputed statement.

Sources read: Stacks `duality.tex`, lemma-duality-proper-over-field, Tag 0FVV,
parts (6),(7); lemma-duality-proper-over-field-perfect, Tag 0FVY;
remark-rework-duality-locally-free-CM; the current node's six proof steps and its
stage-1 review. The canonical-character specialization is the one described by
Andersen Lemma 4 p.58 in the node. That article is still WANTED locally; I do not
claim to have opened it. I read the latest blueprint's six-functor stability unit;
this auxiliary node has no blueprint ancestor of its own, as its existing metadata says.
The proof docstring preserves each of the six accepted steps and names their inputs.

Hypothesis-by-hypothesis reading:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  Positive characteristic is `(pchar : ℕ) [CharP F pchar] (hpchar : 0 < pchar)`;
  neither characteristic two nor any positive prime is excluded.
- `S : Grp (Over (Spec (.of F)))` is the actual group scheme. `hS` is the recorded
  `IsSemisimpleGroupScheme`, including smoothness, connectedness, affineness and
  finite type. `hsc` is precisely the central-isogeny criterion used by the recorded
  `exists_rho_section_modules`, including arbitrary algebra-valued centrality and
  finite scheme-theoretic kernel. It is not a condition only on rational points.
- `T,B,iT,iB,j,hpair` use the recorded `IsRhoBorelPair`: maximal torus, splitness,
  Borel subgroup and commuting inclusion triangle. `Bm,iBm,jm,hpairm` specify the
  opposite Borel containing that same torus. `haB,haBm` pin the tangent actions
  to conjugation. `Φ,hΦ,hpos` enumerate each nonzero positive tangent character
  exactly once. `hneg` says precisely that the nonzero weights of Bm are the
  inverses of those positive characters, so this is the required opposite Borel.
- `N` is written explicitly as `Φ.length`. `ρ,hρ` say that twice rho is the
  sum of the positive characters, using multiplication of actual character maps.
  This avoids dividing by two in F. `pr,hpr,hprU` specify the torus projection:
  it is the identity on T and kills every connected normal unipotent subgroup.
  The recorded `SolvableGroupStructure.IsUnipotent` already includes smoothness.
  Thus this uses the existing radical-splitting interface without a new notion.
- `Q,π,hQ,hQft,hπflat,hπsurj,hπinv,hπtorsor` introduce the proper finite-type
  flag quotient and its faithfully flat right-Bm torsor and exact kernel-pair
  square. These are the quotient data supplied by the Borel-pair theorem,
  rather than a different choice of flag scheme. The statement is independent
  of which representative of this quotient is used.
- `P` is the family of the existing `AssociatedCharacterLineBundle.Presentation`
  for the actual extended character `pr ≫ y`. Its exact all-scheme orbit
  relation is `(g,z)b=(gb,y(b)⁻¹z)`, its pullback trivialization is specified,
  and its geometric left action is `[g,z] ↦ [sg,z]`. The recorded existence theorem
  supplies these data. Quantifying over their presentations makes the result
  independent of choices; it does not replace the line by an arbitrary sheaf.

Clause-by-clause reading:

- `w.hom.hom = (ρ.hom.hom ^ 2)⁻¹` specifies -2rho as an actual character. The
  equivalence `e` identifies `exteriorSheaf Q.hom.relativeDifferentials Φ.length`
  with `(P w).L`. The differential sheaf is the existing universal-derivation
  construction, and the exterior power is the existing sheafification of local
  exterior powers, not a newly supplied canonical sheaf.
- `D` is a linearization in the existing sense on every test scheme.
  `IsPresentationLinearization` pins it to the presentation's geometric action
  using the natural representing equivalence for sections on every base scheme.
  `Dω` and `IsCanonicalLineLinearization` pin the action on the top differential
  wedge to the actual differential pullback on every local wedge. The commuting
  square following `e` is the equivariance of the canonical-line isomorphism.
  Canonical differential normalization is tested on all F-valued translations
  and all local wedge generators, while Dω itself is a linearization on every
  test scheme. Smoothness over algebraically closed F makes S reduced and
  rational points dense, so these equations uniquely specify the algebraic
  differential action, including its evaluations on nonreduced test algebras.
- `cohomology Q L i` is an abbreviation for the existing `scalarCohomology`,
  whose carrier is `(RingedSpace.moduleCohomology Q.left.toRingedSpace i).obj L`.
  Thus this is right-derived O-module global sections with scalars restricted
  along Q → Spec F, not the unrelated underlying-abelian-sheaf Ext encoding.
- `δ` is an F-linear map into the actual module tensor F[S]. Its identity and
  multiplication laws are stated after every commutative F-algebra extension,
  using `pointAction` and the actual coordinate evaluation `RhoSection.evaluate`.
  Evaluating these equations at the identity and universal pairs is exactly
  counitality and coassociativity; conversely the coalgebra identities imply
  all these equations. There is no finite-dimensional restriction in this law.
- `IsInducedCoaction (D y) i (δ y i)` fixes the action to the canonical
  inverse-universal-translation pullback on S × Q, followed by the bundle
  linearization and canonical flat base-change comparison. The formula is
  written for every finite tensor presentation of δ(v). On v' tensor c the
  comparison is c times the pullback of v', so no arbitrary comparison
  isomorphism or representation has been assumed.
- `tr` is F-linear on H^N(-2rho). Its displayed tensor equality is precisely
  `(tr tensor id) δ(v) = tr(v) tensor 1`, with trivial action on F. Applying
  evaluation at any A-valued s gives tr_A(sv)=tr_A(v).
- The universally quantified y,z, with `z.hom.hom = y.hom.hom⁻¹*w.hom.hom`,
  are exactly y and -y-2rho. `i ≤ Φ.length` encodes 0 ≤ i ≤ N because i is a
  natural number. The two `Module.Finite` clauses are finite dimensionality
  of both displayed factors.
- `m` is an isomorphism of the actual tensor of lines with L(-2rho).
  `IsLineMultiplication` fixes its map on all local sections after pullback
  to S, multiplying their coordinates in the specified trivializations.
  Testing these local sections, including when H^0 on Q vanishes, determines
  the usual line multiplication. This is not a freely chosen tensor map.
- `cup` satisfies exactly the recorded `Scheme.Modules.IsModuleCupProduct`,
  including its resolution/cocycle characterization. The equation for `b`
  composes this cup with H(m), the degree equality i+(N-i)=N and tr.
  The equality transports a cohomology object only; no uncanonical equivalence
  is used. `Function.Bijective b` and `Function.Bijective b.flip` are precisely
  the two maps to the linear duals in the question.
- The final double-sum equation is the pairing coaction identity. For arbitrary
  tensor presentations δ(x)=sum x'_j tensor c_j and δ(v)=sum v'_l tensor d_l,
  it says sum c_j*d_l*b(x'_j,v'_l)=b(x,v)*1 in F[S]. Evaluating at every
  algebra-valued group point, and extending A-bilinearly, gives exactly
  b_A(sx,sv)=b_A(x,v) over every commutative F-algebra. Using finite tensor
  presentations avoids choosing a Sweedler decomposition or a basis.

Existing declarations used (the signatures and docstrings were opened):

- `Field`: Mathlib/Algebra/Field/Defs.lean:180; `IsAlgClosed`:
  Mathlib/FieldTheory/IsAlgClosed/Basic.lean:62. The algebraic-closure node's
  record identifies this class for the hypothesis; no actual chosen closure
  of F is needed.
- `CategoryTheory.GrpObj`: Mathlib/CategoryTheory/Monoidal/Grp.lean:43;
  bundled `Grp`, group-scheme kernels and their maps come from the recorded
  group-scheme definitions imported by the rho module.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`: `IsRhoBorelPair`,
  `exists_rho_section_modules`; the simply connected criterion is copied
  exactly from its signature, rather than defined again.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`.
  Its torus projection and quotient clauses are the interfaces used above.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsCongr` and its
  universal derivation/Hom equivalence.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`: `exteriorSheaf`,
  `exteriorSheafSection`, `exteriorSheaf_zero_iso` (degree-zero convention).
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`, documenting the recorded cohomology;
  the actual functor is `RingedSpace.moduleCohomology`.
- `Sheaf.Paper.ModuleCohomologyCupProduct`: `Scheme.Modules.IsModuleCupProduct`
  and `exists_unique_moduleCupProduct`. The theorem uses the predicate itself.
- `Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle`:
  `AssociatedCharacterLineBundle.Presentation`, all its canonical trivialization,
  section representation and base/total action fields.
- `Sheaf.AlgebraicGeometry.GroupSchemeLinearization`:
  `GroupSchemeLinearization.Linearization`, `act`.
- `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `Scheme.Hom.relativeDifferentialsPullbackMap`, the uniquely generator-normalized map.
- `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`:
  `Scheme.Modules.scalarCohomology`, with its structural scalar action.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `Scheme.Modules.moduleCohomologyPullback`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`; the comparison to the existing
  `pullbackPushforwardAdjunction` is left-adjoint uniqueness. This is actual
  canonical map data, not a choice from bare Nonempty.
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal`:
  `Scheme.Modules.pullbackMonoidal`, used in normalized line multiplication.
  `unitSectionsEquiv` in Modules.TensorSection identifies unit-sheaf sections
  with regular functions when multiplying the two coordinates.
- `RhoSection.Coordinate` and `RhoSection.evaluate` are publicly imported through
  the associated-line module; the latter is the actual Spec--Gamma evaluation.

The item's stmt_deps gains only six already landed terminology/interface nodes:
`def-sfb-associated-character-line-bundle`, `def-sfb-group-scheme-linearization`,
`def-a1-relative-differentials-pullback-map`,
`def-sc-field-linear-module-cohomology-operations`,
`def-weil-pbc-module-cohomology-fmap`, and `def-pc-module-pullback`.
All original dependency records are retained. No independent missing definition
has been invented. Helpers in the owning module just give the canonical maps and
normalization predicates needed to write this node (explicitly authorized by the brief).

The recorded proof dependencies with Lean modules are imported as plain imports:
StandardParabolicLeviCharts, ReductiveRankOneReflections, BorelOppositeRootDichotomy,
ReductiveRootSubgroupParametrizations and BorelRootProductCoordinates. The Borel-pair
module is already public. The homogeneous-cotangent, cohomology-coaction and
smooth-proper-trace proof nodes have no recorded Lean modules on the base and
are consequently not imported; this statement does not assume their conclusions.
It states the required result directly on the existing notions and canonical maps.

Edge cases checked:

- Empty positive-root list: N=0, hρ still makes sense, and the actual zeroth
  exterior-power sheaf is used. The local wedge test includes Fin 0's empty
  family, fixing the action on the structure sheaf; i=0 is admitted.
- SL2: tangent weights for S/Bminus are positive; cotangent determinant is the
  negative positive root, -2rho, giving O(-2) on P1. The second character is
  -y-2rho, so the standard O(n)/O(-n-2) Serre pairing has the correct signs.
- Characteristic two: hρ is an equation in character maps, not a half-sum in F.
- Cohomology groups may both be zero. The curried maps on zero modules are
  bijective, and all finite-sum and rationality equations still make sense.
- i=0 and i=N are both allowed, with H^N/H^0 in the appropriate order.
- Local multiplication is tested even when all global sections vanish, so it
  cannot be vacuously normalized by a global-section condition.
- Arbitrary algebra A, including zero and nonreduced algebras, occurs in the
  rationality law. Pairing/trace invariance is a coordinate-algebra identity,
  so no restriction to reduced algebras or F-points enters those conclusions.
- All coefficient, scheme and test universes follow the existing fixed-u
  group-scheme framework. No universe equality is imposed between previously
  independent parameters, and no field/algebra test universe is smaller than F.

Searches actually run:

- msearch leanfinder: `Equivariant Serre duality canonical line of flag variety invariant trace perfect pairing`.
  Eight results, including root-pairing maps, `FGModuleCat.exactPairing`,
  `LinearMap.IsPerfPair.dualEval`, FDRep rigidity and a Lie trace form. None states
  this flag-scheme cohomology theorem.
- msearch loogle: `LinearMap.IsPerfPair`. Twelve abstract pairing results;
  `IsPerfPair` means precisely bijectivity of both curried maps. No geometric match.
- msearch grep: `Serre.*pair|[Cc]ohomology.*[Cc]oaction|[Ll]inearization`
  under Mathlib/AlgebraicGeometry: zero hits.
- msearch leansearch: `Serre duality trace perfect pairing smooth proper flag variety canonical sheaf equivariant`.
  Eight abstract perfect-pairing results, none for coherent sheaf cohomology.
- Local rg in both lean/WeilConjectures and lean/Sheaf:
  `FlagLine|flagLine|HomogeneousLine|homogeneousLine|SerrePairing|serrePairing|Serre.*[Pp]air|cohomologyCoaction`.
  Found homogeneous line presentations, curve-only trace pairings and
  projective-space-only pairings; no flag theorem in arbitrary dimension.
- Local rg by the exact item id in lean/WeilConjectures and dag/lean_names_upstream.json:
  no declaration match. Local rg for `FlagSerre|flagLine_equivariant_serre_pairing`
  in lean/WeilConjectures, lean/Sheaf and the upstream name map: no collision.
- Local rg `equivariant.*Serre|Serre.*equivariant|flag.*pairing|canonical.*flag`
  in Mathlib/AlgebraicGeometry and both project AlgebraicGeometry trees: zero hits.
- `python3 tools/blueprint_refs.py search 'flag line Serre'`: zero blueprint nodes.
- A server `scompile.py --source Sheaf.AlgebraicGeometry.LinearizedQcoherentCohomologyCoaction`
  lookup returned source unavailable. This was a check for a possibly newer source,
  not evidence to introduce a duplicate definition or a dependency assumption.

Compilation uses only the prescribed scompile.py wrapper. It caught the need to
transport identity pullback in the canonical-wedge condition, and the distinction
between unit-sheaf sections and ring elements in local multiplication; both were
repaired with existing canonical comparisons. Final clean compile and dry-run
results are recorded below after validation.

## Second reading by Q02

This is an explicit second pass by the same dispatcher-started worker, not a claim
of independent agent review. The brief prohibits starting other agents and says
the maintainer independently reviews the delivery. I reread the actual node and
final source against each item above. The cotangent action uses inverse translation
and differential pullback in the matching direction; the cohomology action uses
that same inverse translation with the inverse forward linearization. The tensor
multiplication is fixed on all local atlas sections, and the pairing is the
recorded cup product followed by H(m) and a single trace shared by every y,i.
Both curried maps and both finite-dimensionality clauses are present. The two
elaboration mismatches found on the first reading were repaired as described
above; no mathematical statement change was needed. Independent mathematical
review remains the maintainer's task under the dispatcher brief.

Validation: final scompile.py run succeeded for both the sandbox probe and the actual
module path, with no errors or warnings reported. The signature record matches the
final source verbatim; there is one sorry, no auto-implicit variables, and no Lean
source line exceeds 100 characters. No global build or direct repository write was run.
