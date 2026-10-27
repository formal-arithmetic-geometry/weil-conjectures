## Worker report

Item: `lem-trf-block-straightening-projection-transport`.
Module: `Sheaf.AlgebraicGeometry.BlockStraighteningProjectionTransport`.
Main declaration: `AlgebraicGeometry.HilbertCoefficient.blockStraighteningProjectionTransport`.
The only postponed proof is this theorem, with the seven DAG proof steps in its docstring.
All auxiliary definitions contain actual data; the input/output structures specify the
objects in the statement and do not choose witnesses using an existence axiom.

Source read: Bierstone--Milman, Inventiones 128 (1997), Theorem 9.6, (9.7)--(9.8),
Remarks 9.9--9.11, printed pp.279--280, and the matrix argument on p.281, available at
https://mahalex.net/teaching/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf .
The source explicitly uses the block order `(w,y,T)`, mixed regular/formal derivatives,
the implicit graph substitution, and a single open for regular coefficient families.
The additional exact stored projection is the node's agent refinement, proved by its
existing finite coefficient-operator base-change dependency. The node is an extracted
subargument of the blueprint's local Hilbert presentation route, not a unit statement.
The mathematical statement needs no correction and is not disputed. The H2 return
requires the definition-ownership extraction documented below.

Hypothesis-by-hypothesis correspondence:

- Characteristic-zero field: `{k : Type u} [Field k] [CharZero k]`.
  `B : Scheme.{u}` and `a : B` give the coefficient scheme and distinguished point.
- Smooth, finite type and etale coordinates `(w,y)`: `c` is the polynomial-coordinate
  homomorphism. `BlockStraighteningInput.etale`, `.smooth`, and `.finite_type` use
  the recorded `Etale`, `Smooth`, `LocallyOfFiniteType` and `QuasiCompact` classes on
  `implicitCoordinateMorphism c` and `implicitStructureMorphism c`. Finite type is
  the recorded conjunction, without an additional affine hypothesis on B.
- Coordinate derivations: `D : ImplicitCoordinateDerivations B c`, whose fields kill
  ground-field scalars, send the coordinates to their Kronecker values, commute and
  respect restriction. These are the existing coordinate derivations specified by
  the node, not arbitrary derivations substituted for them.
- Previously formal transverse variables and regular coefficient families:
  `f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤)`. There is no finite-support hypothesis.
  `.taylor` and `.taylor_spec` name the centered coefficient Taylor maps at every
  point, using the existing `isTaylorMap` characterization. This retains all relative
  coordinates also at nonclosed points and does not identify the original stalk's
  completion with the full relative-coordinate power series ring.
- Initial exponents: `.first` uses the existing `MonomialDiagram.IsFirstExponent` on
  `blockFlattenChart (map (taylor a) (f i))`. `blockVariableEquiv` numbers the full variables
  w, then y, then T, as `Fin ((m+r)+t)`. This avoids Mathlib's default incomparable
  Sum summands and enforces precisely complementary-first degree-lex order.
- Minimal vertices of a monotone diagram, in ascending order: `.vertices` is the
  existing `IsOrderedVertexFamily (generated α) α`; `.monotone` is the existing
  `IsMonotone (generated α)`. They specify minimality, no repetition, additive
  closure, and the whole-coordinate transfer for every u<v.
- Degree blocks and their last indices: the current block is represented by its
  degree `d`, with `.current_block` saying it occurs. Indices before it are exactly
  those with `(α i).degree < d`; indices later than the old block have degree ≥d.
  Earlier blocks are the occurring degrees q<d. This is the same partition, with
  no chosen enumeration of the distinct degrees or extra nonempty-block condition.
- Old and newly essential variables: `.old_variables` identifies the union of supports
  of vertices of degree <d with exactly T; `.current_variables` identifies the degree-d
  prefix support with exactly `(y,T)`. Consequently y is precisely the new essential
  block and no w coordinate belongs to this prefix.
- Earlier stages after the inherited identifications: `.old_stages` uses
  `blockOldStages` at every b and every occurring prefix q<d. Its first clause places
  all earlier vertex derivatives in their earlier transverse variable ideals, as
  full series in the complementary variables. Its second clause is the invertible
  transverse Jacobian of these equations. These express the already straightened
  derivative-equation descriptions of the earlier smooth closed coefficient stages;
  their ambient formal ideals are the corresponding coordinate ideals. B is their
  final coefficient scheme, with the given smooth etale chart. No unrelated ambient
  scheme or arbitrary replacement for the inherited Taylor ideal is introduced.
- Q bound: `.bound : ∀ i, (α i).degree - 1 ≤ Q` is equivalent to the stated maximum
  bound. The current block exists, so the vertex family here is nonempty.
- Earlier exact coefficient identities: `.old_tests` quantifies all occurring q<d,
  all i with q<(α i).degree, and all `FormalCoefficientTest t` satisfying
  `blockTestAt α q Q`. This predicate says the fixed exponent has degree ≤Q, belongs
  to the prefix diagram restricted to T, and the retained variables are precisely
  the complement of its essential variables. The test structure already requires
  its fixed exponent to vanish on retained variables. `E.eval (f i)=0` is equality
  of full complementary-variable series. Every ordering of complementary variables
  is allowed; duplicate enumerations do not alter a common kernel.
- Ideal membership and generation in every centered Taylor ring: `.ideal`, `.membership`
  and `.generation` explicitly bind K_b and require membership of every Taylor f_i and
  equality with their generated ideal. The ideal is in the iterated ring, identified
  with joint coefficients by `blockFlattenChart`.
- Chosen vertex derivatives: `pick` and `β` range over all current transverse variables,
  with the new ones first. `.vertex_derivative` is the displayed equality alpha=beta+e_j;
  `.first_block` requires the chosen vertex to occur in that variable's first degree
  block; `.beta_supported` confines beta to that degree prefix. This retains the old
  picks as well as choosing the newly essential ones, as required by the joint clause.
  `blockDerivative` uses actual formal `pderiv` iterates in T followed coefficientwise
  by the existing regular y derivations.
- Optional P: the output's `.projection` quantifies every
  `FiniteCoefficientExpression Γ(B,⊤) t 1 t 1`. The syntax includes addition,
  composition, extraction, insertion, full-series multiplication and finite matrices;
  specified inverse matrices are already matrices of regular coefficients, as in the
  recorded dependency. `blockProjectionHypotheses` specifies exactly projection onto
  the common old-test kernel, correction by the ideal of degree-<d generators on ALL
  inputs, fixing degree-≥d generators, and the first-exponent property at a on ALL
  completed series whose first monomial passes the tests. It does not require a source
  lift of the coefficients of an arbitrary formal input. The geometric construction
  is available without assuming that a projection was supplied.

Conclusion-by-conclusion correspondence:

- `blockEquations` computes the regular h_j as the T=0 coefficient of the actual mixed
  derivative. Its codomain is Γ(B,⊤), so regularity is part of this real construction.
  The theorem's first conjunct is h_j(a)=0; its second is the nonzero y-Jacobian at a.
- `BlockStraighteningOutput` specifies one open subset of the existing actual zero
  scheme `implicitZeroScheme D h`, a common ambient open, and a cartesian square.
  `.closed` is its closed immersion into that ambient open. `.center` and `.center_eq`
  keep a. `.smooth` says C is smooth over k; `.etale` says its restricted w coordinates
  are etale. `.affine` is the permitted further common affine shrinking used in step 6.
- `.points` gives the existing `ImplicitTaylorPoint` at EVERY point of this same C.
  Its `.phi`, `.phi_zero`, `.solution`, `.straight_apply`, `.straight_inverse` and
  `.ideal_straight` state the implicit graph substitution y=phi_b(W)+Y and the equality
  of the extended ideal of C in B with (Y). Its residue fields are the actual
  `C.residueField b`; no rational or closed-point restriction is imposed.
- `.ideals` identifies the inherited transformed K_b with the ideal generated by all
  transformed f_i; `.membership` states membership in that same transformed ideal.
  The displayed scalar extension uses the actual inclusion's `.residueFieldMap b`,
  followed by the formal graph ring isomorphism, so it does not compare ideals over
  different residue fields without transport. `.first` retains every alpha_i at a.
- `.rho` is an honest ring homomorphism Γ(B,⊤)→Γ(C,⊤)[[Y]], not an assumed arbitrary map.
  `.rho_coeff` prescribes EVERY coefficient, namely the restriction of the regular
  y derivative divided by delta!. `blockRegularCoefficient` takes inverse factorials
  in k and maps them into the section ring; it never assumes the section ring is a
  field. `.coefficient_specialization` identifies these regular coefficients with
  their Taylor expansions at every point for every regular function. `.coefficients`
  spells out the resulting Y^delta T^gamma identity for all f_i and all exponents.
- `.old_tests` retains the exact zero tests on rho_* f_i as full Y-series and on every
  centered completed coefficient ring, including indices in intermediate old blocks.
- `.joint_derivatives` puts ALL selected derivatives, old and new, in the ideal of
  `(Y,T)` at every b, and requires the full transverse Jacobian determinant to be a
  unit there. The finite determinant shrinking occurs only once, uniformly on C.
- `.projection` gives `blockProjectionConclusions` for the actual transported syntax
  `P.map rho`. Evaluation is linear over Γ(C,⊤)[[Y]] by the existing finite-expression
  evaluation interface; this includes arbitrary target inputs. Its conjuncts give
  the full old-test kernel projection, ideal correction, later-generator fixing,
  zero old-test coefficients in EVERY Y degree, and the corresponding kernel,
  correction and fixing assertions for every unrestricted centered Taylor input.
  Its `blockPreservesFirst` conjunct retains the first-exponent property at a.
- Every scalar, matrix entry, specified inverse entry, and coefficient of every full
  correction column is carried by the SAME `rho` in `FiniteCoefficientExpression.map`.
  The universal `.rho_coeff` assertion makes all of them regular on this same C.
  There is no separate coefficient-dependent neighborhood, truncation, new arbitrary
  projection, or assumption that the target coefficient homomorphism is surjective.
- `IsEmpty (BlockEarlierTest α d Q)` implies P.scalarEval=id and its transported
  evaluation=id explicitly. If r=0 the equation family is indexed by Fin 0 and
  contains no equation; the graph has no new components and rho is restriction
  under the canonical zero-variable identification. Shrinking remains permitted.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, the evaluation and residue maps.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, coefficients and maps;
  `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv`.
  The derivative node is a Mathlib leaf with no lean record; its mathlib_match is used.
- `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`: `essential`, `inDiagram`,
  `iteratedPartial`, `isTaylorMap`.
- `Sheaf.RingTheory.SupportedHomogeneousDivision`: `MonomialDiagram.IsMonotone`,
  `IsOrderedVertexFamily`, `generated`.
- `Sheaf.RingTheory.FormalInitialDiagram`: `MonomialDiagram.IsFirstExponent`.
- `Sheaf.RingTheory.FiniteCoefficientExpression`: `FormalCoefficientTest`, its `eval`,
  `FiniteCoefficientExpression`, its `map`, `scalarEval` and `IsKernelProjection`.
- `Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus`:
  `ImplicitCoordinateDerivations`, `implicitIteratedDerivative`, `implicitJacobian`,
  `implicitZeroScheme`, `implicitZeroInclusion`, `implicitCoordinateMorphism`,
  `implicitStructureMorphism`, `implicitTransverseCoeff`, `ImplicitTaylorPoint`.
  The calculus theorem remains the first geometric proof dependency. Its module is
  public because it also supplies the definition-owned data used by the statement.
  `implicitTransverseCoeff` is owned by the existing
  `def-trf-implicit-transverse-coefficient` node and reused from that same module.
- Proof-only imports retain `Sheaf.RingTheory.FormalCoefficientOperatorBaseChange`
  (including all-input kernel and Noetherian ideal transport, and formal-target and
  composition compatibility), `Mathlib.RingTheory.FiniteType` and
  `Mathlib.RingTheory.MvPowerSeries.Equiv` (the two Noetherian proof dependencies).

The original seven statement dependencies remain intact. Three added dependencies
are the landed formal-initial-diagram, supported-division and finite-expression
definition nodes; a fourth is the landed regular Hilbert coefficient datum. The fifth
is now the new definition node `def-trf-implicit-taylor-coordinate-data`, replacing
the calculus theorem that the returned packet had added to stmt_deps. The calculus
theorem remains in proof_deps. All block helpers retain their own node ownership.
The existing shared definitions and their definition-node ownership are detailed below.

Edge cases checked before writing and in the final rereading:

- t=0: no old formal variables; no old block can have an essential variable, and the
  test family and empty-stage Jacobian use the existing empty-index conventions.
- r=0: the new equation family and new Jacobian are empty (determinant 1); no equation
  or shift is demanded. Existing old derivatives and projections still occur.
- m=0: C has zero relative dimension; Taylor coefficients are constants in zero w
  variables. Nonclosed residue extensions remain explicit.
- The block itself must exist, hence s=0 has no block to which this lemma applies.
  This does not exclude the empty NEW block r=0. The unit ideal with alpha=0 is
  allowed: d=0, r=t=0, Q=0, no selected derivatives or equations.
- Zero coefficients and infinite families are allowed. A generator whose exponent
  alpha_i is specified is nonzero at a by IsFirstExponent; no exponent is assigned
  to a zero series. Q=0 and first blocks of degree 1 are allowed.
- Empty tests force the identity, including on unrestricted target inputs. Empty
  finite matrices and zero correction columns are accepted by the existing syntax.
- Partial tests retain ALL complementary degrees. In particular equality only at
  Y=0 would not imply the displayed all-delta conclusion and was not substituted.
- The ordering does not use the default Sum relation: full indices are Fin, so the
  proof's comparison of a new variable with an earlier W coordinate is meaningful.
- The characteristic-zero factorial inverse is taken in k, not in an arbitrary ring
  of functions. The same neighborhood handles all coefficients.
- Arbitrary and nonclosed b use the actual residue-field map of the inclusion; the
  inherited ideal is extended along it explicitly before the graph substitution.

Searches actually run (2026-10-24):

1. msearch.py / leanfinder: "Etale derivative coordinate straightening transports
   initial exponents of power series and exact coefficient projections". Eight hits:
   StandardEtalePair.hasMap_X, StandardEtalePresentation.toPresentation_σ',
   StandardEtalePresentation.hasMap, StandardEtalePresentation.toSubmersivePresentation,
   StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x,
   StandardEtalePresentation.P, PowerSeries.IsWeierstrassDivisorAt.seq and .seq_one.
   None states a multivariate block straightening and exact projection transport.
2. msearch.py / loogle: "MvPowerSeries.pderiv, AlgebraicGeometry.Etale". Zero hits.
3. msearch.py / grep, RingTheory: "initialExponent|[Bb]lock[Ss]traightening|[Cc]oefficient[Pp]rojection".
   Zero hits. This is a search for an existing statement, not a claim that derivatives
   or coefficient operations are absent: their existing declarations above are reused.
4. rg on lean/WeilConjectures and lean/Sheaf for implicitTaylor, ImplicitTaylor,
   initialExponent, ExactProjection, coefficientOperator, CoefficientOperator,
   BlockStraightening and blockStraightening. Found the existing implicit Taylor
   calculus and the unrelated categorical exact projection mate. The formal operator,
   initial diagram, monotone diagram and regular coefficient modules were then opened
   in full or at all used declaration signatures/docstrings and reused.
5. rg for the exact item ID in lean/WeilConjectures: no result. File/name searches in
   the project, upstream declarations and DAG identified no existing theorem for this
   item. Further straightening searches in the upstream algebraic geometry, current
   Sheaf algebraic geometry and Mathlib ring-theory sources found only its supporting
   Taylor calculus and regular coefficient data, not a duplicate of this statement.

Validation: scompile.py compiled this module separately under sandbox and final module
names, without errors or warnings, in approximately 11--12 seconds per pass. All
compilation used the prescribed server wrapper. Dry-run and delivery results follow
from deliver2.py; no live source or launcher tool was edited and no git command was run.

## Second reading by Q42

This is the worker's final semantic rereading, not a claim that another agent reviewed
it. The dispatcher's brief forbids starting agents and assigns independent review to
the maintainer. I reopened the node and completed module and matched each clause above.
The final rereading added explicit retention of all old-generator tests, not merely
those implied for later fixed generators by the projection, and added the completed
operator's later-generator fixing at every b. It also made coefficient specialization
universal over all regular functions so that regularity applies to matrix and correction
column coefficients as well as to f_i. The residue-field scalar extension in the ideal
clause, the explicit Fin ordering, the unrestricted ideal-correction inputs, and the
empty newly essential block were checked against the source paragraphs. No existing
notion was redefined: the helpers are the constructions and specifications of this
single block. The theorem has exactly one sorry, and definitions have none.


## Repair of the collision at 52e060545c2a

The returned landing named implicitTransverseCoeff as declared both in the proposed
ImplicitTransverseCoefficient module and in the existing ImplicitTaylorCoordinateCalculus.
The earlier packet attempted a source move, removing the old declaration in the same
packet, and all four modules compiled together. The per-module landing check still
compares a new module against existing source before the removal lands. The latest
return explicitly says to import and reuse the existing declaration. This repair
follows that instruction for all shared data and removes the extraction altogether.

The packet now delivers only the unchanged block theorem module and its record,
the new definition node, and this report. It removes all three auxiliary modules
from the returned packet and removes both dependency-node edits. In particular it
neither declares implicitTransverseCoeff nor changes its already landed owning node.
No shared declaration is copied, renamed, moved, restated, or proved again.

The original H2 fault remains repaired: the item cites the definition node
`def-trf-implicit-taylor-coordinate-data` in stmt_deps instead of the theorem node.
The new node records existing:true with the exact existing definitions and their
module. The calculus theorem remains in proof_deps, exactly as requested. Public
import of its module is needed to expose the definitions; it does not assert use
of the theorem's existential D in the statement. D remains a statement parameter.

## New nodes

`def-trf-implicit-taylor-coordinate-data` owns the existing coordinate derivations,
Jacobian-open equation scheme, coordinate and structure morphisms, formal shift
helpers, iterated regular derivative, and pointwise implicit Taylor data. Its
existing:true record points to `Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus`;
there is no new module. Its principal declaration is ImplicitTaylorPoint. This
is an ownership record for an existing data specification, not an existence theorem.
The existing `def-trf-implicit-transverse-coefficient` owns coefficient extraction
and is cited, so the new node does not claim that operation a second time.

The node's clauses correspond to the existing declarations as follows:

- `implicitCoordinatesOnOpen` and `implicitCoordinatesAt` restrict the polynomial
  coordinates and take their actual germs.
- `ImplicitCoordinateDerivations` specifies derivations on every open with scalar,
  coordinate, restriction and commutation fields.
- `implicitJacobian`, `implicitJacobianOpen`, `implicitEquationIdeal`,
  `implicitZeroScheme`, `implicitZeroInclusion` give the determinant, its actual
  nonvanishing open, scheme-theoretic ideal and canonical zero-scheme inclusion.
- `implicitCoordinateMorphism` and `implicitStructureMorphism` are the specified
  morphisms through B.toSpecΓ, not arbitrary replacements.
- `implicitShiftVariables`, `implicitGraphVariables`, `implicitShiftFamily` use
  actual formal substitution; `implicitIteratedDerivative` iterates the regular
  y derivations in the specified increasing-coordinate list.
- `ImplicitTaylorPoint.deriv`/`.germ_partial` extend the coordinate derivatives.
  The taylor/taylorN maps, their spec and unique fields give the existing residue
  and coordinate characterization at the actual stalks, even at nonclosed points.
- The phi/phi_zero/phi_value/solution/unique_solution fields specify the centered
  implicit graph; matrix/matrix_unit/factorization specify its factorization.
- The straight/apply/inverse and continuity fields give the actual continuous
  substitution equivalence and inverse. ideal_of_N/ideal_straight specify the
  extended kernel ideal and its coordinate-ideal image.
- restriction/derivative/coefficients give the graph restriction, differentiation
  compatibility and all formal-family coefficients with the factorial formula.
  faithfullyFlat/ideal_descent give faithful flatness and ideal equality descent.
- All six extension fields quantify every coefficient-field extension in Type v,
  including uniqueness of both Taylor maps, invertible factorization, unique
  graph solution, substitution and derivative coefficient compatibility.

All variables/universes and zero-dimensional/empty-coordinate conventions are those
of the existing declarations. There is no new mathematical restriction or assumption.
The source remains BM Lemma 3.5 and Remarks 3.7, 9.9, 9.11 with the existing algebraic
nonclosed-point interpretation and ILO VIII 2.3.11--2.3.13 route context.

The three required Mathlib searches are retained verbatim in mathlib_searches:
LeanSearch for implicit Taylor coordinate data (eight analytic/polynomial Taylor
hits, no algebraic scheme datum), Loogle "MvPowerSeries.subst, Derivation" (zero
hits), and Mathlib AlgebraicGeometry grep for ImplicitTaylorPoint,
ImplicitCoordinateDerivations, implicitZeroScheme (zero hits). Project/upstream/DAG
rg found only the original calculus module and theorem record for the package;
blueprint_refs search "implicit Taylor" found zero nodes. The exact project
interface is reused; only a definition-node ownership record was missing.

## Repair self-check by Q42

I read the collision return, the original shared source via scompile.py --source,
the new existing-definition record, and the block module. Current server source
still defines implicitTransverseCoeff and all coordinate data in the original
calculus module. The final packet now imports and reuses exactly those declarations.
There are no auxiliary Lean modules or dependency-node rewrites in this packet.
The block theorem signature and all mathematical clauses remain unchanged.
The subsequent chart-adapter collision repair is described below. The item
adds the new definition-node dependency and keeps the theorem in proof_deps. This
both preserves the first H2 ownership repair and removes the returned collision.
The main hypothesis/conclusion mapping and all edge-case checks above still apply.
No other agent was started, as required by the dispatcher's brief.

Validation uses scompile.py for the block module, and deliver2.py for the dry run
and delivery, including its existing-declaration probes. Only the block theorem's
expected sorry warning is permitted. No live source, tool or compiled artifact is
edited and no direct git command is run.


## Repair of name collisions at 0da0f305bc6b

The return names blockFlatten and blockNewExponent in the landed
ExactBlockCoefficientProjection module. I read both complete definitions and their
docstrings, including the current server source via scompile.py --source. The
signatures distinguish the two pairs of operations:

- Existing blockNewExponent takes a vertex family, Q, d and a transverse exponent
  and returns Prop: membership in the bounded new prefix tests. This block's old
  helper instead took one full (w,y,T) exponent and returned its y exponent. It is
  now named blockNewVariableExponent, retaining the same restriction formula.
  This is the return's permitted case of two declarations saying different things.
- Existing blockFlatten takes T-series with coefficients in R[[Fin m]], returning
  series indexed by Fin (m+t). Our chart has coefficients indexed by Fin m ⊕ Fin r
  and needs Fin ((m+r)+t). The chart adapter is now blockFlattenChart. Its body
  renames the coefficient chart to Fin (m+r), applies the existing
  MvPowerSeries.flattenFormalCoefficients, and renames the final sum to Fin.
  Thus the actual coefficient regrouping is reused from the existing definition
  node def-trf-finite-coefficient-expression, which is already in stmt_deps.
  No second generic flattening is defined, and no theorem-module dependency is
  introduced merely for its helper definitions.

These helpers' new docstrings state the domain/codomain distinctions explicitly.
Every reference and lean.declarations entry uses the new names. The theorem
signature, all geometric and projection clauses, dependency list and exponent
ordering are unchanged. The adapter implements exactly the previous coefficient
formula: for a full exponent, renameEquiv splits off the (w,y) exponent and the
existing flattenFormalCoefficients splits off T. This is canonical reindexing;
it adds no assumption or truncation and does not exchange w, y or T.

The r=0, m=0 and t=0 cases use the same finSumFinEquiv and zero-coordinate series
conventions as before. All infinitely many coefficients are retained. The new
variable restriction still applies to the actual y positions, independently of
whether an exponent belongs to any forbidden-test set. The record's main theorem
signature is unchanged verbatim. No statement correction is required.

The original three search families remain recorded. For this repair the targeted
source search was rg for blockFlatten/blockNewExponent in lean/Sheaf and dag/nodes;
it identified ExactBlockCoefficientProjection and its theorem record. The existing
formal flattening was read at FiniteCoefficientExpression.lean:133--145 and reused
from its already-recorded definition node. No new node is required. Validation is
per-file scompile.py followed by the prescribed dry run and delivery.
