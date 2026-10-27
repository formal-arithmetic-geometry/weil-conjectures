## Worker report

The module `Sheaf.AlgebraicGeometry.TriangularRepresentationEigenline` states
`AlgebraicGeometry.RationalRepresentation.triangular_representation_eigenline`.
Its sole theorem has proof `by sorry`; there are no new definitions, instances,
axioms, or helper theorems. The node's natural-language statement, proof and
proof dependencies are unchanged. Its statement dependencies gain the multiplicative-group node and the new
definition ownership node `def-sfb-rational-representation-coordinate-comodule`,
which records the already landed plain definitions used in the signature. The
comodule dictionary theorem remains a proof dependency only.

Source read: Milne, *Algebraic Groups* (2017), Definition 16.1, printed p.324,
and Proposition 16.2(c) implies (d) implies (a), printed p.325. The source says
that an algebraic subgroup of the triangular group is trigonalizable, with
nonzero unipotent invariants and the diagonalizable quotient supplying an
invariant line. No algebraic-closedness, characteristic, smoothness or
connectedness hypothesis occurs. The node's eight proof steps are included,
with their cited prerequisites, in the theorem docstring.

The hypothesis and clause correspondence is as follows.

| Node text | Lean rendering |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| An affine k-group scheme J | `J : Scheme.{u}`, `J.Over (Spec (.of k))`, `GrpObj (J.asOver (Spec (.of k)))`, and `IsAffine J` |
| Finite type over k | `LocallyOfFiniteType (J ↘ Spec (.of k))` and `QuasiCompact (J ↘ Spec (.of k))`, exactly the recorded finite-type convention |
| Some n >= 1 | A binder `n : ℕ` and `hn : 0 < n`; supplying any witness of the stated existence supplies these arguments |
| Closed immersion of group schemes into B_n | `i : J.asOver (Spec (.of k)) ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k`, `IsMonHom i`, `IsClosedImmersion i.left`, and `htri` |
| B_n(A) consists of invertible upper triangular matrices over every k-algebra A | `GeneralLinearGroup.homMulEquiv` already gives an invertible matrix; `htri` quantifies over every `R : Type u` with `CommRing R` and `Algebra k R`, every scheme-valued point `x`, and every `a b : Fin n` with `b < a`, and sets entry `(a,b)` to zero |
| A nonzero finite-dimensional vector space V | `V : Type u`, `AddCommGroup V`, `Module k V`, `FiniteDimensional k V`, `Nontrivial V` |
| A linear coaction satisfying exactly the two stated identities | `c : CoordinateComodule (k := k) J V`; this is the existing subtype of `V →ₗ[k] V ⊗[k] Γ(J, ⊤)` satisfying `HopfAction.Coassociative` and `HopfAction.Counital` |
| A one-dimensional subspace | `L : Submodule k V` and `Module.finrank k L = 1` |
| A group-scheme character J to G_m | `χ : J.asOver (Spec (.of k)) ⟶ StandardGroupSchemes.multiplicative k` and `IsMonHom χ` |
| The coordinate t in k[t,t^-1] | `LaurentPolynomial.T 1`, transported into the global sections of its affine spectrum by `(Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv` |
| c(v) = v tensor chi*(t) for every v in L | The conjunct `∀ v : L, c.val v = (v : V) ⊗ₜ[k] ...`, whose coefficient is `χ.left.appTop` applied to that transported Laurent coordinate; `@id Γ(J, ⊤)` only fixes the elaborator's choice of the identical global-sections type |
| L is a rational submodule | The same coaction formula lands in the image of `L ⊗[k] Γ(J, ⊤)`. In addition the final conjunct explicitly preserves the image of `L.subtype.baseChange R` for every test algebra |
| Its action is by chi after every commutative k-algebra extension | An existing `NaturalRepresentation J V` is exhibited with `genericCoaction J V r = c.val`, and for every algebra `R`, every coordinate point `x : Γ(J, ⊤) →ₐ[k] R`, and every `z : R ⊗[k] L`, the action on `L.subtype.baseChange R z` equals multiplication by `x (χ.left.appTop (t))` |
| No algebraic closedness, smoothness or connectedness | No such instance or proposition occurs; there is also no perfectness or characteristic restriction |

The formulation of the embedding introduces no new notion and changes no
hypothesis. The upper triangular group is the closed subscheme of GL_n defined
by its below-diagonal coordinates. Vanishing on **all** algebra-valued points,
in particular the universal coordinate-valued point of J, says exactly that
the coordinate map kills these equations. Thus i factors through B_n. Since
B_n to GL_n is a closed immersion, a closed immersion J to GL_n factoring through
it is a closed immersion J to B_n (the corresponding coordinate map remains
surjective). Conversely a closed immersion into B_n composes to just such an i.
This matches the already landed all-test-algebra matrix convention in
`Sheaf.AlgebraicGeometry.CharZeroCommutativeUnipotentVectorGroup`.

The final action clause uses the affine Spec dictionary: every R-point of J is
`coordinatePoint J R x` for its unique algebra homomorphism x. Consequently it
covers all R-points, including points invisible on k-rational points. The
representation r is not an arbitrary extra assumption: its existence and the
equality of its generic coaction to c express the representation determined by
the given coaction, via the already landed dictionary. Quantification over all
`z : R ⊗[k] L` records the whole scalar-extended line, not just vectors from L.
The character value is the image of the Laurent coordinate under the point
composed with chi, exactly `x (chi*(t))`.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`
  (lines 45--49), with `CategoryTheory.IsMonHom` for homomorphisms;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents their
  specialization to group schemes over `Spec k`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (line 43), and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact` (line 43).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (line 45).
- `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`:
  `AlgebraicGeometry.RationalRepresentation.CoordinateComodule`,
  `NaturalRepresentation`, `coordinatePoint`, and `genericCoaction`.
  Its `dictionary` theorem supplies the intended equivalence for stage 3.
  The coassociativity/counitality definitions were read in
  `Sheaf.RingTheory.HopfActionModuleData`; the canonical coordinate Hopf
  instance was read in `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`
  and `Mathlib.AlgebraicGeometry.Group.Affine` (lines 337--343).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and
  `multiplicativeGroup`; their data are Spec of the Laurent Hopf algebra.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`:
  `AlgebraicGeometry.GeneralLinearGroup` and its `homMulEquiv`.
  These are the recorded general-linear-group interface, publicly imported
  through the comodule dictionary and its `LinearGroupSchemes` dependency.
- The available proof interfaces are imported without `public`:
  `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis`
  (`TensorProduct.eq_zero_of_forall_rTensor_eq_zero`) and
  `Mathlib.RingTheory.Coalgebra.GroupLike`
  (`linearIndepOn_isGroupLikeElem`). Unstated proof prerequisites do not
  require extra theorem statements in this statement delivery.

Edge cases checked before drafting and on the second pass:

- n = 1: there are no pairs b < a, so htri is correctly empty and the group
  is a closed subgroup of G_m. n = 0 is excluded by the node itself.
- V = 0 is excluded by `Nontrivial V`, exactly as required; dimension-one V
  is allowed and its full space can be L.
- The trivial group is allowed, with trivial character and any line in V.
- Non-smooth groups such as alpha_p and mu_p in characteristic p, disconnected
  triangular subgroups, finite base fields and imperfect fields are all
  admitted. No argument replaces a scheme-theoretic condition by k-points.
- The zero test algebra, nonreduced algebras and arbitrary test-algebra
  dimensions are allowed: only `CommRing R` and `Algebra k R` occur.
- All objects are in an arbitrary common universe u, as in the existing
  dictionary, with the finite matrix index lifted to that universe. No
  independent, potentially smaller universe of test algebras is used.

Searches actually run:

- `msearch.py ... leanfinder` with query
  `A nonzero finite dimensional rational representation of a closed subgroup scheme of the upper triangular matrices over any field has an invariant line with a group scheme character`:
  eight hits, including abstract-group invariant submodules and the
  finite-group characteristic-zero Schur lemma; no exact rational
  group-scheme statement.
- `msearch.py ... leansearch` with query
  `A rational representation of a trigonalizable algebraic group has a one dimensional subrepresentation`:
  eight hits, chiefly Lie-module triangularizability and abstract-group
  subrepresentations; no exact match.
- `msearch.py ... loogle` with query
  `Representation, IsTriangularizable, IsGroupLikeElem, Comodule`:
  zero hits, with the service diagnostic `unknown identifier 'IsTriangularizable'`.
  This query was not treated as a successful exhaustion of those names.
- `msearch.py ... grep` with query
  `upperTriangular|UpperTriangular|IsTriangularizable|eigenline`:
  25 hits on matrix triangularity, modular cusps and Lie modules, no theorem
  for rational representations of triangular group schemes.
- `rg -n 'upperTriang|UpperTriang|triangular|Triangular|eigenline'`
  over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  found matrix conventions, unrelated field models and the existing
  unipotent group statement, but no exact theorem. Narrower searches found
  the existing comodule dictionary and standard multiplicative group.
- Search by the exact node id in `lean/WeilConjectures`: no declaration.
- Search for the proposed theorem name and `characterCoefficient` in
  `lean/WeilConjectures` and `lean/Sheaf`: no collision. No helper definition
  named characterCoefficient was ultimately introduced.
- Search of `coord/repair-notes` for this item: no released repair note.

No `STATEMENT-DISPUTED` issue or mathematical correction was needed. The
repository's advertised CompactObject example is now a withdrawn module, so
this module follows the current header and public-import conventions directly.

## Second reading by Q06

A separate pass in this worker reread the node, Milne pp.324--325, the complete
Lean signature, and the imported comodule and multiplicative-group definitions.
This is a self-check, not a claim of review by another worker: the dispatcher
explicitly forbids starting other agents, and the maintainer supplies the
independent delivery review.

The pass checked each row above. In particular it checked b < a rather than
a < b, closed immersion rather than mere pointwise injectivity, both finite-type
conditions, nonzero V, both coaction axioms, finrank one, a genuine scheme
character, the direction of the pullback on global functions, and the action
on **every** tensor of the extended line. The coordinate point quantifier was
checked against the affine dictionary, so it drops no algebra-valued point.
It found an elaboration issue in the coefficient's global-sections type:
Lean inferred the identical but syntactically different `J.asOver.left` and
failed to infer its k-module. An explicit `@id Γ(J, ⊤)` fixes the intended
type without changing the coefficient or adding an assumption.

## Validation

Every compiler invocation used the prescribed `scompile.py` wrapper and module
mode. Initial server diagnostics identified the global-sections elaboration
issue above. The wrapper also reported `OSError(28, 'No space left on device')`,
and a later attempt returned only `resource exhausted (error code: 28, no space
left on device)`. The required `deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`
then failed with the same server `resource exhausted (error code: 28, no space
left on device)` message and explicitly reported that nothing was pushed.
Compilation and preflight therefore remain unverified; no delivery commit exists.
The final source and its verbatim node signature are preserved in the sandbox.
No launcher script, shared source, global build or published artifact was edited.

## Resume validation, 2026-10-24

Retained the saved packet and started with the required
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`.
It exited 1 after 2.9 seconds with `COMPILE FAILED on the server, nothing pushed`
and `resource exhausted (error code: 28, no space left on device)` for
`sandbox Sheaf.Stage2.Sandbox0`. A subsequent direct `scompile.py Q06
lem-sfb-triangular-group-representation-eigenline` invocation on the saved module
also exited 1 after 2.9 seconds with the identical server disk-space error.
Neither invocation supplied a Lean statement diagnostic to repair. The source
and node record remain unchanged; compilation and preflight remain unverified,
and no delivery was pushed. This is a repeated server tool failure.

## Further dispatcher retry, 2026-10-24

Started again from the preserved packet with the prescribed `deliver2.py Q06
lem-sfb-triangular-group-representation-eigenline --no-push`. It exited 1 after
2.9 seconds: `COMPILE FAILED on the server, nothing pushed`, followed by
`sandbox Sheaf.Stage2.Sandbox0` and `resource exhausted (error code: 28, no space
left on device)`. A direct `scompile.py` invocation on
`lean/Sheaf/AlgebraicGeometry/TriangularRepresentationEigenline.lean` also exited
1 after 2.9 seconds with exactly the same server disk-space error. Neither
returned a Lean diagnostic that a source repair could address. The saved Lean
and node file were retained without modification; no delivery was pushed.

## Dispatcher retry 4, 2026-10-24

Retained the saved packet and first ran the required `deliver2.py Q06
lem-sfb-triangular-group-representation-eigenline --no-push`. It exited 1 after
2.9 seconds with `COMPILE FAILED on the server, nothing pushed` and
`resource exhausted (error code: 28, no space left on device)` for
`sandbox Sheaf.Stage2.Sandbox0`. A direct `scompile.py` retry on the saved
`TriangularRepresentationEigenline.lean` likewise exited 1 after 2.9 seconds
with the identical error. Neither invocation produced a Lean diagnostic.
The source and node record are preserved unchanged. Nothing was pushed;
compilation and preflight remain unverified because the server has no space.

## Dispatcher retry 5, 2026-10-24

Retained the saved packet and inspected its report and Lean module. The required
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`
exited 1 after 2.9 seconds with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and `resource exhausted (error code: 28, no space
left on device)`. A direct `scompile.py Q06
lem-sfb-triangular-group-representation-eigenline` retry on the saved
`lean/Sheaf/AlgebraicGeometry/TriangularRepresentationEigenline.lean` also exited
1 after 2.9 seconds with the identical server disk-space error. Neither returned
a Lean diagnostic that could guide a source repair. The Lean source and node
record remain unchanged; compilation and preflight remain unverified, and
nothing was pushed. No launcher scripts or shared repository files were edited.

## Dispatcher retry 6, 2026-10-24

Inspected the preserved report and packet, then ran the required
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`.
The dry run exited 1 after 2.9 seconds with `COMPILE FAILED on the server,
nothing pushed`, `sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)`.
A direct prescribed `scompile.py` retry on the saved module also exited 1
after 2.9 seconds with the identical server disk-space error. Neither returned
any Lean diagnostic to repair. The Lean source and node record are retained
unchanged; compilation and preflight remain unverified and nothing was pushed.
Only this sandbox report was edited; no launcher scripts or shared files changed.

## Dispatcher retry 7, 2026-10-24

Inspected the saved report and module and first ran the prescribed
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`.
It exited 1 after 2.9 seconds with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and `resource exhausted (error code: 28, no space
left on device)`. A direct `scompile.py` retry on the saved module also exited 1
after 2.9 seconds with the identical server disk-space error. Neither invocation
returned a Lean diagnostic to repair. The source and node record remain unchanged;
compilation and preflight remain unverified and nothing was pushed. Only this
sandbox report was updated; no shared sources or launcher scripts were edited.

## Dispatcher retry 8, 2026-10-24

Inspected the preserved report and Lean source and began with the prescribed
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`.
It exited 1 after 2.9 seconds with `COMPILE FAILED on the server, nothing pushed`
and `resource exhausted (error code: 28, no space left on device)` for
`sandbox Sheaf.Stage2.Sandbox0`. A direct prescribed `scompile.py` retry on the
saved module likewise exited 1 after 2.9 seconds with the same server disk-space
error. Neither invocation returned a Lean diagnostic to repair. The saved
source and node remain unchanged; compilation and preflight remain unverified,
and nothing was pushed. Only this sandbox report was updated.

## Dispatcher retry 9, 2026-10-24

Inspected the preserved report and Lean source and first ran the prescribed
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`.
It exited 1 after 2.9 seconds with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)`.
A direct prescribed `scompile.py` retry on the saved module also exited 1
after 2.9 seconds with the identical server disk-space error. Neither returned
a Lean diagnostic to repair. The saved Lean source and node record remain
unchanged; compilation and preflight remain unverified and nothing was pushed.
Only this sandbox report was updated; shared sources and launcher scripts were
not edited.

## Dispatcher retry 10, 2026-10-24

Inspected the preserved report and Lean module and first ran the prescribed
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`.
It exited 1 after 2.9 seconds with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)`.
A direct prescribed `scompile.py` retry on the saved module also exited 1
after 2.9 seconds with the identical server disk-space error. Neither returned
a Lean diagnostic to repair. The saved source and node record remain unchanged;
compilation and preflight remain unverified and nothing was pushed. Only this
sandbox report was updated; shared sources and launcher scripts were not edited.

## Dispatcher retry 11, 2026-10-24

Inspected the preserved report and Lean module and first ran the prescribed
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`.
It exited 1 after 2.9 seconds with `COMPILE FAILED on the server, nothing pushed`,
`sandbox Sheaf.Stage2.Sandbox0`, and
`resource exhausted (error code: 28, no space left on device)`.
A direct prescribed `scompile.py` retry on the saved module also exited 1
after 2.9 seconds with the identical server disk-space error. Neither returned
a Lean diagnostic to repair. The saved source and node record remain unchanged;
compilation and preflight remain unverified and nothing was pushed. Only this
sandbox report was updated; shared sources and launcher scripts were not edited.

## Successful dispatcher retry, 2026-10-24

Retained the saved Lean module and node record. The required initial
`deliver2.py Q06 lem-sfb-triangular-group-representation-eigenline --no-push`
passed: `OK (dry run): commit 470640b9c2d passes the preflight and compiles;
nothing pushed`. Both sandbox and library module compilation completed on the
server; the earlier disk-space failure no longer occurs.

The self-check reread the current item's statement, saved complete signature,
and the current CoordinateComodule, NaturalRepresentation, coordinatePoint,
genericCoaction and multiplicative-group definitions. It confirmed the
hypothesis/clause table above, the below-diagonal inequality, nonzero and
finite-dimensional hypotheses, the coaction and character equations, and the
action on every tensor in the extended line. The recorded signature matches
the file verbatim. Relative to the current repository node, the saved packet
only adds the Lean record and the two already landed statement dependencies
`lem-sfb-rational-representation-comodule-dictionary` and `def-sc-gm-ga`;
these additions cite the actual notions used, as authorized by brief-stage2
section 5. No statement correction or source change is needed. Only this
sandbox report was updated during this retry.


## New nodes

`def-sfb-rational-representation-coordinate-comodule` is a definition node with
`existing: true` on five declarations in
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`:
`AlgebraicGeometry.RationalRepresentation.CoordinateComodule`,
`NaturalRepresentation`, `genericPoint`, `coordinatePoint` and `genericCoaction`
(the latter four share the same namespace). Its source is Milne Chapter 4(a),
p.83, and the right-comodule equations (24) and Remark 4.1 on p.84. It records
the subtype of counital coassociative linear coactions; natural families of
group actions on R tensor V; the actual affine universal point; its pullback
along any coordinate-algebra map; and the generic linear map extracted from
a natural family, with tensor symmetry explicit. It asserts no equivalence.
No new Lean definition, theorem or module is introduced. Existing helpers stay
in the landed module; their docstrings still cite their original theorem node.

The new definition depends on the recorded field, group-scheme, affine-spectrum,
canonical coordinate Hopf, Hopf-action module-data and scalar-extension notions.
In particular it uses `HopfAction.Coassociative`, `HopfAction.Counital`,
`HopfAction.coordinateHopfAlgebra` and Mathlib's tensor products and Spec.
It has no dependency on the dictionary theorem. Its common universe is that of
the landed definitions. Zero V, infinite-dimensional V, trivial G, arbitrary
characteristic, nonreduced test algebras and groups not of finite type are
allowed, exactly as in those definitions. None of the helpers chooses data from
a postponed theorem.

Searches for this new node: LeanSearch with the natural-family/coaction query
in its mathlib_searches returned eight abstract-representation, group-like and
coalgebra hits; LeanFinder with the coordinate-comodule query returned eight
affine-space/coalgebra hits. Neither gives this notion. Mathlib grep for the
four consumed names returned zero hits. Direct rg over WeilConjectures found
none; rg over Sheaf found the five landed definitions and consumers (plus
unrelated private coordinate-point helpers). A scan of every definition node's
Lean record found no owner. The existing representation-gzero notion concerns
finite-dimensional Grothendieck groups, and algebraic-representations concerns
finite-dimensional scheme maps; neither supplies these general families and
generic-point definitions. `blueprint_refs.py search "coordinate comodule"`
returned zero matches; `ancestor` returned None. Actual search queries, hit
names, results and verdicts are recorded in the new node.

## Returned H2 repair, Q06

Return reviewed: immutable head 29383e6e830b. The saved Lean statement and
module are retained byte-for-byte: the maintainer found the mathematics correct.
Against current main, all original node fields except lean and stmt_deps still
match. Replaced `lem-sfb-rational-representation-comodule-dictionary` in stmt_deps
by `def-sfb-rational-representation-coordinate-comodule`, and kept the theorem
in proof_deps, where it already occurs. The new definition node owns the plain
helpers, following the explicit requested correction. `def-sc-gm-ga` stays in
stmt_deps. The statement, proof and proof_deps are unchanged, so no
statement_change is needed. The public import of the dictionary module stays
because it contains the owned definitions required by the signature.

H11 advisory: this is explicitly a self-check by Q06, not an independent
reader. The dispatcher's instruction prohibits starting another agent, so the
maintainer's independent immutable-head review supplies the independent reading.
The repair self-check reread the five full definitions and matched each clause
of the new node: group homomorphisms and naturality to the structure's action
and naturality fields, actual Spec points to genericPoint and coordinatePoint,
restriction to 1 tensor V and symmetry to genericCoaction, and exactly the two
Hopf identities to CoordinateComodule. The original hypothesis/clause table
still applies verbatim to the unchanged eigenline theorem. The H2 correction
changes declaration ownership and DAG edges, without changing any mathematical
hypothesis, conclusion or construction.
