## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.UnipotentRadicalExistence` states
`AlgebraicGeometry.exists_unipotent_radical`, with its proof postponed by `sorry`.
It introduces no definitions. Only the item's `lean` record is changed.

The source was read directly in Milne, Algebraic Groups, printed pp.134--136
(PDF pp.146--148), especially Proposition 6.42 and Section 6.46. Section 6(h)
assumes affine algebraic groups. Section 6.46 asserts precisely the largest
connected normal unipotent subgroup variety; the node specializes to an
algebraically closed field and spells out smoothness and the matrix definition.

Hypotheses and clauses, in order:

- The field F is `{F : Type u} [Field F] [IsAlgClosed F]`. No characteristic
  restriction or extra perfect-field hypothesis is imposed.
- H is a group scheme over F: `H : Grp (Over (Spec (.of F)))` bundles its group
  object structure, following `def-sc-group-scheme`.
- H is affine and of finite type: `hH : SolvableGroupStructure.IsAlgebraic H`.
  The recorded dependency definition expands to
  `IsAffine H.X.left ∧ LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom`.
- H is smooth and connected: `hsm : Smooth H.X.hom` and
  `hc : ConnectedSpace H.X.left`, using the recorded dependency notions.
- Existence is `∃ (U : Grp (Over (Spec (.of F)))) (i : U ⟶ H), ...`.
  The map i is a homomorphism of group schemes, not an arbitrary scheme map.
- U is smooth and connected: `Smooth U.X.hom ∧ ConnectedSpace U.X.left`.
- U is closed and normal in H: `IsClosedSubgroupScheme i.hom.hom` and
  `IsNormalSubgroupScheme i.hom.hom`. These use all algebra-valued points,
  not merely F-points. Their subgroup maps are injective on all test algebras.
- U is unipotent: `SolvableGroupStructure.IsUnipotent U`. Its existing
  definition requires smoothness and an integer n and a closed faithful
  representation in GL_n, followed by the nilpotence condition `(r(x)-1)^N=0`
  with `0<N` for every point over every algebraically closed extension field.
  This dependency is used verbatim, without a private replacement.
- Greatestness quantifies over every V and every homomorphism `j : V ⟶ H`
  satisfying the same five subgroup properties. Its conclusion
  `∃ f : V ⟶ U, f ≫ i = j` is scheme-theoretic subgroup containment. A map
  between closed subschemes of H factoring their closed embeddings is itself
  a closed immersion: affine-locally it is the surjection between the
  corresponding quotient rings. Thus no pointwise-only containment is used.
  There is no additional algebraicity assumption on a competitor: any closed
  subscheme of the affine finite-type H is automatically affine finite type.
  The same observation supplies these implicit properties of U.
- Uniqueness as a closed subgroup scheme is the last universal clause. For
  any V,j with those properties and with the same greatestness property,
  it asserts `∃ e : V ≅ U, e.hom ≫ i = j`. This is equality of the embedded
  closed subgroup schemes, permitting different bundled representatives.
  There cannot be two such maps e.hom because i is a closed immersion and
  hence a monomorphism. No equality of arbitrarily chosen representatives
  of an isomorphism class is demanded.
- The name unipotent radical is in the theorem's name and docstring; no
  arbitrary subgroup is selected as the data of a new definition.
- The H=1 case is retained by universal quantification over H. Taking the
  trivial candidate V=H with j the identity in greatestness gives a right
  inverse of i. Since i is a monomorphism it is an isomorphism, so U=H=1
  as closed subgroup schemes. No nontriviality hypothesis excludes this case.

Dependency declarations used (their definitions and full signatures were read):

- `Mathlib.Algebra.Field.Defs`: `Field`, for def-weil-field.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, for the algebraically
  closed part of def-weil-algebraic-closure (whose mathlib_match explicitly
  records this declaration in addition to AlgebraicClosure).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and the bundled
  `CategoryTheory.Grp`, for def-sc-group-scheme.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`, used through IsAlgebraic as recorded by
  def-weil-finite-type-morphism.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  for def-sbc-smooth-morphisms.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, for
  def-weil-connected-scheme; this explicitly includes nonemptiness.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`, and
  `IsNormalSubgroupScheme`, for def-sc-group-scheme-subgroup.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsAlgebraic` and `IsUnipotent`,
  for def-sfb-solvable-group-structure.
- Proof-only import: `Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus`,
  declaration `AlgebraicGeometry.perfect_solvable_unipotent_torus`.
  The current records of lem-sfb-smooth-unipotent-solvable and
  lem-sfb-solvable-normal-subgroup-products have no Lean declarations, so
  there are no proof modules for them to import yet. Their proof roles are
  retained explicitly in the theorem's five-step docstring.

Edge cases checked before drafting: the trivial ambient group and trivial
candidate; zero-dimensional smooth connected groups over an algebraically closed
field (necessarily trivial); positive characteristic as well as characteristic
zero; the exclusion of the empty scheme by ConnectedSpace; distinct bundled
presentations of the same closed subgroup; and geometric rather than merely
rational matrix unipotence. Universe u is explicit throughout, with the same
universe for the field, group schemes and all test algebras/extensions, following
the recorded dependencies. There are no auto-bound implicit variables.

Searches performed for an existing statement:

- msearch.py, leanfinder: "Every smooth connected affine algebraic group over an
  algebraically closed field has a largest smooth connected closed normal
  unipotent subgroup scheme". Eight hits concerned abstract/topological groups,
  such as Group.IsVirtuallyNilpotent, Subgroup.connectedComponentOfOne and
  upperCentralSeriesAux. None is the group-scheme theorem.
- msearch.py, loogle: `"unipotent"`. Six hits, exclusively the upper/lower
  unipotent biproduct isomorphisms and their components; no match.
- msearch.py, grep: `unipotentRadical|unipotent_radical|[Uu]nipotent` in
  Mathlib/AlgebraicGeometry. Zero hits.
- msearch.py, leansearch: "Existence and uniqueness of the largest smooth
  connected closed normal unipotent subgroup scheme of a smooth connected
  affine algebraic group over an algebraically closed field". Eight hits,
  including Subgroup.normalCore_eq_iSup, abstract subgroup normality, and Lie
  algebra nilpotent ideals; none gives algebraic subgroup-scheme existence.
- rg in lean/WeilConjectures and lean/Sheaf for
  `unipotentRadical|unipotent_radical|[Uu]nipotent`, then for the item id.
  The unipotence notion and solvable perfect-field structure theorem exist and
  are reused. Other modules mention this item in their proof plans, but no
  declaration states its existence theorem.
- rg of Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  `exists_unipotent_radical`: no existing declaration of the proposed name.

The full natural-language proof in the docstring follows each of the node's
five steps, including fppf-local product closure and the dimension argument.
There are no statement corrections, missing definitions, or disputed claims.

Validation: the first scompile.py attempt encountered a disk-space failure.
On retry, its initial server compiler again reported OSError(28), after which the wrapper
confirmed the module against current server sources: exit status 0, 2.0 seconds,
nice 19, two threads, 60-second limit, no errors or warnings. The sandbox record's
signature was checked verbatim against the source; only `lean` differs from the
base node, and every Lean line is at most 88 characters. No shared source,
compiler artifact, or launcher tool was edited. The prescribed dry run follows.

Delivery tooling outcome: two `deliver2.py --no-push` attempts both failed in
its prescribed compile step with `resource exhausted (error code: 28, no space
left on device)`, including a retry after a pause. Thus preflight was not
reached and nothing was pushed. This is a compile-service storage failure;
the source has already passed the wrapper's current-server-source fallback
once, but a clean dry run remains required. No launcher script or unrelated
storage was modified to work around the failure.

Retry handoff (2026-10-24 10:30 UTC): inspected the saved report and module, and confirmed that the saved node differs from the current shared node only in `lean`. Ran the required saved-packet `deliver2.py Q16 lem-sfb-unipotent-radical-existence --no-push` twice. Both attempts exited 1 at server compilation of `Sheaf.Stage2.Sandbox0`, with `resource exhausted (error code: 28, no space left on device)` (2.1 seconds each). Preflight was not reached and nothing was pushed. The existing packet is retained unchanged apart from this report entry; server storage remains the blocking tool failure.

Retry handoff (2026-10-24 10:33 UTC): inspected the retained packet and ran the
required saved-packet dry run, then retried after the packet self-check. Both
`deliver2.py Q16 lem-sfb-unipotent-radical-existence --no-push` attempts exited 1
at server compilation of `Sheaf.Stage2.Sandbox0` in 2.1 seconds with
`resource exhausted (error code: 28, no space left on device)`. The node still
differs from the current shared node only in `lean`; its recorded signature
matches the source verbatim, the module-mode header is present, the maximum
line width is 88, and the only proof is the single expected `sorry`. Current
statement-dependency records were checked and no released repair note exists.
No module or node was changed. Preflight was not reached; nothing was pushed.
The compile-service storage failure prevents the required clean dry run.

Retry handoff (2026-10-24 10:38 UTC): inspected the saved report, module and current
node/dependency records, then ran the required saved-packet dry run and one
retry. Both `deliver2.py Q16 lem-sfb-unipotent-radical-existence --no-push`
attempts exited 1 during server compilation of `Sheaf.Stage2.Sandbox0`
with `resource exhausted (error code: 28, no space left on device)`
(2.1 seconds each). The saved node differs from the current shared node only
in `lean`; its recorded signature matches the source verbatim, the module
header is present, the maximum line width is 88, and the only proof is the
expected single `sorry`. No released repair note exists. No Lean module or
node was changed. Preflight was not reached and nothing was pushed. The
compile-service storage failure still prevents the required clean dry run;
no shared source, compiler storage or launcher tool was modified.

Retry handoff (2026-10-24 10:42 UTC): inspected the retained report and module, ran the
required saved-packet dry run, checked the packet against current shared records,
and retried the dry run. Both deliver2.py --no-push attempts exited 1 at
server compilation of Sheaf.Stage2.Sandbox0 with
`resource exhausted (error code: 28, no space left on device)` (2.1 seconds each).
Only lean differs from the shared node; the recorded signature matches the
source verbatim, autoImplicit is false, maximum line length is 88, and the
module contains only the expected single sorry. No repair note exists.
No Lean source or node was changed. Preflight was not reached; nothing was
pushed. The prescribed delivery remains blocked by compile-server storage.

Retry handoff (2026-10-24 10:45 UTC): inspected the retained report and module, ran the
required saved-packet dry run, checked the packet against current shared records,
and retried the dry run. Both deliver2.py --no-push attempts exited 1 during
server compilation of Sheaf.Stage2.Sandbox0 with
`resource exhausted (error code: 28, no space left on device)` (2.1 seconds each).
Only lean differs from the current shared node; the recorded signature matches
the module verbatim, module mode and explicit autoImplicit false are present,
the maximum line width is 88, and the only proof is the expected single sorry.
Current statement-dependency records were checked; no repair note exists.
No Lean module or node was changed. Preflight was not reached; nothing was
pushed. The packet is retained; the compile-service storage failure prevents
the required clean dry run. No shared source, compiler storage or launcher
tool was modified.

Retry handoff (2026-10-24 10:48 UTC): inspected the saved report and ran the required
saved-packet dry run, checked the packet against current shared records, and
retried once. Both `deliver2.py Q16 lem-sfb-unipotent-radical-existence
--no-push` attempts exited 1 during server compilation of
`Sheaf.Stage2.Sandbox0` with `resource exhausted (error code: 28, no space
left on device)` (2.1 seconds each). Only `lean` differs from the current shared
node. Its signature matches the source verbatim before the `:=` delimiter;
module mode, explicit autoImplicit false, maximum line width 88 and the single
expected sorry are retained. Current statement-dependency records were checked;
no repair note exists. No Lean module or node was changed. Preflight was not
reached and nothing was pushed. The compile-service storage failure prevents
the required clean dry run. No shared source, compiler storage or launcher
tool was modified.

Retry handoff (2026-10-24 10:52 UTC): inspected the retained report and ran the
required saved-packet dry run, checked the packet against current shared records,
and retried once. Both `deliver2.py Q16 lem-sfb-unipotent-radical-existence
--no-push` attempts exited 1 during server compilation of
`Sheaf.Stage2.Sandbox0` with `resource exhausted (error code: 28, no space
left on device)` (2.1 seconds each). Only `lean` differs from the current shared
node; the recorded signature matches the source verbatim. Module mode,
explicit autoImplicit false, maximum line width 88, and the single expected
sorry remain present. Current statement-dependency records were checked;
no repair note exists. No Lean module or node was changed. Preflight was not
reached; nothing was pushed. The packet is retained. Compile-server storage
prevents the required clean dry run; no shared source, compiler storage or
launcher tool was modified.

Retry handoff (2026-10-24 10:57 UTC): inspected the saved report and module and ran the
required saved-packet dry run, then retried once after checking the packet
against current shared node and statement-dependency records. Both
`deliver2.py Q16 lem-sfb-unipotent-radical-existence --no-push` attempts exited 1
at server compilation of `Sheaf.Stage2.Sandbox0` with
`resource exhausted (error code: 28, no space left on device)` (2.1 seconds each).
Only `lean` differs from the current shared node; the recorded signature is
verbatim, autoImplicit is false, maximum line width is 88, and the only proof
is the expected single sorry. No repair note exists. No Lean module or node
was changed. Preflight was not reached and nothing was pushed. The retained
packet needs a clean dry run once server storage is repaired; no shared source,
compiler storage or launcher tool was modified.

Successful retry (2026-10-24 11:00 UTC): the required saved-packet
`deliver2.py Q16 lem-sfb-unipotent-radical-existence --no-push` passed
server preflight and both sandbox and library compilation, producing dry-run
commit `6a6467fa012`. The previous storage failure did not recur. The retained
module and node are unchanged. Self-check against current shared records
confirms only `lean` differs, the signature is verbatim, autoImplicit is false,
the maximum line width is 88, and the single postponed proof is `sorry`.
Current statement and proof dependency records still match the imports
described above; no released repair note exists. All hypotheses, greatestness
and uniqueness clauses, and the trivial-group case were re-read against
the node. No source or node repair was needed. Independent mathematical
review remains with the maintainer as specified by the dispatcher brief.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
