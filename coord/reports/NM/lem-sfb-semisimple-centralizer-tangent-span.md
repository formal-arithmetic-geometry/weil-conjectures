## Worker report

Item: lem-sfb-semisimple-centralizer-tangent-span. Module:
`Sheaf.AlgebraicGeometry.SemisimpleCentralizerTangentSpan`. Main declaration:
`AlgebraicGeometry.SemisimpleCentralizerTangentSpan.tangent_span`.
The theorem has exactly one postponed proof, `sorry`. Its docstring contains all eight
accepted proof steps and all their dependency names, including the restricted-power
argument over imperfect fields. No theorem has been proved in this delivery.

The helpers are declarations of this item's own notions, authorized by the launcher brief:
`scalarExtension` abbreviates the existing pullback functor on bundled group objects;
`geometricTangentMatrix` computes the epsilon coefficient of the actual geometric tangent
point projected into G and composed with i; `IsIndex` is exactly the node's indexing predicate;
`Centralizer` packages a representative of the explicitly specified stabilizer functor.
No data is obtained by choosing from an unproved existence theorem. The structural
commutativity proof in geometricTangentMatrix uses Over.w, pullback.condition, Spec.map_comp
and the scalar tower. It contains no sorry. Centralizers are quantified existentially in
the main theorem, with their entire functor of points fixed by their inclusions.

Source read: Milne, Algebraic Groups (2017), PDF pages 389--390, printed pp.377--378,
Propositions 17.74 and 17.76--17.79. The main statement follows the reviewed DAG's
explicit faithful-representation formulation and its characteristic-p restricted-power
repair; it does not take rational Jordan parts over an imperfect field.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node text | Lean rendering |
| --- | --- |
| k a field | `{k : Type u} [Field k]` |
| k infinite | `[Infinite k]` |
| fixed algebraic closure | `{K : Type u} [Field K] [Algebra k K] [IsAlgClosure k K]` |
| affine k-group scheme G | `G : Grp (Over (Spec (.of k)))`, `[IsAffine G.X.left]` |
| finite type | `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]` |
| smooth | `[Smooth G.X.hom]` |
| geometrically connected | `[GeometricallyConnected G.X.hom]`, the existing predicate testing ConnectedSpace on all field pullbacks |
| identity tangent Lie algebra, commutator bracket | Existing `GrpObj.Lie G.X`, its canonical `LieRing`/`LieAlgebra` instances and `⁅_, _⁆` |
| faithful closed linear representation | `i : G.X ⟶ GeneralLinearGroup ι k`, `[IsMonHom i] [IsClosedImmersion i.left]` |
| n finite, including n=0 | `{ι : Type u} [Fintype ι] [DecidableEq ι]`; choosing a basis identifies this with GL_n for n=card ι |
| semisimple means di(X) diagonalizable over K | `IsIndex`: `Module.End.IsSemisimple (Matrix.toLin' ((RationalHom.differential i X).map (algebraMap k K)))`; over an algebraically closed field on a finite-dimensional vector space this is precisely diagonalizability |
| noncentral means some bracket nonzero | `IsIndex` second conjunct `∃ Y : GrpObj.Lie G.X, ⁅X,Y⁆ ≠ 0` |
| geometric noncentral semisimple element in Lie(G_K) | `hgeom` quantifies `S,T : GrpObj.Lie (scalarExtension G K).X`, asserts semisimplicity of the actual `geometricTangentMatrix`, and `⁅S,T⁆ ≠ 0` |
| C_G(X)(R)={g:Ad(g)(X tensor 1)=X tensor 1} | `Centralizer.represents` fixes the image of its inclusion on every commutative k-algebra R as the matrices commuting with `di(X)` extended entrywise to R |
| adjoint is differential of conjugation | With a faithful closed representation, `di_R(Ad(g)X)=i(g)di_R(X)i(g)^(-1)` and di_R is injective, so the preceding matrix equation is precisely the given stabilizer condition; it imposes no hypothesis on Ad or an arbitrary action |
| all subgroup schemes closed and finite type | `Centralizer.closed`, its finite-type/quasi-compact instance fields, and the conclusion's `IsClosedSubgroupScheme` for the composite inclusion |
| K_X=C_G(X)^0 with its open-subscheme structure | Existing `GrpObj.identityComponent (C X).group.X`, not a reduction or a closed reduced model |
| each K_X smooth | First conjunct of the universal conclusion, `Smooth ...hom` |
| each K_X geometrically connected | Second conjunct, `GeometricallyConnected ...hom` |
| each K_X affine and finite type | `IsAffine ...left`, `LocallyOfFiniteType ...hom`, `QuasiCompact ...hom` |
| each K_X a closed subgroup of G | `IsClosedSubgroupScheme (GrpObj.identityComponentι ... ≫ (C X).inclusion)` |
| strict dimension drop | `topologicalKrullDim ...left < topologicalKrullDim G.X.left` in WithBot ENat |
| tangent subspace is {Y:[Y,X]=0} | `Set.range (GrpObj.differential (identityComponentι ... ≫ inclusion)) = {Y : GrpObj.Lie G.X | ⁅Y,X.val⁆ = 0}` |
| these subspaces span g over k | The supremum in `Submodule k (GrpObj.Lie G.X)` of the actual differential-image submodules is `⊤`; supremum of subspaces is their k-linear span |
| rational indexing set nonempty | Final conjunct `Nonempty {X : GrpObj.Lie G.X // IsIndex (K := K) i X}` |
| no perfectness or characteristic hypothesis | No PerfectRing, CharZero, CharP, algebraic-closedness of k, or restriction on characteristic occurs |

Use of dependency declarations:

- `def-weil-field`: Mathlib `Field`, read in `Mathlib.Algebra.Field.Defs`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, bundled as `CategoryTheory.Grp`;
  `Mathlib.CategoryTheory.Monoidal.Grp` and upstream GroupScheme.Defs.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in the recorded Mathlib morphism modules.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme` and its
  inherited `IsSubgroupScheme`/`IsMonHom`, from the recorded upstream GroupScheme.Defs.
- `def-sbc-smooth-morphisms`: Mathlib `AlgebraicGeometry.Smooth`.
- `def-weil-connected-scheme`: Mathlib `ConnectedSpace`; geometric testing is the existing
  `AlgebraicGeometry.GeometricallyConnected` from Mathlib.AlgebraicGeometry.Geometrically.Connected.
- `def-weil-algebraic-closure`: existing `IsAlgClosure` from Mathlib.FieldTheory.IsAlgClosed.Basic,
  imported through the recorded AlgebraicClosure module.
- `def-sc-scheme-tangent-space`: the recorded upstream `schemeTangentSpace` module is public;
  the canonical group-tangent realization is existing `GrpObj.Lie`/`lieEquivTangent`, not a
  copied tangent definition. The existing `GrpObj.lieIdentityTangentEquiv` signature and
  docstring were also read to check the identification with the scheme tangent space.
- `def-wf-lie-algebra`: Mathlib `LieRing`/`LieAlgebra`, with the group-commutator instances
  in upstream GroupScheme.Lie.Bracket.
- `def-sc-general-linear-group`: the record's owning module LinearGroupSchemes is public;
  as its note requires, GL itself uses upstream `GeneralLinearGroup`, `homMulEquiv`,
  `RationalHom.points`, `RationalHom.differential` from GroupScheme.GeneralLinear.Lie.
- `def-weil-closed-immersion`: Mathlib `AlgebraicGeometry.IsClosedImmersion`.
- `def-kun-topological-krull-dimension`: Mathlib `topologicalKrullDim`.
- Added statement dependencies on the already landed owning nodes
  `def-wf-lie-algebra-derivation` and `def-wf-algebraic-components`: these record the exact
  existing `GrpObj.Lie`, bracket, `lieEquivTangent`, and `GrpObj.identityComponent` APIs used.
  No new notions or dependency module repairs are necessary.

Stated proof dependencies imported without `public`: AffineGroupDualNumberCalculus,
GroupScheme.LieLocalDimension, GroupScheme.IdentityLocalDimension, OpenImmersion.
The connected-rational-point lemma is already imported publicly by upstream GroupScheme.Basic;
the open-immersion/smooth-composition leaves are already in Mathlib's Smooth module.
The other proof-dependency nodes currently have no Lean record and introduce no objects
needed by this statement, so there is no module to import for them yet.

Edge cases checked before and after drafting:

- Dimension zero/empty ι is permitted. GL_0 is trivial and the geometric noncentral hypothesis
  then cannot hold. No nonemptiness binder on ι silently excludes that case.
- X=0 is semisimple but cannot be an index because noncentrality fails; central tangent
  elements are similarly excluded. This is exactly the node's index set.
- A commutative G cannot satisfy hgeom. The theorem does not falsely produce indices there.
- An empty rational indexing set is not assumed away: hgeom is geometric and the final
  Nonempty conclusion asserts the required rational descent.
- Characteristic p, imperfect infinite k, and nonreduced test algebras R are all allowed.
  In particular, no perfectness inference or restriction to field-valued centralizer points
  is hidden in represents.
- Identity components are the open-subscheme construction, so nilpotent structure is retained.
  The dimension is topologicalKrullDim, including its full WithBot ENat codomain.
- All objects/test algebras live in the common project universe u; ι is an arbitrary finite
  type in that universe. There is no independent smaller testing universe making a universal
  condition vacuous, and no extra equality between independently specified universes.

Searches performed via the prescribed msearch.py wrapper:

1. leanfinder: `Centralizers of rational noncentral semisimple tangent vectors span the Lie algebra of a smooth geometrically connected affine algebraic group over an infinite field`.
   Eight hits (regular elements, Engel/Cartan existence, characteristic-zero radical/weight
   results), none the scheme-theoretic centralizer spanning theorem.
2. loogle: `"centralizer", "span"`: zero hits.
3. grep of Mathlib: `semisimple.*centralizer|centralizer.*span|centralizer.*semisimple`:
   zero hits.
4. leansearch: `Lie algebra centralizers of noncentral semisimple elements span over an infinite field`:
   eight hits (abstract subalgebra centralizers, Lie center, span_univ, semisimple Lie algebras),
   none this assertion.
5. Mathlib matrix API grep: `baseChange|tensorProduct` under LinearAlgebra/Matrix:
   five Kronecker/tensor imports, no alternative construction needed.
6. rg in project `lean/WeilConjectures` and `lean/Sheaf` for the item id and
   `semisimple.*centralizer|centralizer.*span`, and wider case-insensitive concept searches:
   found matrix-subgroup centralizer calculations and torus semisimple-point centralizers,
   but no existing statement of this theorem. Read the relevant upstream GeneralLinear.Lie
   and GroupScheme.Basic rather than introducing private copies.
7. Searched exact proposed namespace/helper names in Mathlib/upstream/project name records:
   no clash. Read the existing Mathlib Module.End.IsSemisimple definition and its finite-dimensional
   algebraically-closed eigenspace-spanning characterization.

No STATEMENT-DISPUTED issue, statement correction, new DAG node, or dependency-module repair.
Only the item's lean record and the two additional existing-interface stmt_deps are changed.

Validation: scompile.py compiled the file cleanly against the current server sources after
removing the initial long-line warning. A transient server overlay disk-space error was
handled by scompile.py's own fallback; the confirming per-file compilation returned success
with no Lean warnings or errors (AffineGroupDualNumberCalculus 7.5 s, item module 4.5 s).

## Second reading by NM

The dispatcher expressly forbids starting other agents; this is a second pass by the same
worker, with independent review reserved for the maintainer as the brief states.
Re-read the node and final file together, including each helper body and the exact signature.
The table above accounts for every hypothesis and conclusion. In particular checked that
hgeom quantifies actual Lie(G_K) vectors; noncentrality uses its genuine commutator bracket;
scalar extension is the existing pullback group object; all test algebras (including dual
numbers) occur in represents; K is the existing open identity component; the range equality
is inside Lie(G); and the supremum is of those actual differential images over precisely
all rational noncentral semisimple indices. No mismatch was found in this second pass.


## Dispatcher retry, 2026-10-24

Retained the saved module and node. Rechecked the current node against the packet:
only `lean` and the two reported existing-interface `stmt_deps` additions differ.
The theorem signature agrees verbatim with `lean.statement`; the file has explicit
universes, `autoImplicit false`, no lines exceeding 100 characters and exactly one
postponed theorem proof. The node JSON has the required serialization. No repair
note is present for this item.

The required initial `deliver2.py NM lem-sfb-semisimple-centralizer-tangent-span
--no-push` failed during server compilation before Lean checking. Then ran
`scompile.py NM lem-sfb-semisimple-centralizer-tangent-span` on the saved module,
followed by a second identical dry run. All three calls failed with the same
server error: `sandbox Sheaf.Stage2.Sandbox0`, then
`resource exhausted (error code: 28, no space left on device)` (7.3 s each).
No Lean diagnostic was produced and nothing was pushed. The saved work remains
intact; server disk exhaustion prevents the required compile and delivery gates.

## Further dispatcher retry, 2026-10-24

Inspected the saved report and retained the existing packet. Ran the prescribed initial
`deliver2.py NM lem-sfb-semisimple-centralizer-tangent-span --no-push`, then a direct
`scompile.py` of the saved module, then a second identical dry run. All three again
failed before Lean checking with `sandbox Sheaf.Stage2.Sandbox0` followed by
`resource exhausted (error code: 28, no space left on device)` (7.3 s each).
The wrappers were used unchanged; no server files were edited and nothing was pushed.

Repeated the saved-packet checks against the current read clone: only `lean` and
the two documented additions to `stmt_deps` differ; the recorded theorem signature
matches the module verbatim, there are no lines over 100 characters, the only
`sorry` is the main theorem proof, and the JSON serialization is exact. There is
no repair note for this item. The Lean and node files remain unchanged because
these failures supply no Lean diagnostic to repair.

## Saved-packet retry, 2026-10-24

Retained the saved packet and ran the required initial dry run before investigating.
The initial `deliver2.py --no-push`, direct `scompile.py` of the saved module,
and confirming `deliver2.py --no-push` all failed before Lean checking with:
`sandbox Sheaf.Stage2.Sandbox0` and
`resource exhausted (error code: 28, no space left on device)` (7.3 s each).
There was no compiler diagnostic to repair. The wrappers were used unchanged;
no server files were edited, and nothing was pushed.

Rechecked against the current read clone: the only changed node fields are `lean`
and the two documented additions to `stmt_deps`; no dependency was removed.
The signature still matches `lean.statement` verbatim, the JSON serialization is
exact, every line is at most 100 characters, and the only postponed proof is the
main theorem. No repair note is present. The Lean module and node remain intact.

## Current dispatcher retry, 2026-10-24

Read the saved packet first and ran the prescribed initial dry run unchanged.
The initial `deliver2.py NM lem-sfb-semisimple-centralizer-tangent-span --no-push`,
a direct `scompile.py` of the saved module, and the confirming identical dry run
all failed before Lean checking with `sandbox Sheaf.Stage2.Sandbox0` followed by
`resource exhausted (error code: 28, no space left on device)` (7.3 s each).
The delivery wrapper reported nothing pushed. No Lean diagnostic was available
to repair, and no launcher scripts or server files were changed.

The saved module and node are retained. Checked against the current read clone:
only `lean` and the two documented existing-interface additions to `stmt_deps`
differ; no dependency was removed. The theorem signature matches `lean.statement`
verbatim, JSON serialization is exact, every source line is at most 100 characters,
and the sole `sorry` is the main theorem proof. No repair note exists for this item.

## Saved-packet confirmation, 2026-10-24

Read the saved report and ran the required initial dry run. The initial
`deliver2.py NM lem-sfb-semisimple-centralizer-tangent-span --no-push`, direct
`scompile.py` of the saved module, and confirming dry run each failed before
Lean checking with `sandbox Sheaf.Stage2.Sandbox0` followed by
`resource exhausted (error code: 28, no space left on device)` (7.3 s each).
No Lean diagnostic was produced, and nothing was pushed. The prescribed wrappers
were used unchanged; no server files or launcher scripts were edited.

Retained the saved Lean module and node. Compared the packet with the current
read clone: only `lean` and the two already documented additions to `stmt_deps`
differ, with no removed dependencies. The theorem signature matches the record
verbatim; JSON serialization is exact; no source line exceeds 100 characters;
the sole `sorry` is the main theorem proof. No repair note is present. Server
disk exhaustion still prevents the required compilation and delivery gates.

## Successful saved-packet retry, 2026-10-24

Retained the saved Lean module and node. The required initial dry run failed
before Lean checking with server disk exhaustion, but the following direct
`scompile.py` succeeded (sandbox 3.5 s, item module 3.8 s). The confirming
`deliver2.py --no-push` passed preflight and compilation: `OK (dry run)`,
commit `410456e8072`. The server disk failure has cleared.

Repeated the packet self-check: the theorem signature matches `lean.statement`
verbatim (including its named-argument `:=` syntax), JSON serialization is exact,
all variables and universes are explicit, no line exceeds 100 characters, and
the sole postponed proof is the main theorem. The current read-clone node
differs only in `lean` and the two documented existing-interface additions to
`stmt_deps`, with none removed. No repair note is present. Re-read the full
module against the node statement and the clause table above; the geometric
noncentral hypothesis, rational index set, stabilizer functor on all test
algebras, actual open identity components, differential images, dimension
drop, spanning, and nonemptiness are retained without additional field
hypotheses. No Lean or node changes were required.
