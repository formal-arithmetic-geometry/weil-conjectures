## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CommutativePTorsionVectorWoundFactor`
states `AlgebraicGeometry.VectorWoundFactor.commutative_p_torsion_vector_wound_factor`.
Its three Prop-valued helper definitions expand the decomposition and the universal
property, with real defining expressions and no postponed data. The theorem alone
has `sorry`; its docstring contains all seven proof steps of the node.

The source was read online at https://math.stanford.edu/~conrad/papers/appbnew.pdf:
Definition 2.1, printed p.10, Theorem 2.6 and its proof, printed pp.12--13,
and Corollary 2.7 and the preceding nonuniqueness remark, printed p.13.
These agree with the node. No statement correction or statement dispute is needed.

Hypotheses and clauses:

- `k : Type u`, `[Field k]`, `p : ℕ`, `[Fact p.Prime]`, `[CharP k p]`
  give a field of prime positive characteristic. There is no perfectness assumption.
- `H : Grp (Over (Spec (.of k)))` is a group scheme over precisely that field.
  `[IsAffine H.X.left]`, `[LocallyOfFiniteType H.X.hom]`, and
  `[QuasiCompact H.X.hom]` give affine finite type. `[Smooth H.X.hom]`,
  `[ConnectedSpace H.X.left]`, and `[IsCommMonObj H.X]` give the three
  stated properties. ConnectedSpace includes nonemptiness.
- `hp` quantifies over every commutative k-algebra R and every R-valued section,
  and asserts `x ^ p = 1`. Group-object Hom uses multiplicative notation,
  so this is exactly the sum-of-p-copies condition, not a geometric-points test.
  Test rings are in the same universe as k and schemes, not a smaller independent
  universe; in particular their affine coordinate algebras occur among the tests.
- `K : Type u`, `[Field K]`, `[Algebra k K]`, `[IsSepClosure k K]` specify the
  fixed separable closure. This is separable algebraic closure, not algebraic
  closure and not perfection. A separable closure admits a model in the field's
  universe, as does the library's standard scalar-extension interface.
- The conclusion supplies actual group schemes V,W and group homomorphisms i,j
  into H. `IsDecomposition K i j` asserts both inclusions are closed subgroup
  schemes, both sources are affine finite type, smooth and connected.
- Its `IsIso ((fst ... ≫ i.hom.hom) * (snd ... ≫ j.hom.hom))` says exactly that
  multiplication from V times W to H is an isomorphism over k. This is an
  isomorphism in Over, with the product computed by its Cartesian tensor.
  Since H is commutative and i,j are group maps, this multiplication is a group
  map; an inverse to a bijective group-object morphism is automatically a group
  map. Thus this expresses the required group-scheme isomorphism without
  specifying any different or arbitrary isomorphism.
- The next conjunct supplies `d : ℕ` and an isomorphism of group objects
  `V ≅ ∏ᶜ (fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k))`.
  This uses the existing additive group and its coordinatewise product law.
  The integer d is bound inside the decomposition predicate, hence witnesses
  the existential d in the node; no positive-dimension restriction is imposed.
- `IsWoundGroup ((MultiplicativeType.baseChange (K := K)).obj W)` is woundness
  after the specified separable scalar extension with its pulled-back group law.
  Woundness tests *all scheme maps* from the affine line, not only group maps.
- `IsGeneratedByPointedLines ((...baseChange...).map i)` first requires
  every pointed affine-line scheme map into H_K to factor through V_K.
  Its minimality clause quantifies over every closed subgroup J -> H_K and
  requires a group-scheme map V_K -> J commuting with the inclusions whenever
  J contains every such affine-line map. Closedness of V_K follows from the
  already asserted closedness of i and base change. No merely pointwise
  generation or Zariski closure of rational points is substituted.
- `ContainsPointedLines` uses the identity point of the recorded additive group
  as its zero and requires its composite with f to equal the identity of H.
  The factorization g is an arbitrary scheme map, as f need not be a homomorphism.
- Uniqueness quantifies over every alternative V',W',i',j' with the same
  decomposition conditions and returns `e : V ≅ V'` with `e.hom ≫ i' = i`.
  This is equality of embedded subgroup schemes, stronger than mere abstract
  isomorphism in exactly the way intended by uniqueness of the subgroup.
- `Nonempty (V ≅ Grp.trivial ...) ↔ IsWoundGroup H` is the V=1 criterion.
  For a closed subgroup inclusion the trivial source has necessarily the
  identity section as its inclusion, so this means the identity subgroup.
- No uniqueness of W is asserted. The source's 'need not be unique' is permission
  for different complements, not a claim that every group has two complements.
  The proof docstring records the graph-of-W-to-V explanation.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs (def-weil-field).
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, `CategoryTheory.IsCommMonObj`,
  `CategoryTheory.IsMonHom`, and `CategoryTheory.Hom.group`, through the
  existing Mathlib Cartesian group-object framework (def-sc-group-scheme).
- `AlgebraicGeometry.IsClosedSubgroupScheme` from
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (def-sc-group-scheme-subgroup).
  The full signature and its injectivity-on-every-algebra parent were read.
- `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact
  (def-weil-finite-type-morphism); finite type is their conjunction.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth
  (def-sbc-smooth-morphisms), and `ConnectedSpace`, Mathlib.Topology.Connected.Basic
  (def-weil-connected-scheme).
- `AlgebraicGeometry.StandardGroupSchemes.additive` and `.additiveGroup`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes (def-sc-gm-ga). Its coordinate
  maps are the recorded primitive comultiplication, evaluation at zero and negation.
- `AlgebraicGeometry.Spec`, `.Spec.map`, Mathlib.AlgebraicGeometry.Scheme,
  and `Polynomial`, Mathlib.Algebra.Polynomial.Basic
  (def-weil-affine-spectrum and def-weil-polynomial-ring).
- `AlgebraicGeometry.SolvableGroupStructure.IsAlgebraic` and `.IsUnipotent`,
  Sheaf.AlgebraicGeometry.SolvableGroupStructure (def-sfb-solvable-group-structure).
  The latter is smoothness plus a closed embedding in GL_n with all geometric
  matrices unipotent, exactly the node's intended geometric definition.
- `AlgebraicGeometry.MultiplicativeType.baseChange`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType (def-sfb-tori-multiplicative-type),
  is `(Over.pullback (Spec.map ...)).mapGrp`, not an arbitrary scalar extension.
- `IsSepClosure`, Mathlib.FieldTheory.IsSepClosed; the public upstream module
  WeilConjectures.Mathlib.FieldTheory.IsSepClosed for def-pd-separable-closure
  documents this class and supplies `IsSepClosure.exists_intermediateField_mem`.
- The sole already-stated proof-only dependency is
  `AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Noetherian (pqf-lem-lft-fp-locnoeth), imported plainly.
  The three statement-only group-theory proof dependencies have no Lean records
  or mathlib matches, so no invented imports or premature restatements are added.

The original nine statement dependency nodes are retained. Added citations are
one new woundness node and the three already-landed terminology nodes for
unipotence, scalar extension and separable closure. No dependency record is repaired.

Edge cases checked before writing: trivial H, d=0 (Fin 0 and its empty categorical
product), wound nontrivial H (V trivial), a positive vector group (W trivial),
imperfect k, and k already separably closed (K=k). The empty scheme is not an
admissible group scheme: it has no identity point. Nonreduced test algebras remain
among the p-torsion tests, and closed subgroup generation is scheme-theoretic.
The alternative-complement quantifier permits graph complements and does not
impose equality of W. The source's Rosenlicht wound subgroup illustrates why
perfectness and a linearity condition on vector-group isomorphisms must be absent.

Searches made with the required wrapper (full records in searches.jsonl):

- LeanFinder: 'Smooth connected commutative algebraic group killed by p has a unique
  vector subgroup and wound complement' returned abstract primary components,
  p-groups and formal smoothness, not this algebraic-group statement.
- Loogle: '"Unipotent", "Group"' returned no hits.
- Mathlib grep: 'wound|vectorGroup|IsUnipotent' in AlgebraicGeometry returned no hits.
- LeanSearch: 'A wound unipotent group is a smooth connected unipotent group for
  which all morphisms from the affine line are constant' returned formal
  unramifiedness and uniform-group declarations, not woundness.
- LeanFinder: 'A wound unipotent algebraic group has only constant morphisms from
  the affine line' returned terminal schemes, formal unramifiedness and affine
  space declarations, not woundness.
- Mathlib grep: 'wound|IsWound' returned only an English 'un-wound' comment.
- Direct rg searches of lean/WeilConjectures and lean/Sheaf for woundness,
  vector powers, unipotence and scalar extension found the reusable modules
  listed above, but no existing woundness declaration or this theorem.
  The exact item-id search of lean/WeilConjectures found no declaration.
- DAG rg for woundness found statements mentioning it but no definition node;
  `tools/blueprint_refs.py search wound` returned zero blueprint nodes.
  `tools/blueprint_refs.py ancestor` returned None, as recorded in the item's
  existing blueprint ancestry. The new definition retains that ancestry and via.

Validation: scompile.py compiled both files separately in dependency order on
current server sources, each under four seconds. The first probe exposed the
missing scoped MonObj instances; adding `open scoped MonObj` fixed it.
The compiler wrapper reported ENOSPC in its preliminary path, and its
authorized server confirmation succeeded. Only the expected theorem-uses-sorry warning is allowed.
The first deliver2.py preflight caught a signature-record extraction stopping at
the named argument `K := K`; the record now contains the entire signature.
Two subsequent deliver2.py --no-push attempts failed identically at sandbox
Sheaf.Stage2.Sandbox1 with `resource exhausted (error code: 28, no space left on
device)` after the wound-definition overlay and preliminary compiles succeeded.
The earlier two-file scompile and the first dry-run compile both passed; the
remaining failure is compiler infrastructure storage, not a Lean diagnostic.
No tool, cache or shared file was edited to work around it. No push occurred.
Final delivery validation is run with deliver2.py; no local global build or
read-only source edit was made. Independent review belongs to the maintainer;
no independent second-reading section is claimed by this worker.

Recovery attempt on 2026-10-24: retained the saved packet and ran the prescribed
`deliver2.py Q73 lem-sfb-commutative-p-torsion-vector-wound-factor --no-push`
before making changes. It again compiled the private overlay, preliminary,
sandbox and library checks of the wound definition, then failed compiling
`Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
This is the same server-storage failure as the preceding attempts, with no
Lean elaboration diagnostic to repair. No shared storage or launcher tool
was changed. The final unchanged-packet retry failed identically at
`Sheaf.Stage2.Sandbox1` with error code 28 after the four wound-definition
checks passed. Neither recovery dry run pushed a delivery.

## New nodes

`def-sfb-wound-unipotent-group` defines
`AlgebraicGeometry.IsWoundGroup` in
`Sheaf.AlgebraicGeometry.GroupScheme.Wound`, following Conrad Definition 2.1,
printed p.10 (and Remark 2.3 for the characteristic-zero convention). It conjoins
existing affine-algebraic, smooth-geometric-unipotence and connectedness predicates
with the requirement that every affine-line scheme map factors through a rational
point of G. Each notion used is cited in its stmt_deps. No arbitrary data are chosen
and no proof is postponed. The three search kinds above found no existing notion;
project and DAG searches likewise found no definition. This node is needed by
the wound complement and the trivial-vector-factor criterion, and is directly
cited by the item. No new scalar-extension, vector group or unipotence notion
is introduced: existing definitions and the categorical finite product are reused.

## Latest recovery validation

On 2026-10-24 this recovery retained the packet, read the saved report and both
Lean modules, and ran the prescribed deliver2.py --no-push twice. Both runs
passed the four wound-definition checks and failed at Sheaf.Stage2.Sandbox1
with `resource exhausted (error code: 28, no space left on device)`.
Neither run pushed anything. The packet remains available for retry after
server storage is repaired; no launcher script or shared file was modified.

Recovery validation at 2026-10-24 10:37 UTC: read the retained report and both
Lean modules, then ran the prescribed unchanged-packet `deliver2.py --no-push`
twice. Both runs passed the private-overlay, preliminary, sandbox, and library
checks for Wound, then failed at `Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)` (exit 1).
No Lean diagnostic was reported, no source or tool was changed, and neither
run pushed anything. The packet is retained for a storage-repair retry.

Recovery validation at 2026-10-24 10:42 UTC: inspected the retained report and both Lean
modules, then ran the prescribed unchanged-packet `deliver2.py --no-push`
twice. Both runs passed the private-overlay, preliminary, sandbox, and library
checks for Wound, then failed at `Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)` (exit 1).
There was no Lean elaboration diagnostic to repair. No Lean source, node,
launcher script, or shared storage was changed, and nothing was pushed.

Recovery validation at 2026-10-24 10:45 UTC: inspected the retained report and both Lean
modules and ran the prescribed unchanged-packet `deliver2.py --no-push` twice.
Both attempts passed the four wound-definition checks and failed compiling
`Sheaf.Stage2.Sandbox1` with `resource exhausted (error code: 28, no space left
on device)` (exit 1). No Lean elaboration diagnostic was reported. No Lean
source, node, launcher tool, or shared storage was changed; nothing was pushed.

Recovery validation at 2026-10-24 10:48 UTC: retained the packet, read the
saved report and both Lean modules, and ran the prescribed unchanged-packet
`deliver2.py --no-push` twice. Both runs passed the private-overlay, preliminary,
sandbox, and library checks for Wound, then failed compiling
`Sheaf.Stage2.Sandbox1` with `resource exhausted (error code: 28, no space left
on device)` (exit 1). No Lean elaboration diagnostic was reported. No Lean
source, node, launcher tool, or shared storage was changed; nothing was pushed.

Recovery validation at 2026-10-24 10:55 UTC: read the saved report and both Lean modules;
ran the prescribed unchanged-packet `deliver2.py --no-push` twice.
Both runs passed all four Wound checks, then failed compiling
`Sheaf.Stage2.Sandbox1` with `resource exhausted (error code: 28, no space left
on device)` (exit 1). No Lean elaboration diagnostic was reported.
No Lean source, node, launcher tool, or shared storage was changed; nothing
was pushed. The retained packet awaits server storage repair.

Recovery validation at 2026-10-24 10:59 UTC: inspected the saved report, both
Lean modules and the item's node record, and ran the prescribed unchanged-packet
`deliver2.py --no-push` twice. Both runs passed the four Wound checks, then
failed compiling `Sheaf.Stage2.Sandbox1` with `resource exhausted (error code:
28, no space left on device)` (exit 1). No Lean diagnostic was reported.
No Lean source, node, launcher tool or shared storage was changed; nothing
was pushed. The packet remains retained for retry after server storage repair.

Recovery validation at 2026-10-24 11:02 UTC: inspected the retained report,
both Lean modules and the current item node, then ran the prescribed
unchanged-packet `deliver2.py --no-push` twice. Both attempts passed the
private-overlay, preliminary, sandbox and library Wound checks, then failed
compiling `Sheaf.Stage2.Sandbox1` with `resource exhausted (error code: 28,
no space left on device)` (exit 1). No Lean elaboration diagnostic was
reported. The packet is retained; no Lean source, node, launcher tool or
shared storage was modified, and nothing was pushed.

Recovery validation at 2026-10-24 11:07 UTC: inspected the retained report, both Lean
modules and node records, then ran the prescribed unchanged-packet
`deliver2.py Q73 lem-sfb-commutative-p-torsion-vector-wound-factor --no-push`
twice. Both runs passed the private-overlay, preliminary, sandbox and library
checks for Wound, then failed at `Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)`.
Local disk and inode space were available; the reported failure is on the
server compile path. No Lean diagnostic was reported, no source, node, launcher
tool or shared storage was changed, and nothing was pushed.

Recovery validation at 2026-10-24 11:10 UTC: inspected the retained report, both
Lean modules and the current item node, then ran the prescribed unchanged-packet
`deliver2.py Q73 lem-sfb-commutative-p-torsion-vector-wound-factor --no-push`
twice. Both attempts passed the private-overlay, preliminary, sandbox and library
checks for Wound, then failed compiling `Sheaf.Stage2.Sandbox1` with
`resource exhausted (error code: 28, no space left on device)` (exit 1).
No Lean elaboration diagnostic was reported. No source, node, launcher tool or
shared storage was changed, and nothing was pushed. The packet is retained.

## Successful recovery validation

At 2026-10-24 11:14 UTC, the prescribed unchanged-packet `deliver2.py --no-push`
passed server preflight and compilation of both delivered modules and printed
`OK (dry run)` for commit `3d2bfff9fb9`. The earlier storage failure did not recur.
The final self-check confirmed that the current item statement is unchanged,
only `lean` and the four documented added statement dependencies differ from
the live node, both signature records occur verbatim in their modules, all
variables are explicitly bound with `autoImplicit false`, and no lines exceed
100 characters. The wound definition has no `sorry`; the sole postponed proof
is the named theorem with its seven-step proof docstring. No released repair
note is present. The saved Lean and node files are retained without changes.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
