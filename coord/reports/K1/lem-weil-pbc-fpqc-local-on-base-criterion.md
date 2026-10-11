## Worker report

The module states `AlgebraicGeometry.fpqc_local_on_base_criterion` for a
morphism property `P : MorphismProperty Scheme.{u}`.  Condition (1) is the
explicit hypothesis `hflat` (stability of `P` along flat base changes
`pullback.snd f g`); conditions (0) and (2) are `[IsZariskiLocalAtTarget P]`
(which extends `RespectsIso`; its restriction clause follows from (0) and (1)
since open immersions are flat); condition (3) is `hdesc` (affine `S`, `T`,
arbitrary `X`, flat surjective `g : T ⟶ S`, `P (pullback.snd f g) → P f`).
The fpqc covering is `g : ∀ i, S' i ⟶ S` with
`hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`, and `H` states that
every second projection `pullback.snd f (g i)` has `P`.  The conclusion is `P f`.
(Reviewer R-flb1109: this paragraph replaces a stale one describing an earlier
version with `P.IsStableUnderBaseChange` and `Sieve.ofArrows … ∈ fpqcTopology`.)

The dependency declarations used are Mathlib's `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.Flat`, `CategoryTheory.Limits.pullback`,
`AlgebraicGeometry.Surjective`, and `AlgebraicGeometry.Scheme.fpqcPrecoverage`/
`Scheme.fpqcTopology`; these are imported through Mathlib's algebraic geometry
morphism and fpqc-site modules.  The source is Stacks Project, Descent,
Lemma Tag 02KP (line 5407), with Definition 02KO and Topologies 022B/022E.

Edge cases checked include an empty indexing type (the fpqc-covering hypothesis
then cannot hold except over an empty target), and the empty scheme appearing as
an affine target; the statement does not add a nonemptiness assumption.

Searches made: `rg -n 'local_on_base|fpqc.*criterion|of_isPullback_of_ofArrows_mem_fpqcTopology'
/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found the source theorem
`AlgebraicGeometry.Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`, whose
family encoding is the Mathlib fpqc topology.  Mathlib searches recorded in the
node (LeanSearch, LeanFinder, Loogle and grep) found only single-morphism
`DescendsAlong` results and no exact covering-family criterion; hence this node
is stated separately with `sorry`.

## Earlier second reading (a previous round; superseded)

The node and module were reread together.  The property `P`, base-change and
Zariski-local hypotheses, affine flat-surjective descent hypothesis, fpqc family,
and all fibre-product second projections correspond clause by clause.  No
mismatch was found.

## Second reading by K1

This reading supersedes the earlier second reading above. I opened the item node,
its five statement-dependency nodes, the delivered Lean, and the actual dependency
signatures. The repository does not contain the Stacks checkout on this machine;
I fetched the upstream `descent.tex` and `topologies.tex` into this item's scratchpad.
Their labels and line numbers agree with the node: 02KO at 5310, 02KP at 5407,
022B at 2888, and 022E at 3151. The source assumes a property of morphisms over a
base; the node specializes this to schemes without a designated base (equivalently
the terminal base). It imposes no field, characteristic, Noetherian, separation,
or finite-presentation assumption in the fpqc case.

Object/hypothesis/conclusion inventory, with the final Lean and verdict:

1. A class of morphisms of schemes: `P : MorphismProperty Scheme.{u}`. Exact.
   `def-pc-scheme` names Mathlib `Scheme` and its category of morphisms. I read
   `Scheme.lean`'s locally-ringed-space structure with its local-affineness field.
2. Condition (0), invariance under isomorphic arrows: included in
   `[IsZariskiLocalAtTarget P]`. I read `Morphisms/Basic.lean:112` and
   `MorphismProperty/Local.lean:51`: this abbreviates locality for the Zariski
   precoverage and extends `P.RespectsIso`. Exact together with (1) and (2).
3. Condition (1), preservation only along flat base changes:
   `hflat : ∀ {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S),
   Flat g → P f → P (pullback.snd f g)`. Exact; `T` is arbitrary, not affine.
   `def-weil-flat-morphism` records Mathlib `Flat`; its affine definition is
   equivalent to flatness of all stalk maps by `Flat.iff_flat_stalkMap`, which
   I opened in `Morphisms/Flat.lean`.
4. Condition (2), descent from any open cover of the target:
   `[IsZariskiLocalAtTarget P]`. Exact as a combined encoding of (0)-(2):
   `IsLocalAtTarget.of_forall_pullbackSnd` supplies the descent direction, and
   `IsZariskiLocalAtTarget.of_iSup_eq_top` states it for arbitrary indexed open
   covers. The class also supplies preservation of open restrictions, but this
   is already implied by (1), because every open immersion is flat, and by (0)
   to identify the restriction with the chosen pullback. Thus no stronger
   mathematical assumption is added. Conversely the class implies (0),(2).
5. Condition (3), descent along a flat surjection between affine schemes, with
   arbitrary total space: `hdesc : ∀ {S T X : Scheme.{u}} [IsAffine S]
   [IsAffine T] (f : X ⟶ S) (g : T ⟶ S), Flat g → Surjective g →
   P (pullback.snd f g) → P f`. Exact: only `S,T` are affine; `X` is not.
   `def-weil-surjective-morphism` records Mathlib `Surjective`; I read its
   underlying-map surjectivity field in `Morphisms/UnderlyingMap.lean:59`.
6. An arbitrary morphism and arbitrary family: `{S Z : Scheme.{u}}`
   (written as separate binders), `f : Z ⟶ S`, `{ι : Type w}`,
   `{S' : ι → Scheme.{u}}`, `g : ∀ i, S' i ⟶ S`. Exact; `Z` renders the
   node's `X`, and each `S' i` its `S_i`.
7. The family is an fpqc covering: `hg : Presieve.ofArrows S' g ∈
   Scheme.fpqcPrecoverage S`. Exact. `def-weil-pbc-fpqc-covering` records this
   very precoverage. I read `Sites/Fpqc.lean:63`, `Sites/QuasiCompact.lean`,
   and `Cover/QuasiCompact.lean:38,60`: it requires flat arrows and coverage
   of every affine open by finitely many images of compact opens, equivalently
   affine opens (`QuasiCompactCover.exists_isAffineOpen_of_isCompact`). It does
   not require each family member to be a quasi-compact morphism.
8. Every base-changed morphism has the property: `H : ∀ i,
   P (pullback.snd f (g i))`. Exact. `def-pc-fibre-product` records Mathlib's
   chosen `pullback`; I opened its definition and projections in
   `Limits/Shapes/Pullback/HasPullback.lean:95,111,115`. The second projection
   has target `S' i` as required, not `Z`.
9. Conclusion: `P f`. Exact, with the property hypotheses before the arbitrary
   morphism, covering family, and its base-change hypotheses.

Mismatches found and repaired (the node's own statement remains unchanged):

- `[P.IsStableUnderBaseChange]` assumed stability under every base change,
  rather than just flat ones. Replaced it by the exact `hflat` hypothesis.
- Old `hdesc` used `f : X ⟶ Spec R` as the flat-surjective covering map,
  did not require `X` affine, and concluded `P g` from `P (pullback.snd f g)`.
  That projection targets `Y`, the source of the morphism being descended,
  instead of the covering source `X`; the hypothesis was not descent at all.
  Replaced it by affine `S,T`, arbitrary `X`, covering `g`, and second
  projection `pullback.snd f g`, concluding `P f`.
- A generated sieve lying in `fpqcTopology` need not make every generator
  flat: one can append an arbitrary nonflat map to the identity covering.
  The node requires an fpqc family. Replaced the topology-sieve hypothesis
  by the recorded dependency's fpqc-precoverage family hypothesis.
- The theorem docstring had none of the seven proof steps. Added all seven,
  with their dependency-node names, including the empty coproduct case.
  Added the standard copyright header and replaced the unused broad descent
  import by `Mathlib.AlgebraicGeometry.Morphisms.Flat`.

Edge cases: `ι` may be empty, with no `Nonempty` or `Finite` instance added.
An empty family covers exactly an empty base; Zariski locality includes the
empty-cover case. Empty schemes are admitted in all binders. Both affine
schemes may be `Spec 0`; no nontrivial-ring assumption is present. The finite
refinement in the natural-language proof may have `n = 0`, yielding the empty
scheme `Spec 0`. No integers, field, or characteristic enter the signature.
All schemes lie in arbitrary universe `u` and the family index in independent
arbitrary universe `w`. The property hypotheses quantify over schemes in the
same `u` as the morphism, so there is no smaller testing universe making them
vacuous. No universe or variable is unbound.

Independent searches (logged in `searches.jsonl`): LeanFinder query
“morphism property stable under flat base change affine faithfully flat descent
fpqc covering criterion” returned flatness instances and single-map descent,
not this statement. LeanSearch query “criterion morphism property flat base
change Zariski open cover faithfully flat affine descent covering family”
failed with Internal Server Error; no result is claimed for it. Loogle query
`"IsStableUnderBaseChangeAlong"` returned the standard categorical notion of
stability along a morphism, not this covering criterion. The grep service query
`fpqc.*local|local.*fpqc|of_isPullback_of|flat.*base.change` in AlgebraicGeometry
returned single-map descent uses and concrete property instances. Independent
`rg` of the source project and `lean/Sheaf` for `fpqc_local_on_base_criterion`,
`IsStableUnderBaseChangeAlong`, `flat.*descent.*criterion`, `criterion.*fpqc`,
plus the fpqc/base-change searches, found no exact existing criterion.

I opened the source's `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`
(`WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:118`) including its
section variables: it requires full base-change stability and an instance of
descent along flat-surjective-quasi-compact maps, so it is not this node's
statement. Its arbitrary-square encoding does not cure that hypothesis mismatch.
The project's concrete flatness/local-finite-presentation/universally-closed
fpqc-descent statements specialize `P`; they do not duplicate this generic
criterion. No new definition node or dependency module is needed; all notions
are Mathlib's recorded ones, with no private definition.

The sole theorem still has `sorry`; nothing was proved and there is no definition
with postponed data. Source/blueprint docstrings and the seven-step proof are
present. The repaired module compiled on the server with `scompile.py`, exit 0,
in 1.7 seconds and without warnings. The node's `lean.statement` is extracted
verbatim from the final theorem signature, and all lines are at most 100 characters.
