## Worker report

Item: `lem-coef-left-fibration-right-anodyne-base-change`, group Q107, stage 2.
The delivery states `SSet.Enhanced.leftFibration_rightAnodyne_baseChange` in
`Sheaf.CategoryTheory.LeftFibrationRightAnodyneBaseChange`. Its proof is `sorry`;
its docstring retains all eight steps of the node's saturation/prism proof.
No definition is introduced. The natural-language statement is unchanged.

Repair of return L on immutable head `2e622b187696` (2026-10-17): the retained
packet added `lem-coef-right-anodyne-mono-cancellation` to `stmt_deps` despite
its being a proof dependency with no Lean record on the returned base. Restored
`stmt_deps` verbatim from the current base: enhanced simplicial primitives,
fibrations, and right-anodyne maps only. Cancellation stays in `proof_deps`.
The current base now has the reviewed Q24 module
`Sheaf.CategoryTheory.RightAnodyneMonoCancellation`, declaration
`SSet.rightAnodyneExtensions_mono_cancellation`, with degreewise injectivity
hypotheses and the exact right-cancellation conclusion. Read its full signature
and proof docstring. Removed this packet's duplicate cancellation module and
node file; the item's existing proof-only import now resolves to that landed
module. No dependency module or new node is delivered, no statement correction
is needed, and no landed node's Lean record is overwritten.

Compared the retained node with the current shared node: only `lean` and the
invalid `stmt_deps` addition differed. The repaired node preserves every current
non-Lean field, including its original `stmt_deps`, `proof`, and `proof_deps`.
The item's theorem signature and eight-step proof docstring are retained.

Clause-by-clause statement check:

- Arbitrary simplicial sets in a fixed containing universe: `universe u` and
  `{X Y Z : SSet.{u}}`. There is no fibrancy or nonemptiness instance.
- The right-anodyne inclusion is `(i : X ⟶ Y)` with
  `(hi : rightAnodyneExtensions i)`. The predicate uses the smallest morphism
  property containing isomorphisms and the horns indexed by `0 < j`, and closed
  under pushouts, small transfinite compositions, and retracts. Being an inclusion
  follows from this class; no additional hypothesis is needed in the signature.
- The map to the same base is `(q : Z ⟶ Y)` with `(hq : leftFibration q)`.
  Its recorded definition quantifies over `n : ℕ`, `j : Fin (n + 1)`,
  `1 ≤ n`, and `j < Fin.last n`, with `HasLiftingProperty (horn n j).ι q`.
  Thus it is exactly the stated lifting of horns with `0 ≤ j < n`.
- The conclusion is `rightAnodyneExtensions (pullback.snd i q)`, whose domain
  is `pullback i q` and codomain is `Z`, the stated `X ×_Y Z → Z`.
  Pullbacks of simplicial sets are degreewise pullbacks.
- Neither total space nor base is assumed to be a quasicategory; the only two
  logical hypotheses are `hi` and `hq`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: existing Mathlib `SSet`,
  standard simplices/horns, and categorical products/pullbacks, publicly imported
  by that recorded interface. No private simplicial notion is introduced.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: publicly
  reexports `Sheaf.CategoryTheory.InfinityFibrations`, whose declaration
  `SSet.Enhanced.leftFibration` has the exact signature above. The newer
  recorded `cocartesianFibrationOver` interface introduces no constraint on it.
- `Sheaf.CategoryTheory.RightAnodyne`: `SSet.rightAnodyneExtensions`.
- Proof-only imports: `Sheaf.CategoryTheory.RightAnodyneProduct`
  (`SSet.rightAnodyneExtensions_pushoutProduct`), the landed
  `Sheaf.CategoryTheory.RightAnodyneMonoCancellation`
  (`SSet.rightAnodyneExtensions_mono_cancellation`), and
  `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`.

Edge cases: empty simplicial sets and empty pullbacks remain meaningful;
identity inclusions and isomorphisms are retained; dimension one has exactly the
appropriate endpoint horns. In dimension zero `0 < j` for `j : Fin 1` is
impossible, and `leftFibration` explicitly requires `1 ≤ n`; neither convention
imposes a dimension-zero nonemptiness condition. There is no Kan or quasicategory
hypothesis and no finite-size restriction. All universes and variables are
explicit (`autoImplicit false`). There is no STATEMENT-DISPUTED issue.

Retained searches (already performed on this packet):

- LeanFinder: "Pullback of a right anodyne map along a left fibration of
  simplicial sets is right anodyne", "Left fibrations are proper maps:
  pullback preserves right anodyne extensions", and "Base change of final
  horn cellular inclusions by an initial horn fibration". Results concern
  all-horn Kan fibrations or generic pullback stability; no exact match.
- LeanSearch: "A left fibration of simplicial sets preserves right anodyne
  inclusions under pullback" and "Pulling back a final anodyne simplicial
  inclusion along a left fibration preserves being final anodyne". Results
  concern ordinary fibrations and generic lifting/pullback properties.
- Loogle: `"anodyne", "pullback"`, no hits.
- `msearch.py grep`: `RightAnodyne|LeftFibration|right.anodyne|left.fibration`
  in AlgebraicTopology had no hits; `anodyne|fibration` in Quasicategory
  found only inner-fibration material. Mathlib's CategoryWithFibrations and
  AnodyneExtensions/Basic signatures were read; those use all horns.
- Targeted `rg` over Mathlib, the read-only upstream `WeilConjectures`, and
  shared `lean/Sheaf` found no exact base-change theorem. The repair repeated
  the duplicate check with `leftFibration_rightAnodyne_baseChange`,
  `rightAnodyneExtensions.*pullback`, and `pullback.*rightAnodyneExtensions`:
  no matches in those three trees. The cancellation search is now resolved
  by Q24's landed theorem and is not grounds to restate it.

Validation: `scompile.py Q107 lem-coef-left-fibration-right-anodyne-base-change
lean/Sheaf/CategoryTheory/LeftFibrationRightAnodyneBaseChange.lean` passed the
sandbox and library checks (1.7 s and 1.9 s), with no errors or warnings.
The only additional validation is the prescribed `deliver2.py --no-push` dry run;
no direct Lake/global build or live source edit is performed. The separate second
reader will review the repaired packet before delivery.

## Earlier second reading (a previous round; superseded)

Retained from the earlier independent reading of the theorem statement against
Cisinski, Proposition 4.4.11, with Proposition 4.4.4(iv). The packaging repair
above removes the obsolete auxiliary delivery; the theorem signature and the
mathematical inventory below have not changed. A separate fresh second reader
is responsible for this repaired packet's final delivery.

Statement inventory and verdict:

1. The ambient objects are simplicial sets, standard simplices, horns and
   degreewise pullbacks from `def-cbc-enhanced-diagrams-cones`; the theorem uses
   the fixed universe `SSet.{u}`. Verdict: exact, with no hidden size equality.
2. `i : X ⟶ Y` is a right anodyne map. In Lean this is
   `hi : SSet.rightAnodyneExtensions i`, the weakly saturated class generated by
   right horns and isomorphisms. Verdict: exact generator ranges and closure.
3. `q : Z ⟶ Y` is a left fibration. In Lean this is
   `hq : SSet.Enhanced.leftFibration q`, namely lifting every
   `horn n j` for `n ≥ 1` and `j < n` (equivalently `0 ≤ j < n`). Verdict:
   exact one-sided lifting condition; no quasicategory instances on `Y` or `Z`.
4. The conclusion is the pullback inclusion
   `X ×_Y Z → Z`. Mathlib's canonical map is
   `pullback.snd i q : pullback i q ⟶ Z`. Verdict: exact degreewise pullback
   projection and canonical inclusion; no arbitrary map or extra Mono hypothesis.
5. The statement explicitly allows empty simplicial sets, `n = 1`, and arbitrary
   containing universes, and explicitly imposes no Kan or quasicategory
   assumptions. Verdict: all source cases are retained.


## Second reading by Q107

I read the current node, its three statement dependencies, the module, and
Cisinski Proposition 4.4.11 (printed p. 159), together with Proposition 4.4.4(iv)
and the surrounding definition of properness. The source says that a left
fibration is proper, and that pulling back a right-anodyne monomorphism along it
is right anodyne. It imposes no quasicategory assumptions on the base or total
space. The node is exactly this specialization, with the one-sided horn
conventions spelled out.

Statement inventory, matched against
`SSet.Enhanced.leftFibration_rightAnodyne_baseChange`:

1. The fixed containing universe and arbitrary simplicial sets are rendered by
   `universe u` and `{X Y Z : SSet.{u}}`; no fibrancy, nonemptiness, or other
   instance is introduced. Verdict: exact.
2. The map `i : X ⟶ Y` and hypothesis that it is right anodyne are rendered by
   `(i : X ⟶ Y)` and `hi : rightAnodyneExtensions i`. The recorded definition
   is the smallest class containing isomorphisms and horns with `0 < i` in
   dimensions `n ≥ 1`, closed under pushouts, transfinite compositions, and
   retracts. Its members are the source's right-anodyne inclusions, so no
   extra `Mono` hypothesis is needed. Verdict: exact.
3. The map `q : Z → Y` and left-fibration hypothesis are rendered by
   `(q : Z ⟶ Y)` and `hq : leftFibration q`. Unfolding the recorded declaration
   gives `∀ n i, 1 ≤ n → i < Fin.last n → HasLiftingProperty (horn n i).ι q`,
   exactly `n ≥ 1` and `0 ≤ i < n`. Verdict: exact.
4. The pullback inclusion `X ×_Y Z → Z` is rendered by
   `rightAnodyneExtensions (pullback.snd i q)`. The Mathlib pullback projection
   has precisely this source and codomain. Verdict: exact orientation and
   conclusion.
5. The node's explicit statement that neither `Y` nor `Z` is a quasicategory
   is respected: the signature has no such instances. Verdict: exact.

Edge cases checked: empty simplicial sets and empty pullbacks remain allowed;
identity and isomorphism maps are included by the right-anodyne generators;
`n = 0` contributes no left-fibration horn because of `1 ≤ n`, while `n = 1`
has the expected unique left endpoint horn; right horns include the allowed
indices `0 < i ≤ n`; and the fixed universe is not restricted. There are no
ring, characteristic, finiteness, or zero-object hypotheses in this simplicial
statement.

Independent existing-declaration searches were run with LeanFinder via
`msearch.py` for “left fibration right anodyne base change”, and with `rg` for
`leftFibration_rightAnodyne_baseChange`, `left.?fibration.*right.?anodyne`, and
`right.?anodyne.*left.?fibration` in Mathlib, the read-only upstream
`WeilConjectures`, and shared `lean/Sheaf`. LeanFinder returned only all-horn
Kan-fibration and generic pullback results; the targeted grep found no exact
declaration. The only project hit was a prose reference to this blueprint.
The recorded dependency declarations were opened: `leftFibration` is the
arbitrary-base horn predicate in `InfinityFibrations`, and
`rightAnodyneExtensions` has the exact right-horn saturation generators.

No statement mismatch was found, so no Lean signature or node statement was
changed. The earlier packet repair was verified in this reading: the current
`stmt_deps` contains only the three statement dependencies, while right-anodyne
mono cancellation remains proof-only and resolves to the landed Q24 declaration;
there is no duplicate dependency module or node in this delivery. The module's
eight-step docstring matches the node's proof steps and all postponed proofs are
`sorry`. The required `scompile.py` check had already passed for the retained
module; this reading adds only this audit section.
