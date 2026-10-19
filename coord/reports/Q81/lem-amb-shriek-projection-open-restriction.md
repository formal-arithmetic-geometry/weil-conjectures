## Worker report

The module states the node's actual coefficient-first open-restriction equality and its
inverse clause. Every theorem proof is `sorry`. No definition, axiom, new node or
natural-language statement correction is introduced. The shared checkout already carries
an earlier right-coefficient version; this delivery renders the displayed coefficient-first
formula directly using the now-published canonical map, with the names K and M as in the node.
There is no repair-note file for this item.

Hypotheses and clauses, read against the node and the two complete signatures:

- The finite commutative ring A is `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`.
  This is the recorded six-functor size convention, not an extra finiteness or characteristic
  assumption.
- The Noetherian schemes X, S and U are `Scheme.{u}` with their three `IsNoetherian`
  instances. The fibre product is `pullback f u`, with its recorded canonical projections
  `pullback.fst f u` (v) and `pullback.snd f u` (f_U), and square
  `IsPullback.of_hasPullback f u`. Its Noetherian property follows since it is open in X.
- The separated finite-type compactifiable map is `(f : X ⟶ S)`, `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, `[QuasiCompact f]`, `[HasCompactification f]`.
  Compactifiability and quasi-compactness of f_U follow by the existing base-change
  instances; they are not additional binders. The open immersion is `(u : U ⟶ S)` and
  `[IsOpenImmersion u]`.
- K belongs to `DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))`,
  M to the corresponding category over X. These are the ordinary unbounded categories;
  there is no cohomological bound, Tor amplitude or constructibility predicate.
- P is exactly `compactProjectionMapCoeffFirst Λ f K M` and its base-change specialization.
  Its real definition is the canonical signed symmetry, the actual compactified upstream
  `projectionMap`, and direct image of signed symmetry. Thus it has the coefficient-first
  source K tensor Rf_!M and target Rf_!(Lf^*K tensor M) required by the node.
- C is `rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f u)`.
  The recorded `unboundedEtaleCompactSupportBaseChange` is definitionally this transformation
  transported by `leftDerivedUpperStarIsoMapDerivedCategory` at u and v. Its source file
  explicitly defines that transport, so we retain precisely the named canonical exchange,
  rather than an arbitrary map or an assumed isomorphism. On the proper factor the exchange
  is the unit-square-counit mate; on the open factor it is the inverse derived open comparison.
- The left side of the first equality is u^*P followed by C on f^*K tensor M, then
  `Rf_U!` of `leftDerivedUpperStarTensorComparison` at v, then tensoring the canonical
  `derivedSquareUpperStarIsoInvApp` at K with v^*M. These last two factors write out the
  target identifications suppressed in the node's display.
- The right side is the pullback tensor comparison at u applied to K and Rf_!M, then
  tensoring u^*K with C at M, then P for f_U at u^*K and v^*M. This is precisely
  P_U composed with (1 tensor C), with the source identification written out.
- Compactification independence is inherited from the recorded canonical compact-support
  and exchange constructions. The proof docstring identifies the general exchange theorem
  and the proper/open normalization and refinement comparisons that give this interpretation.
- The second theorem assumes `IsIso` of exactly the two projection maps and states
  C followed by the same target identifications and P_U inverse equals u^*(P inverse)
  followed by the source tensor comparison and (1 tensor C). This is the inverse identity
  obtained by canceling the first equation. It does not replace that identity by an identity
  of unrelated isomorphisms.

Dependency declarations inspected and used (possibly through the public upstream import):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded ordinary
  `DerivedCategoryModule` encoding (unfolded in the binders); its current source was read
  with `scompile.py --source`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact` supplies the exact coefficient
  inverse image interpretation; its full live declaration was read with `--source`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`; the convention node
  def-weil-scheme-morphism-properties fixes no separate object. Its separated and finite-type
  properties are the Mathlib `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` classes.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification` and `rightDerivedLowerShriek`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleCompactSupport_baseChange`, `unboundedEtaleCompactSupportBaseChange`.
  Its definition was read to check the exact-derived pullback transport.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap`, the proper factor of the compactified map.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`: `SheafOfModules.ringedSlice_extension_tensor`;
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  `Etale.derivedOpenImmersionLowerShriekProjectionIso`, the actual derived open factor.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `Etale.exactDerivedBaseChangeMap`;
  `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `Etale.etaleLowerShriekBaseChangeMap` (live source read with `--source`).
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its etale constant-coefficient instance is the upstream
  `leftDerivedUpperStarTensorComparison` appearing in the equality.
- `Sheaf.AlgebraicGeometry.CompactProjectionExchange`:
  `Etale.compactProjectionMapCoeffFirst` and
  `Etale.compactProjectionMapCoeffFirst_baseChangeMap`. This already recorded proof dependency
  is added to stmt_deps because its coefficient-first map is now used explicitly.

Edge cases checked: the empty base or empty open U, identity open immersion, zero ring,
zero K or M, and unbounded K and M. None is excluded by a new binder. The two isomorphism
assumptions occur only in the conditional inverse clause. Base-change compactifiability uses
`HasCompactification.pullback_snd`, whose source constructs the pullback compactification.
The category size follows ModuleCat at u+1 on Scheme at u and does not equate independent
site universes. No disputed statement or source correction was needed.

Searches made:

- msearch LeanFinder, “compact support derived projection formula commutes with open base
  restriction”: eight irrelevant Profinite Nobeling restriction hits, no match.
- msearch Loogle, `AlgebraicGeometry.Etale.projectionMap,
  AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`: no hits; unknown identifier
  projectionMap in the Mathlib search index.
- msearch grep, `compactSupportProjection|projectionMap.*BaseChange` in AlgebraicGeometry:
  zero Mathlib hits.
- msearch LeanSearch, “compact support projection map compatible with base change”:
  eight unrelated support and ring-map base-change hits; no theorem match.
- rg in the source WeilConjectures tree found
  `projectionMap_rightDerivedLowerShriekBaseChangeMap` and its WeilFrobenius use.
  Reading the full declaration confirms it is the opposite tensor convention, hence it
  supplies the general input but does not directly state this coefficient-first formula.
- rg in lean/Sheaf found the earlier statement of this item and the already published
  coefficient-first CompactProjectionExchange module. We reuse its construction, introducing
  no second projection map. The theorem specializes that statement to an open base and adds
  the inverse clause. The source node-id grep in WeilConjectures has no hit, and the upstream
  name index has no collision for the two theorem names.

Source reading: more-etale.tex lemma-base-change-shriek (0F7L) constructs exchange by
proper base change followed by open base change and requires compactification independence;
sites-cohomology.tex remark-compatible-with-diagram (0E48) displays precisely the source
tensor, exchange, target tensor and pullback-composition transports. Both local source
passages were read in full. The existing tensor symmetry accounts for coefficient order.

Validation: scompile.py completed with exit code 0, no errors and no non-sorry warnings.
It compiled the imported coefficient-first module, the sandbox file, and the final library
module separately. The prescribed delivery preflight is the next check.

## Second reading by Q81

Independent maintainer reading of the immutable delivery, 2026-10-18. This section is
written by the independent reviewer and does not claim a prior worker reading.


| Node object or clause | Exact Lean rendering and assessment |
| --- | --- |
| Finite commutative ring A | `Λ : Type (u + 1)`, `[CommRing Λ]`, `[Finite Λ]`. No field, nontriviality or invertible integer is assumed. |
| Ordinary small-etale unbounded categories | `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, definitionally the recorded `DerivedCategoryModule Λ T`. Neither bounded nor pro-etale categories occur. |
| Noetherian schemes | `[IsNoetherian X]`, `[IsNoetherian S]`, `[IsNoetherian U]`. Mathlib's class is locally Noetherian plus compact, equivalent to a finite Noetherian affine cover. The pullback is an open subscheme of X and thus Noetherian. |
| Separated, finite type, compactifiable f | `(f : X ⟶ S)`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`, `[HasCompactification f]`. Locally finite type plus quasi-compact is precisely finite type. |
| Open u and its square | `(u : U ⟶ S)`, `[IsOpenImmersion u]`; `pullback f u`, `pullback.fst f u = v`, `pullback.snd f u = f_U`, `IsPullback.of_hasPullback f u`. No arbitrary square comparison is introduced. |
| No extra base-change assumptions | Compactifiability of f_U is supplied by `HasCompactification.pullback_snd`, constructed by base-changing a compactification; quasi-compactness is stable under base change. No additional instance binder is demanded. |
| Arbitrary K and M | K is over S, M over X, with no amplitude, cohomological, flatness, constructibility, or support restriction. |
| Actual coefficient-first P | `compactProjectionMapCoeffFirst Λ f K M`. Its body is signed tensor symmetry, the real upstream `projectionMap`, and direct image of signed tensor symmetry. It is not an arbitrary map or an uncharacterized choice. |
| Canonical C | `rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f u)`. The recorded exact `unboundedEtaleCompactSupportBaseChange` is this transformation transported by `leftDerivedUpperStarIsoMapDerivedCategory` at u and v. Thus L inverse image in the theorem expresses the node's exact inverse image. |
| Left side | `L(u^*).map P`, followed by C on `Lf^*K ⊗ M`, then `Rf_U!` of the tensor comparison at v and of the square comparison tensored with v^*M. The final two factors are exactly the target identifications suppressed in the node. |
| Right side | The tensor comparison at u, followed by tensoring u^*K with C at M, followed by P for f_U. This is the node's `P_U ∘ (1 ⊗ C)` with its source identification. |
| Independence and normalization | `rightDerivedLowerShriek` is the chosen-compactification functor `Dj_! ⋙ Rr_*`. The comparison dependency provides refinement coherence and canonical exchange normalization. Its exact exchange is proper exchange followed by the inverse open comparison. The projection is assembled from the proper projection and inverse open tensor comparison; symmetry changes only coefficient order. The equality is on these maps, not on unspecified isomorphisms. |
| Inverse clause | The second theorem assumes `IsIso` of exactly P_f and P_f_U and asserts `C ≫ target-identifications ≫ inv P_f_U = L(u^*).map (inv P_f) ≫ source-identification ≫ (1 ⊗ C)`. This follows by precomposing the first equality with the pulled-back inverse P_f and postcomposing with inverse P_f_U. No assumed invertibility of an unrelated map or extra exchange assumption occurs. |

The main equality is the specialization of
`compactProjectionMapCoeffFirst_baseChangeMap` to the chosen pullback square, Q = K.
All four factors and both tensor positions match that declaration. The inverse clause is
ordinary categorical cancellation of that same equality. The node proof's wording
“four projection maps” is an incidental counting slip: the display has two projection maps,
and the delivered conditional statement assumes precisely those two are invertible.
It does not change the mathematical assertion or warrant a source-based correction.

## Dependency and exact-declaration audit

The following are the sixteen dependency interfaces inspected. Generic declarations are
specialized at the actual coefficient category, not inferred from similar names.

1. `def-weil-pbc-derived-categories`: synchronized
   `WeilConjectures.AlgebraicGeometry.DerivedCategories`, its module docstring and
   `DerivedCategory.torsionCohomology`; the needed category abbreviation itself is in
   `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
   `AlgebraicGeometry.Etale.DerivedCategoryModule`.
2. `prop-weil-pbc-inverse-image-modules-exact`: synchronized
   `AlgebraicGeometry.etaleInverseImageModulesExact`, including its constant-ring
   identifications, module action, exactness and adjunction clauses.
3. `def-kun-derived-tensor`: `Etale.derivedTensor` in `Derived.Tensor` is the actual curried
   tensor of the unbounded derived category, with the K-flat total derived interface.
4. `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and scheme morphisms.
5. `def-amb-etale-compact-support`: `Etale.rightDerivedLowerShriekOfCompactification` in
   `Derived.LowerShriek` is definitionally `D(c.i_!open) ⋙ R(c.g_*)`; the chosen version
   `rightDerivedLowerShriek` applies it to `HasCompactification.compactification f`.
6. `lem-amb-unbounded-compact-support-comparisons`:
   `unboundedEtaleCompactSupportBaseChange`, `unboundedEtaleCompactSupport_baseChange`,
   comparison coherence, and exchange normalization in
   `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`. In particular the
   exact-pullback transport is an explicit definition, not a new exchange choice.
7. `def-weil-scheme-morphism-properties`: explicitly a convention node, not a missing
   declaration. Its separated/finite-type/open properties are the Mathlib classes used here.
8. `def-pc-fibre-product`: Mathlib `pullback`, `pullback.fst`, `pullback.snd` and the canonical
   `IsPullback.of_hasPullback`; schemes have the required pullbacks.
9. `def-weil-open-immersion`: Mathlib `IsOpenImmersion`, the scheme specialization of the
   locally ringed-space notion.
10. `def-kun-projection-formula-map`: `Etale.rightDerivedLowerStarProjectionMap` in
    `Derived.LowerStarProjection`, defined as the adjunction projection mate. Its
    `app_app` and transpose declarations give the precise tensor-comparison/counit map.
11. `lem-weil-pbc-ringed-slice-extension-tensor`:
    `SheafOfModules.ringedSlice_extension_tensor` in the recorded module. This theorem
    asserts a natural sheaf tensor isomorphism. The consumer uses the separately recorded
    canonical derived open map, not a choice from its bare `Nonempty` conclusion.
12. `def-kun-unbounded-exchange`: `Etale.exactDerivedSquareUpperStarIso` and
    `exactDerivedBaseChangeMap` in `ExactUnboundedExchange`, explicitly the mate of the
    descended canonical square. The compact-support normalization identifies this proper
    factor with the transported L-derived exchange used in the theorem.
13. `def-weil-pbc-etale-shriek-base-change-map`: synchronized
    `Etale.etaleLowerShriekBaseChangeMap`, the inverse conjugate of underived exchange.
    Its direction is `j'_! f'^* ⟶ f^* j_!`, so the compact exchange uses its inverse.
14. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`:
    `CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
    with independent site object/Hom universes and its unique K-flat representative
    characterization. The concrete etale `leftDerivedUpperStarTensorComparison` is the
    derived ordinary tensor comparison, with natural isomorphism and representative
    normalization in `Derived.UpperStarMonoidal.Comparison`.
15. `lem-pur-etale-open-derived-tensor`:
    `Etale.derivedOpenImmersionLowerShriekProjectionIso`, `asIso` of the canonical
    adjunction projection map, not an arbitrary isomorphism. Its inverse is the required
    `(j_!M) ⊗ N ⟶ j_!(M ⊗ j^*N)` comparison.
16. `lem-asd-compact-projection-exchange`: read the complete
    `CompactProjectionExchange.lean`, including the real definition
    `compactProjectionMapCoeffFirst`, the full coefficient-first theorem, and its six-step
    proof docstring. Also read the upstream right-coefficient
    `projectionMap_rightDerivedLowerShriekBaseChangeMap` and the proper/open assembly in
    `LowerShriekProjection` and `LowerShriekBaseChange`.

No dependency module needs §1(B) repair. No helper or unstated DAG prerequisite is missing.
No mathematical statement was corrected, so a §1(C) citer audit is not applicable.

## Sources, searches and edge cases

Read the complete Stacks passages at
`literature/stacks-project/more-etale.tex:3429` (0F7L),
`sites-cohomology.tex:13715` (0E48), and `sites-cohomology.tex:4578` (0GL1)
in the group clone. The first constructs exchange as proper exchange followed by open
base change, and explicitly requires compactification independence. The second is the
unbounded projection/exchange diagram with source tensor, target tensor and pullback
composition comparisons; it does not require projection invertibility. The third gives
the unbounded open tensor formula on K-flat representatives. The surrounding compact-support
context allows all unbounded complexes for a torsion coefficient ring; a finite ring is
such a ring. Read the blueprint source for the general compact projection/exchange node
and the short tensor, projection, unbounded exchange and scheme source definitions.

Independent `rg` searches in Mathlib's algebraic geometry, the slopmaster2
`WeilConjectures` tree and the group clone's `lean/Sheaf` used
`compactSupportProjection`, `compactProjectionMapCoeffFirst`,
`projectionMap_rightDerivedLowerShriekBaseChangeMap` and projection/open/restriction
variants. The existing general coefficient-first theorem and map are reused; the upstream
theorem uses the opposite tensor order. The older same-item file in the group clone is
an earlier presentation being replaced, not an independent notion to duplicate. The
remaining hits concern other categories or reduction towers. An independent msearch
Loogle query `"compactSupportProjection"` returned zero hits. The worker report also records
LeanFinder, Loogle, LeanSearch and grep searches. No duplicate construction is introduced.

Empty S, empty X, empty U and the identity open are not excluded. Zero coefficients are
allowed (`CommRing` has no `Nontrivial` binder); zero K or M and arbitrarily unbounded
complexes are allowed. There is no characteristic restriction, finite Tor-amplitude bound,
or index family whose empty case could be lost. `Scheme.{u}` with coefficients and module
values at u+1 is the explicitly recorded six-functor size convention; no independent site
universes are identified. Every named binder and the single universe u is explicit, with
`autoImplicit false`. The inverse assumptions occur only in the conditional inverse theorem.

## Findings and complete repairs

- **H11 (and the user's real-section requirement):** the delivered
  `## Second reading by Q81` contains only a disclaimer saying that no second reading
  occurred. Replace it with this independent hypothesis-by-hypothesis reading and the
  findings, retaining the original Worker report. The replacement identifies its authorial
  role as the maintainer's independent reader, not a fictitious earlier Q81 worker.
- **H9, proof-dependency import convention:** the delivered module imports only
  `CompactProjectionExchange` and `Mathlib.AlgebraicGeometry.Noetherian`. Its proof plan
  additionally cites the recorded compact-support comparison package and generic tensor
  pullback dependency. The replacement adds ordinary `import` lines for the five other
  proof-dependency modules, retaining the existing public import of the general exchange
  theorem. This also explicitly imports the compact-support, open tensor and normalized
  open base-change dependencies. These are proof-plan imports as required by §3; the
  `sorry` proof need not use them yet. No declaration or theorem signature changes.

`fixes/lean/Sheaf/AlgebraicGeometry/CompactSupportProjectionOpenRestriction.lean` is a
complete replacement at the delivered module's path.
`fixes/lem-amb-shriek-projection-open-restriction.report.md` is a complete replacement
report. Both formats are accepted by the stage-2 `--apply-fixes` reader in
`tools/merge_delivery.py`. No Lean-record override is required: the declaration names,
file path and verbatim statement remain identical.

The original primary `lean.statement` was compared by exact string equality with the
signature from `theorem` through the text before `:= by`: equal. The replacement changes
only imports, so this equality remains true. Both theorem bodies are exactly `by sorry`;
there is no local proof, definition, axiom, private notation or local instance in either
version. Both declaration docstrings have source tags, blueprint ID and the node's three
proof steps across the main and inverse statements. The module docstring also gives source
and blueprint ID. Every module line is at most 100 characters.

## Compiler evidence and isolation

The worker report records a clean per-file scompile for the imported coefficient-first
module and the delivered sandbox and library forms. Independently reproduced the immutable
file with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q81 \
  lem-amb-shriek-projection-open-restriction \
  snapshot/lean/Sheaf/AlgebraicGeometry/CompactSupportProjectionOpenRestriction.lean
```

Exit 0, sandbox 14.4 s, library 16.3 s; no diagnostics. The wrapper reported a private
`/dev/shm/nt-tmp/nt-local-compile-zj2bwisw/.lbuild` overlay. The currently installed wrapper
executes its overlay checks on the server; this is not evidence of a separate local
compiler invocation. Used only the prescribed wrapper, not a direct SSH command.

Replacement reproduction used the same command with
`fixes/lean/Sheaf/AlgebraicGeometry/CompactSupportProjectionOpenRestriction.lean`.
Exit 0, sandbox 15.3 s, library 15.6 s, with no diagnostics; private overlay
`/dev/shm/nt-tmp/nt-local-compile-nzxkhvyh/.lbuild`. Both invocations retained the
wrapper's 60-second per-file limit. Final checks confirm that the original and replacement
primary statement fields match verbatim, both declaration/docstring blocks are unchanged,
the maximum Lean line length is 97, and the fixes directory contains exactly the two
complete replacement files listed above. No unresolved substantive finding remains. No lake/global build,
live Lean write, Git mutation, claim, delivery, merge, message to another worker or edit of
a project clone was performed. Only review.md and complete fixes under this review's
fixes directory were written. `head.txt` remains the requested immutable SHA.
