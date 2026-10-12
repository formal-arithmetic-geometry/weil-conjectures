## What changed

Replaced the sorry in
`AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange`
with a composition of three comparisons. The existing general
`exists_addEquiv_module_abelian_stalk_exchange` handles the coefficient-universe bridge
and identifies the module stalk exchange with the abelian derived mate. A new abelian
geometric restriction theorem handles only the original-stalk/total-space geometry.
The already proved `pullback_forget_modules_iso` identifies the geometric theorem's
coefficient sheaf with the underlying abelian sheaf of the module pullback in the
original conclusion. Apply `Sheaf.functorH.mapIso` to this isomorphism and its pullback;
`cohomologyMap_map` proves the last commuting square. Thus the original proof combines
two exchange identities and a coefficient naturality identity, rather than applying a
renamed copy of the original theorem.

Added proof-only imports of `ModuleAbelianStalkExchange`, `EtalePullbackForgetModules`
and `ProjectiveLineAbelianOriginalStalkTotalExchange`. The original theorem's signature,
public imports, and existing docstring are unchanged. Updated its node's proof,
proof_deps and proof_origin to the actual reduction. Added one module and its node.
No definition or target statement changed, and no unit route was bypassed.
The cohomology transport identity and the full assembly from supplied coefficient
comparison data were checked in scratch examples with lcompile while waiting for the
newly landed coefficient module to enter the last green compiled library.

## Proved and sorry left

Proved, from named statements:
`AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange`
(node `lem-weil-pbc-p1-original-stalk-total-cohomology-exchange`).
No sorry remains in the item module.

The delivery adds exactly one sorry:
`AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange`
in `Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange`
(node `lem-weil-pbc-p1-abelian-original-stalk-total-exchange`). This theorem is the
abelian geometric restriction part, with no coefficient ring or module-cohomology
comparison, and no torsion hypothesis. It uses the unrestricted first assertion of
Stacks 03Q9. Its docstring and node give the full restriction-complex argument.

The existing `exists_addEquiv_module_abelian_stalk_exchange` still has sorry;
it is an existing independent item, not a new sorry in this delivery.

## No longer needed

All four original public imports serve the original signature and remain unchanged.
The item removes these proof-only imports from the current repository version:
`Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`,
`Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`,
`Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`,
`Sheaf.Paper.InverseImageStalkGerm`, and
`Sheaf.Paper.StrictHenselizationFunctoriality`.
The new item proof has only its three required proof imports. The new abelian module
retains proof-only imports for its four non-definition planned dependencies, including
`UnrestrictedStrictHenselizationStalk`; these support its documented open proof route.

`prop-weil-pbc-strict-henselization-stalk-formula` and
`Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula` are not needed on this route:
the new abelian geometric step uses
`lem-weil-pbc-unrestricted-strict-henselization-stalk` instead. This prunes the
extra torsion/derived clause of that formula from this argument.

The old direct dependencies `lem-weil-pbc-derived-exchange-termwise`,
`lem-weil-pbc-inverse-image-stalk-germ` and
`lem-weil-pbc-strict-henselization-functoriality` now belong to the new geometric
step's proof dependencies; they are not globally pruned. The old direct dependency
`lem-weil-pbc-injective-module-abelian-acyclic` belongs to the existing general
module/abelian exchange comparison's dependencies; it is also not globally pruned.
`lemma-weil-pbc-etale-pullback-forget-modules` remains used directly.

## Where the brief, the DAG or earlier work was wrong

The DAG noted that the narrower `SheafOfModules` injective-acyclic signature does not
supply the coefficient-universe bridge. The newly landed general
`ModuleAbelianStalkExchange` already states precisely that bridge for ModuleCat at
universe u+1 and includes compatibility with the exchange map. Consequently no new
module-resolution or injective-forget bridge is needed here.

The unrestricted first assertion of [Stacks 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
has no torsion assumption. The geometric theorem is therefore stated for arbitrary
abelian sheaves. Only the total strict-local restriction part of the final stalk
calculation of [Stacks 095T](https://stacks.math.columbia.edu/tag/095T) is used; no
proper base change theorem, closed-fibre comparison, or curve invariance is invoked.
The item remains below the realized unit step `lemma-weil-pbc-p1-exchange-geometric-stalk`.

Checked the new statement on degree zero (restriction of sections), zero coefficients
(the zero groups), identity base changes (naturality under a pullback isomorphism),
and purely inseparable extensions (pointed étale neighbourhoods and their stalks are
unchanged). Enlarging a separably closed field to Ω preserves finite separable
pointed-neighbourhood data, so it does not introduce a field-extension restriction.
There is no assertion that forgetting module coefficients preserves injectives.

Mathlib searches ran through msearch: LeanFinder returned eight topological stalk
lemmas, which are not the étale derived comparison; Loogle did not know the project's
`cohomologyMap`; grep found no strict-henselization stalk formula in Mathlib.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as no match.
Repository searches found the two coefficient comparisons used in the proof but no
existing original abelian geometric exchange theorem.

## New nodes

`lem-weil-pbc-p1-abelian-original-stalk-total-exchange`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-p1-abelian-original-stalk-total-exchange.json`,
stated in
`lean/Sheaf/AlgebraicGeometry/ProjectiveLineAbelianOriginalStalkTotalExchange.lean`.
This isolates the abelian geometric restriction argument from the separate general
module/abelian comparison. Its source is Stacks 03Q9 and the total-space restriction
part of the stalk calculation of 095T. Its conclusion does not involve any module
stalk or module pullback; the item proof supplies those via the existing coefficient
comparisons and the cohomology naturality square. No change records are needed.


## Second reading by S2

1. Compared both delivered modules with the repository. The item has exactly one
   existing declaration, whose signature and docstring are byte-for-byte unchanged.
   Its four public imports are unchanged; all added and removed item imports are
   proof-only. The other module is new. No definition, target, or change record is
   introduced. Verdict: pass.
2. Recompiled both files in import order with lcompile: clean, 4.6 s and 18.1 s.
   Inspected every proof: the item has no sorry, and the only added sorry is the named
   abelian geometric theorem listed above. No forbidden declaration or attribute,
   hollow definition, or hidden admitted proof occurs. A scratch module's explicit
   #print axioms checks show only propext, Classical.choice, Quot.sound, and sorryAx
   for both declarations, as expected from the two still-open named inputs.
   Verdict: valid reduction, conditional on the listed open statements.
3. Read the new statement, docstring, matching node, existing coefficient bridge,
   strict-local formula, stalk-germ theorem, and termwise exchange declaration.
   Checked Stacks 03Q9's unrestricted assertion and restriction-complex construction,
   and the total-space portion of 095T; no proper-base-change conclusion is used as
   an input. Degree zero gives section restriction; zero coefficients give zero
   groups; identity squares give the same restriction under pullback isomorphisms.
   Extension of separably closed point fields preserves each etale object's finite
   separable residue-point data, including purely inseparable extensions. The
   structural and residue compatibility hypotheses give precisely the pointed
   lifts required for naturality. The split removes the independent module/abelian
   coefficient comparison and is strictly a geometric part of the item, not a
   renamed item. Repeated LeanFinder, Loogle and grep with different queries:
   found point/global-section naturality and functor mapIso, but no existing etale
   derived strict-local exchange. Searched both repository roots and the upstream
   checkout for stalk/exchange comparisons; none closes this geometric naturality
   statement in a few minutes. Verdict: true, sufficient, nonduplicate split.
4. Read the proof from its conclusion upward. The three compositions and final
   cohomologyMap_map identity have the correct directions. The existing general
   coefficient comparison and proved pullback-forget isomorphism are reused.
   Inspected sk-thm-p1's realized statement and every realized step: this item is
   below the geometric-stalk step, and neither the closed-fibre comparison nor
   curve invariance is bypassed. All six old direct proof dependencies are
   accounted for in No longer needed; only the torsion strict-henselization formula
   leaves this route. Verdict: route preserved and pruning complete after repair.
5. Verified both nodes' lean.statement fields against the exact Lean signatures,
   and verified proof_deps equals the union of proof-step uses. The item's steps
   follow b1/b2, a1/a2, coefficient transport, and naturality as written. The new
   node has its complete statement, source, proof, searches, origin, creation,
   blueprint, chapter/unit and Lean records. Existing metadata changes are confined
   to proof, proof_deps and proof_origin. Verdict: consistent.

Second-reader changes: added the four proof-only planned-dependency imports to the
new abelian module, so its documented open proof route stays in the import closure;
corrected No longer needed to list the five removed proof imports relative to the
current repository version. No statement, definition, or existing proof was changed.
