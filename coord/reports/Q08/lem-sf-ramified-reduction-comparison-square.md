## Worker report

The module states `WeilConjectures.RamifiedReduction.ramified_reduction_comparison_square`.
Its only postponed proof is the theorem with this name. Every helper has real data.
The TeX statement is unchanged. `def-coef-finite-coefficient-stages`, an existing landed
notion, was added to stmt_deps to name the Stage/Arrow presentation used here.

The source read was main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-free-extension.proof.md, especially its paragraph beginning
“For two field extensions, or a quotient followed by extension”. The expanded ten-step
DAG proof is included verbatim in the theorem docstring, with wrapping only.

Hypotheses and clauses:

- The fixed algebraic closure of a finite field is `D₀ : FiniteFieldDatum`,
  the prime is `[Fact l.Prime]`, and the different-characteristic condition is `_hl`.
- `E`, `L`, their Field/Algebra/FiniteDimensional instances, and the embedding `ι`
  give the two finite coefficient extensions and their inclusion.
- `m n : ℕ+` and `hmn` say exactly 1 ≤ m ≤ n. `e : ℕ+` and `_he` give the
  ramification ideal equality, independent of the unit relating uniformizers.
- `_basis` is one integral basis with finite index `Fin rank`. At either level its
  reductions are the stipulated basis. No independent bases, flat quotient assumption,
  smoothness, site perfectness, or arbitrary isomorphism of endpoint objects is assumed.
- The Over instances give V, X, Z their k-structures. The three sets of IsSeparated,
  LocallyOfFiniteType and QuasiCompact instances give separated finite-type k-schemes.
  `f.IsOver`, its three morphism properties, and `i.IsOver`/IsClosedImmersion give
  exactly the geometric maps of the statement. `c` is the fixed structure compactification.
- `baseStage n` has ring A_n. `level ι n` has ring O_L/(ι(varpi_E))^n, hence B_n,
  not O_L/varpi_L^n. `_he` identifies its ideal with (varpi_L)^(e*n).
  `horizontal` and `reduction` contain precisely the given embedding and identity,
  respectively, and `Arrow.ringMap` takes the induced maps on actual quotients.
- The witness `h` asserts commutation of the actual ring maps. `squareIso` is the
  composite of the two published `Sites.comp` reassociations through their common
  composite. These are the normalized scalar associators on K-flat representatives,
  whose balancing multiplies coefficient factors. This retains the derived
  identification of the two paths at B_m, rather than choosing a path isomorphism.
- `Squares` has five conjuncts in order: direct image, closed exceptional image,
  dualizing object, internal Hom in both variables, and Verdier duality. Covariant
  endpoint functors map `squareIso.hom`; contravariant Hom/dual inputs map its inverse.
  This is the displayed mixed-square equation with every understood associator explicit.
- `Sites.direct` is the recorded inverse-image counit transpose. `closedArrow` dispatches
  to `FiniteFreeCoefficients.closedMap` or `Sites.proClosedMap`: its inverse closed
  direct-image comparison followed by the exceptional counit is transposed. `omegaArrow`
  dispatches to the specified compact-support counit transpose or its site transport.
  The compact map in these definitions is the proper projection map followed by
  proper direct image of open extension by zero, as required.
- `Sites.homMap` is the extended-evaluation transpose and `Sites.dualMap` is that map
  followed by Hom of `omegaArrow`. The existential tensorators are constrained by
  `NormalizedTensor`; they cannot be arbitrary maps. The symmetry is similarly
  constrained by the existing `NormalizedSymmetry` (the signed Koszul symmetry).
- Four `Pairings` conjuncts give evaluation and its double-dual transpose for each
  edge. Their equations use the named `evaluation` and `bidual` constructions and
  `Sites.dualMap`, without assuming a biduality isomorphism.
- The final clause types the dualizing objects and all duals at the four corners as
  bounded constructible finite-Tor. Reapplication includes repeated duals. Inputs in
  each square use `Sites.Ctf`, which tests all degree-zero module sheaves for Tor.
- `∀ pro : Bool` asserts the same five equations on both sites. For true, exceptional
  image is the recorded etale right adjoint transported by Rν_* and ν*, not a claimed
  ambient pro-etale exceptional adjunction. The vertical arrows use these same canonical
  counit/evaluation definitions, the normalizations specified in the quotient lemmas.

Dependency declarations used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-scheme-morphism-properties`: `None`, `None`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `lem-exc-closed-ambient`: `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `thm-amb-etale-exceptional-adjoint`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`, `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`, `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- `lem-weil-duality-pairing`: `Sheaf.Paper.DualityPairing`, `AlgebraicGeometry.Etale.ambient_duality_pairing`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-pbc-constructible-complexes`: `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`, `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
- `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `lem-coef-finite-direct-image`: `Sheaf.Paper.FiniteCoefficientDirectImage`, `AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_isIso`.
- `lem-coef-finite-closed-shriek`: `Sheaf.Paper.FiniteClosedShriek`, `WeilConjectures.finiteCoefficientClosedShriek`.
- `lem-coef-finite-dualizing`: `Sheaf.SixFunctors.FiniteDualizing`, `WeilConjectures.finiteDualizingCoefficientComparisons`.
- `thm-coef-finite-hom`: `Sheaf.Paper.FiniteCoefficientHomChange`, `WeilConjectures.finiteCoefficient_derivedHom_change`.
- `cor-coef-finite-verdier`: `Sheaf.SixFunctors.FiniteCoefficientVerdier`, `WeilConjectures.finite_coefficient_verdier`.
- `lem-coef-finite-etale-descent`: `Sheaf.Paper.FiniteEtaleDescent`, `WeilConjectures.finiteCoefficientEtaleDescent`.
- `def-coef-finite-coefficient-stages`: `Sheaf.Paper.FiniteCoefficientAdjointComparisons`, `AlgebraicGeometry.FiniteCoefficientAdjoints.Stage`.

The shared constructions are reused from the published
`Sheaf.Paper.FiniteFreeCoefficientExtension` module: the functions `Sites.D`,
`scalar`, `comp`, `push`, `direct`, `exceptional`, `omega`, `dual`, `homMap`, `dualMap`,
`NormalizedTensor`, `NormalizedSymmetry`, `evaluation`, and `bidual`, together with
`FiniteFreeCoefficients.closedMap`, `omegaMap` and their named pro-etale transports.
Only these real definitions are used; the parent theorem is never invoked. The
existing parent module cannot acquire an import of this consumer without a cycle;
its future proof import must therefore be omitted under stages/2-statements §3.7.
No new notions or dependency replacement modules were needed.

Edge checks: m=n leaves the quotient identity case; e=1 includes unramified extension;
ι=id includes identical coefficient fields; m=1 includes the residue level. For e=2,
n=2, m=1, the upper quotients are O_L/varpi_L^4 and O_L/varpi_L^2. Zero inputs and empty
schemes remain admitted. The quotient is allowed to be non-flat (e.g. Z/l² → Z/l).
Both Hom variables and the first variable's contravariance were checked explicitly.
There is no restriction on a Tor interval beyond finiteness and no dimension bound.

Searches made with msearch.py are preserved in searches.jsonl. LeanFinder queried
“Mixed ramified coefficient extension and quotient reduction commute with direct image
exceptional pullback internal Hom and Verdier duality”: results were generic pullback
and conjugation lemmas, no exact statement. Loogle on
`CategoryTheory.Adjunction, CategoryTheory.Functor` returned general adjunction data only.
Mathlib grep for `scalarExtension.*[Cc]omp|[Cc]oefficient.*[Aa]ssoc` in CategoryTheory
returned zero hits. Additional LeanSearch/LeanFinder/grep searches for canonical finite
coefficient comparison maps returned infrastructure only. Project rg searches found the
published finite-free coefficient module and the distinct ramified-pullback tower
modules; none states the five mixed reduction squares separately. The node-id search
in WeilConjectures returned no declaration. No search failure was counted as no match.

Validation: scompile.py accepted the complete module on the server in 51.3 seconds.
A separate attempt with additional direct proof imports timed out while compiling the
existing FiniteHomDomainCalculus overlay, before checking this module. Those extra
imports were removed for isolation; the full canonical-construction import is retained.
The final compile and prescribed deliver2.py preflight results are recorded below.

Final validation: scompile.py accepted the revised module in both namespaces: sandbox
49.1 seconds, library 54.8 seconds. deliver2.py --no-push returned OK: commit
f82c6034a57 passed the maintainer preflight and per-file server compilation; nothing
was pushed by that dry run. The stale, unowned SixFunctors draft from the interrupted
attempt was removed from this sandbox before the successful dry run.


## Returned delivery repair audit

Return: independent immutable head 0842038b3cbf, five incremental DAG cycles.
The required initial saved-packet dry run was performed again. Both the sandbox
and library module compiled; server preflight rejected precisely the same five
cycles. The current repository node differs from the saved node only in `lean`
and the additional `def-coef-finite-coefficient-stages` statement dependency.
The extra definition's complete dependency closure has 21 nodes and does not
reach this item. No mathematical statement or proof was changed for this audit.

All five rejected outgoing edges already occur in the current repository node.
They are inherited stage-1 graph faults, rather than edges introduced by this
stage-2 packet:

- `lem-coef-finite-closed-shriek` reaches this item through
  `prop-sf-localization-all-stages`, `lem-sf-supported-weil-mate-lift`,
  `lem-sf-open-closed-weil-mate-structures`,
  `def-zl-field-weil-shriek-shift-data`,
  `lem-pod-semilinear-field-operation-lifts`,
  `lem-pod-weil-frobenius-compact-support-exchange`, `sk-def-sf-exchanges`,
  `sk-def-sf-operations`, `thm-sf-ctf-stability`,
  `lem-coef-rational-operations`, and `lem-coef-finite-free-extension`.
- `lem-coef-finite-dualizing` reaches the same path at
  `def-zl-field-weil-shriek-shift-data` through
  `lem-coef-dualizing-affine-space`, `def-pur-exceptional-coefficient-tensor-maps`,
  `def-pur-co-smoothness`, and `fix-prop-projection-formula`.
- `cor-coef-finite-verdier` reaches that second path through
  `lem-coef-finite-dualizing`.
- `lem-coef-finite-etale-descent` reaches the first path through
  `lem-coef-finite-closed-shriek`.
- `lem-sf-finite-free-etale-proetale-transport` reaches the first path through
  `lem-coef-finite-etale-descent` and `lem-coef-finite-closed-shriek`.

The source paragraph beginning “For two field extensions, or a quotient followed
by extension” was reread. It agrees with the existing counit/evaluation statement;
no false or ill-typed clause was found that would justify a section 1(C) statement
correction. Removing citations merely to escape the graph check would not be a
source-based correction. Section 1(B) permits only `lean` repairs of dependency
nodes, which cannot remove these graph paths. The delivery wrapper also expressly
rejects removing statement or proof dependencies without a statement correction.

The gate is `tools/nt_incremental2.py`, `local_findings`: it checks every outgoing
edge of a touched node, including unchanged edges, and explicitly rejects existing
cycles involving a delivered node. Its `check` function does not subtract inherited
cycle findings. Thus rebasing the unchanged mathematical packet cannot pass this
preflight. No launcher or project tool was edited, and no direct Git command or
repository write was performed. The saved Lean work is retained. A maintainer must
repair the upstream graph or authorize a dependency repair before delivery can pass.

Repair-audit validation: the explicit scompile.py call passed both namespaces
(sandbox 9.5 seconds; library 7.1 seconds), with no warnings or errors.

## Dispatcher retry audit, 2026-10-23

The prescribed first action on the saved packet was repeated:
`deliver2.py Q08 lem-sf-ramified-reduction-comparison-square --no-push`.
It refreshed the delivery base through the authorized wrapper, staged the three
packet files, and exited 1 with exactly the same five inherited cycle findings.
It reported no other preflight failure and pushed nothing.

A fresh read-only comparison of the sandbox node with the current shared node
found only the saved `lean` record and the addition of
`def-coef-finite-coefficient-stages` to `stmt_deps`. In particular, `statement`,
`proof`, and `proof_deps` are identical. A breadth-first traversal of the current
base graph independently reproduced all five return paths listed above. The
first four rejected edges belong to both base dependency lists; the transport
edge belongs to the base `proof_deps`. Thus removing the added Stage definition
edge cannot remove any of the five reported cycles.

The mathematical source paragraph was reread again and still agrees with the
node's counit/evaluation characterization. No source-based correction was found.
The repair boundary is explicit in `tools/node_fields.py`: lines 87--92 reject a
new `statement_change` with an unchanged statement, and reject a change in proof
or proof dependencies without a statement correction. Section 1(B) changes only
the Lean record of a dependency, leaving the offending graph paths intact.
Changing an unrelated node's dependencies, fabricating a statement correction,
or patching the validator is outside the authorized packet repair.

The actual refusal is `tools/nt_incremental2.py`, `local_findings`: its loop tests
every outgoing edge of a touched node and rejects an existing return path even
when the edge is unchanged. The required tool therefore refuses this otherwise
unchanged stage-2 packet until the upstream graph is repaired. This is the
remaining tool-policy failure, not a missing declaration or compiler failure.

The separate prescribed `scompile.py` validation was repeated successfully:
sandbox namespace 9.5 seconds, library namespace 7.1 seconds, exit 0, no warnings
or errors. The saved Lean module and node were retained without an unchanged
re-push; only this report was extended with the fresh diagnostic and audit.


## Current repair retry: independently reproduced blocker, 2026-10-23

The first saved-packet dry run and a second refreshed dry run both exited 1 with
exactly the five cycle findings in the return. Neither run pushed anything.
An explicit scompile.py call passed in both namespaces (sandbox 9.5 seconds,
library 7.1 seconds), exit 0, without warnings or errors.

A fresh JSON comparison against the shared base found only `lean` and
`stmt_deps` changed. The sole added edge is
`def-coef-finite-coefficient-stages`; no edge was removed. A read-only
breadth-first traversal independently reproduced all five return paths. The
first four rejected dependencies are already in both base dependency lists;
`lem-sf-finite-free-etale-proetale-transport` is already in base `proof_deps`.
All paths return through `lem-coef-finite-free-extension` to this item.

The source paragraph beginning “For two field extensions, or a quotient followed
by extension” still states the equality of the same counit/evaluation composites
and evaluation/double-dual compatibility. No source-based statement correction
was established. The node still has no landed Lean record on the shared base.

The refusal is precisely tools/nt_incremental2.py lines 61–64: it checks every
outgoing edge of each touched node, including unchanged edges, and rejects an
existing return path. Section 5 of coord/brief-stage2.md permits only `lean`
changes on a dependency node. tools/node_fields.py lines 87–92 also rejects
proof/dependency changes without an actual statement correction. Thus this
stage-2 packet cannot repair the inherited graph under its authorized field
rules. No mathematical statement was fabricated or changed to evade the gate;
no project or launcher tool was edited. The saved module and node are retained.
The needed external repair is removal of the erroneous upstream dependency
paths by the maintainer, or a maintainer correction of the inherited-cycle gate.


## Fresh saved-packet repair verification, 2026-10-23

The required initial `deliver2.py --no-push` was run on the retained packet;
it exited 1 and reproduced all five returned cycle rejections. A fresh
read-only comparison with the current shared node found only `lean` and the
addition of `def-coef-finite-coefficient-stages` to `stmt_deps`. No statement,
proof or existing dependency edge differs. A breadth-first traversal of the
current shared DAG reproduced a return path for each of the five rejected
edges; the first four occur in both base dependency lists, and the transport
edge occurs in base `proof_deps`. All five paths pass through
`lem-coef-finite-free-extension` immediately before returning to this item.

The source paragraph about a quotient followed by extension was opened again.
It states equality after transposing under the same adjunction, and evaluation
and double-dual compatibility. No mathematical defect was established that
would authorize changing the statement or removing its cited comparisons.
`coord/brief-stage2.md` sections 1(B), 1(C) and 5 permit only a Lean-record
repair of another existing node, and proof/dependency removal only as forced
by an actual source-based statement correction. `tools/node_fields.py`
`check_statement_change` enforces that boundary. In contrast,
`tools/nt_incremental2.py` `local_findings` explicitly rejects existing cycles
through any touched node, including unchanged outgoing edges. Thus the
required wrapper refuses the packet for base graph faults that this stage-2
packet is not authorized to repair. No tool was patched, no dependency was
silently dropped, and no artificial statement correction was made.

The explicit prescribed `scompile.py` run succeeded again, exit 0, in both
namespaces: sandbox 9.5 seconds and library 7.1 seconds, no diagnostics.
The saved mathematical packet is retained. A final dry run is performed after
this report update; delivery cannot be pushed unless that gate passes.

## Successful repair verification, 2026-10-23

The current saved-packet dry run now passes: `deliver2.py Q08
lem-sf-ramified-reduction-comparison-square --no-push` reported
`OK (dry run): commit 32388e08c30 passes the preflight and compiles; nothing pushed`.
The preceding blocker audits above are historical and no longer describe the
current base. A fresh traversal of the current shared DAG found no return path
from any of the five dependencies named by the immutable-head return to this
item. The upstream graph repair therefore resolves every returned cycle without
a mathematical statement change or a dependency deletion in this packet.

The saved module and node are retained. The final self-check reread the complete
statement and its real helper definitions against the node and source paragraph.
The recorded Lean signature occurs verbatim in the module; the module uses
explicit universes and disables auto-implicit binders; all lines are at most
100 characters; the JSON has the required layout. The only `sorry` is the whole
proof of the named item theorem. No statement or proof-dependency correction is
needed. The passing dry run compiled the delivered file on the server and
completed the current maintainer preflight.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
