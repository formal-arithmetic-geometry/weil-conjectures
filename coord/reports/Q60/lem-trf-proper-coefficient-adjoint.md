# Worker report: lem-trf-proper-coefficient-adjoint

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proper-coefficient-adjoint.json`: statement item, split into three proof steps, no new nodes.
- `citations.json`: nine verbatim citation entries for the three proof steps.

## Attachments

None. The source checkout has no sorry-free declaration tagged `(blueprint: lem-trf-proper-coefficient-adjoint)` and no declaration stating the item exactly. The existing `ProperPushforwardDiagram.pushforwardCoeff` definition only defines the coefficient map and does not prove this exceptional-adjoint formula.

## WANTED:

None.

## Not duplicates

No new nodes were created. The existing `def-trf-coefficient-pushforward` node defines the proper coefficient pushforward and is cited as the construction used by the proof; it does not state the item's exceptional-adjoint conclusion.

## Inherited metadata and continuation

The inherited creation record Q74 / `lem-trf-trace-triangle-compatibility`, unit `sk-i-additivity`, and blueprint ancestry are correct and retained. The earlier report incorrectly said the creation record had changed and that a unit repair was required. This is the general proper-pushforward mate calculation used in the ancestor's closed graded identification (current proof step 4); it belongs below that argument without moving the unit. The current main-20261015 ancestor proof explicitly invokes the chapter's proper coefficient pushforward in its induced-morphisms paragraph. No statement correction or route departure is needed.

## Review by Q60

I read the full item statement, the existing `def-trf-coefficient-pushforward`, `def-trf-admissibility`, `prop-functor-package`, and the Varshavsky source at §0.3(a), §1.1.6(a)(ii), §1.5.9 and §5.3.3. The hypotheses are unchanged: $A=A_{E,n}$, separated finite-type schemes, proper $f$ and $g$, both leg relations, constructible finite-Tor $K$, and the specified exceptional adjoints. No Cartesian leg square or properness over $k$ is introduced.

Step 1 only unfolds the existing coefficient-pushforward definition. It uses the exact statement that the coefficient map is $\delta\circ Rg_*u\circ\gamma$, that $\delta$ is the exceptional adjoint of the displayed compact-support composite, and that proper maps identify $Rf_!$ with $Rf_*$. Step 2 uses the constructible adjunction supplied by `def-trf-admissibility`; I expanded the mate calculation with the unit, counit naturality, and triangle identity, rather than citing the stronger optional ambient adjunction clause of `fix-prop-adjunctions`. Step 3 cites `thm-sf-comp-composition` for the canonical natural comparison and `lem-sf-proetale-constructible-origin`(ii) for its etale-origin domain, then checks naturality of the specified comparison $\Xi_1$ at $u$, then applies functoriality of $Rf_*$ and the defining equation $v=\varepsilon_{c_1}\circ Rc_{1!}(u)$ to obtain exactly the three arrows in the item. Each citation quote in `citations.json` was copied verbatim from the cited node statement and checked mechanically.

I tested the formula on the identity diagram ($f=g=1$, where $\gamma$ and $\Xi_1$ are identities and the formula reduces to $v$), on $u=0$ (both sides are zero), and on $K=0$. These edge cases do not require Cartesianity or properness of a structure morphism. Mathlib searches were rerun with LeanFinder, LeanSearch, Loogle, and grep; all hits were ordinary sheaf/module adjunctions or linear-map adjoints and none states this derived constructible coefficient comparison. The earlier attempt reported a successful server `check_dag`; this continuation runs the complete required delivery dry run again.

## Additional review on continuation by Q60

I reopened Varshavsky §0.2, §0.3(a), §1.1.6(a)(ii), §1.5.9 and §5.3.3, the current ancestor proof, the chapter/unit records, and each cited DAG statement. The source uses `c_2! c_1*`; exchanging its two legs gives our `Rc_1! c_2*`. In §1.1.6(a)(ii) properness supplies the exchange without a Cartesian square, exactly as required here. The paper's adjoint pushforward is the three-arrow composite, and our explicit unit/counit calculation verifies that the coefficient-map definition has that transpose.

For C1/C4, step 1 cites the actual defining formula for delta and the coefficient map in `def-trf-coefficient-pushforward`, the specified constructible adjunction in `def-trf-admissibility`, and the proper comparison from `prop-functor-package`(3). Step 2 now also cites the coefficient-pushforward definition: delta = R(q) eta and the inverse transpose epsilon L(delta) are expanded, naturality moves R(q) through the counit, and the triangle identity cancels epsilon L(eta). This is the elementary two-line argument written in the step, not a new generic mate lemma. Step 3 takes the explicitly natural composition isomorphism from `thm-sf-comp-composition`; its field, finite quotient coefficient, separated finite-type morphism and bounded-below hypotheses hold. Its etale-origin requirement is checked using `lem-sf-proetale-constructible-origin`(ii) on M and N, whose finite-Tor constructible domains are supplied by the admissibility datum. The proper comparisons defining Xi_1 are natural, so naturality at u and functoriality of P give P(v) Xi L(gamma). Every cited step/node pair has its own verbatim statement quotation in citations.json.

For B1-B10 and C5, no new nodes are created: the unit and the existing coefficient-pushforward definition already supply the geometric construction, and the remaining algebra is elementary. Searches by the item tag and by adjoint/pushforward coefficient terminology in WeilConjectures found only the existing definitions in ProperPushforward.lean, not a theorem giving this full formula. Whole-DAG and blueprint searches found no duplicate theorem. Mathlib search results and prior recorded results were read and retained; the inspected ordinary module-sheaf adjunction and exponentiable-morphism composition declarations concern other functors. The malformed Loogle query is recorded as unavailable rather than as absence evidence; successful semantic queries in multiple phrasings and grep provide the no-match search. No Stacks fact is used, so inventing a Stacks source tag would be inappropriate.

For D1-D5, the steps carry the entire calculation and do not relocate a clause into a child. For E1-E7, f and g alone are used as proper maps, c_1 and b_1 have the specified constructible exceptional adjunctions, all objects and maps have the types displayed in the item, and neither structural properness nor Cartesianity enters. The identity diagram, zero coefficient arrow, and zero complex give the expected identity/zero calculations. The closed specialization used by the ancestor is an instance of the same formula. No claimed theorem is inferred from a definition's proof. All steps are shorter than 2000 characters, and there is no concealed standard comparison argument. Cross-unit generic tools are proposed only in split_report.tool_uses; maintainer-owned tool_uses are untouched.

## What I could not finish

Nothing remains in the mathematical split. The item has three steps, zero new nodes and zero Mathlib leaves. Delivery checks and their result are recorded below when completed.

## Validation

The first complete server delivery dry run exited successfully: `OK (not pushed) deliver/Q60/lem-trf-proper-coefficient-adjoint at a6539efbcd: preflight passed`. The local continuation checks verified all nine quotes, exact step/citation coverage, and equality of proof_deps with the union of step uses. All direct dependencies exist and no dependency path leads back to this item. The broad local read encountered fourteen missing inherited dependency IDs in the shared snapshot; these are not new direct dependencies, and the server baseline-aware preflight passed. A final dry run is performed after this report update before pushing. No Lean file was written and no compiler or build tool was invoked.
