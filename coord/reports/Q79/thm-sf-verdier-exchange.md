# Repair report: thm-sf-verdier-exchange

## Files written

- `dag/nodes/sec-six-functors/thm-sf-verdier-exchange.json`: statement unchanged; domain check and short assembly.
- `dag/nodes/sec-six-functors/lem-sf-dualizing-composition-coefficient-mate.json`: statement, unsplit, no Mathlib match. Constructs the all-stage composition mate with its Hom characterization and coefficient-unit compatibility equation.
- `dag/nodes/sec-six-functors/lem-sf-derived-hom-substitution-coherence.json`: statement, unsplit, no Mathlib match. Proves the actual internal-Hom substitution natural isomorphism's signed-shift and evaluation-defined coefficient squares, including the direct-image mate.
- `citations.json`: verbatim statement quotations for every use in the parent.

## Attachments

None. The read-only project file `lean/Sheaf/Paper/VerdierExchange.lean` ends in `verdier_exchange := by sorry`. Its stage, substitution, and comparison definitions are useful construction data, not proofs of these two assertions. The upstream `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex` and `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek`, `lean/WeilConjectures/SixFunctors/Etale/Derived/TensorHom.lean:401,418`, only give ordinary-etale finite-ring `Nonempty` isomorphisms under compactification hypotheses. They do not supply the all-stage canonical coefficient equations. The exact item-tag search found no finished project attachment.

## WANTED

None. The source is the available main-20261015 blueprint proof, Steps 1–3; the extraction is the formal, agent-written elaboration of that source already present in the returned split. No SGA route or substitute geometric existence theorem is used.

## Return repaired

The human's return requires spreading all 3586 characters of the old argument into separately assignable work, with at least two new statement-only nodes and at most 3000 characters in the parent. Both children have status `unsplit`, empty proof and proof_deps, source and exact blueprint places, three kinds of logged Mathlib search, and full self-contained hypotheses. They are comparable coherence tasks: the first transposes the composition comparison and proves its coefficient equation; the second derives the canonical internal-Hom/direct-image coefficient square from evaluation and proves the signed shift equation. They can be assigned independently: the second takes an arbitrary compatible target isomorphism, rather than depending on the first or on Verdier exchange.

Old Step 1 remains verbatim as the parent's typing check. Old Step 2, including every Hom bijection and its orientation, is the first child's Hom characterization. The unit evaluation is that child's c_f. Old Step 3 remains in the parent, now citing the substitution child as well. Old Step 4's unit/composition/counit substitution becomes the first child's explicit kappa/beta equation. Its internal-Hom comparison, contravariant naturality, and shift argument become the second child's sigma and signed-shift equations. The parent's final step instantiates those equations and pastes the two ingredients' squares. The verbatim old steps below retain the entire argument for the workers who will split the children. No statement or Lean module was changed.

The sandbox initially contained only four hidden dispatcher markers, not the claimed delivered JSON/report/log. I copied the current repository's returned node, read its Q17 report and retained that report as `previous-report.md`; retained source, searches, blueprint-update and Lean metadata in the copied item; and ran new logged searches for the new children. The live item still has exactly the four steps and 3586-character argument named in the return, so there was no competing mathematical repair to rebase. `returned-node.json` records that read-only starting version locally. These local evidence files are not DAG nodes.

## Review by Q79

I read the item and current blueprint statement and proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/`, the `blueprint_update`, the chapter and unit records, GOAL, the stage-1 brief, stages/1-dag, the three route levels in SETUP, and delivery-errors B–E. The source has the same composition-mate, tensor–Hom specialization and compatibility route. The item statement is unchanged, including its constructible rather than ambient exceptional adjoint and its four coefficient stages. The old Q17 report remains available, with its prior search conclusions and statement-expansion history; this is a repair of the returned proof workload, not a new target formulation.

For the mate child I read blueprint Step 1 and Step 3, A1/A4/A5 of `def-sf-datum`, the unit/dualizing formula of `def-sf-pf`, and `VerdierExchange.lean`'s real definition `composition` and its `ScalarConclusion.dualizing` equation. The three Hom adjunctions are all between the displayed finite-Tor categories. The compositor points from Ra_X! to Ra_Y! Rf!, so precomposition by alpha has exactly the displayed direction. This yields Rf^! Ra_Y^! to Ra_X^!, not its inverse. Both structure morphisms are separated finite type, because X,Y are separated finite type over k. Kappa_X and Kappa_Y include the coefficient-unit map after the exceptional comparison; the coefficient equation has common source T_X Rf^!omega_Y and target omega_X at the new stage. It is a new assertion to prove from A1/A4/A5, not a defining axiom or a choice of an unspecified isomorphism. No A6 or ambient admissibility is used. A future proof must perform the old unit–composition–counit calculation recorded below, including coefficient change before evaluation.

For the substitution child I read blueprint Steps 2–3, the actual `substitute`, `StageScalar.dualX`, `StageScalar.star` and `ScalarConclusion` constructions in the same Lean source, and the operation definitions `def-weil-derived-pullback-tensor-hom`, `def-weil-derived-direct-image`. The child is about arbitrary U,V and c and compatible coefficient identifications u,v; it neither mentions nor proves Verdier exchange. Its Hom coefficient map is fixed as the transpose of extended evaluation, its direct-image comparison is the specified counit mate, and sigma composes them in the only typed order. The equality v T(c)=c' u makes its two routes have the same endpoint; this is a hypothesis on arbitrary substitution data, not a hidden assumption about the particular dualizing mate. The source-shift convention is the signed degree-d multiplier (-1)^(rd); it has shift -r in the output. This extracts the old shift identification rather than replacing it by an unsigned arbitrary isomorphism. Integral tensor and coefficient maps remain completed, and fields use the recorded scalar images. No claim of invertibility for arbitrary ambient Hom coefficient arrows is made: only j_c is asserted invertible because c is. A future proof must check the evaluation-transpose equation and localization/field passage, so this child is more than a renaming of the two-line assertion that a functor preserves isomorphisms.

I opened every statement the parent cites. In parent Step 1, `def-weil-finite-tor-amplitude` gives the uniform integral interval and field-stage equality, `def-sf-datum` gives the typed A1 adjunctions, and `def-sf-pf` names the unit and omega. Rank-one free degree zero has interval [0,0], independent of n, so applying A1 is correctly typed. This remains an elementary domain calculation, with no new elementary node. Parent Step 2 uses the first child's displayed Hom characterization and its coefficient equation, both in its statement. Parent Step 3 uses `lem-sf-tensor-hom` with M as given and N=omega_Y from Step 1, explicitly inverts its arrow, and uses the second child's j_c. The endpoint identifications are precisely `def-sf-pf`. Parent Step 4 uses the first child's coefficient equation with u=Rf^!(kappa_Y) beta_f and v=kappa_X as the second child's input compatibility. It then uses the second child's naturality, sigma square and negative-shift square and the explicit compatibility clauses of `lem-sf-tensor-hom`. Pasting gives the parent's full conclusion. The citations file quotes the actual statements including their hypotheses, rather than taking a fact from a cited proof.

I checked B1–B10 and C1–C8: children have no proofs, no proof sketches in their statements, complete object/parameter introductions, ordinary TeX, no invented source tags, exact blueprint ancestor and places, and real search records. The common notions and every operation used in their statements have the defining nodes in stmt_deps. No child assumes a conclusion of the parent; neither is the parent or a standalone clause of it. The parent alone specializes tensor–Hom to omega_Y and assembles the exchange. The source's whole argument is accounted for by the old-step map above. The parent has no step over 2000 characters and its total is below 3000; no long unexamined comparison remains there. The children have no proof dependencies, so neither adds a cycle through the parent. All new proof edges are within the item's unit. No off-unit theorem tool is introduced.

I searched the entire DAG by titles, full statement keywords and the exact geometric expressions (including a_Y, dualizing, mate, composition, coefficient and substitution), and ran `tools/blueprint_refs.py ancestor` and searches for composition mate, dualizing, mate coefficient, mate, coefficient comparison, internal Hom shift, dualizing composition and substitution. I read the plausible overlaps named in Not duplicates below. Mathlib semantic searches were run with two formulations for each task, plus Loogle, LeanSearch and source grep through msearch.py. The generic conjugation source `Mates.lean:425–435`, mate pasting at 170/209, and `CompositionIso.lean:64–85` were read. They can prove the underlying formal constituent but do not themselves state the all-stage coefficient-unit equation. For substitution I read evaluation naturality at `Monoidal/Closed/Basic.lean:109`, and `BifunctorShift.lean:77–110`; these do not by one specialization supply the completed/rational/common-stage evaluation and ordinary-direct-image square. The search log includes one rate-limited LeanSearch request, recorded as unavailable in the log; successful alternative queries are recorded in the children. No unavailable query is described as a negative mathematical result.

Small cases: f=id gives the identity-normalized composition mate and kappa equation; n=1 still uses the free unit and no assertion that all modules are perfect. For a non-field A_(E,n), U,V and M explicitly retain finite-Tor membership. With M=0, or X empty, the substitution and exchange are zero-object isomorphisms and both squares agree. With c=id and u=v, sigma's equation is the same arrow on both sides. With r=0 the source-shift equation is naturality for the identity; with odd r and an odd Hom degree, both postcomposition routes receive the same (-1) sign, since c has degree zero. This checks the sign rather than silently deleting it. The integral assertion keeps actual completed maps; the rational stages never acquire a nonexistent reduction to A_(E,n).

Corrections during this reading: separated the generic mate construction from the genuinely required coefficient equation, instead of creating a duplicate bare categorical mate node; generalized substitution to arbitrary compatible U,V,c so it is independently assignable; fixed the coefficient-square endpoints and explicitly normalized h by evaluation and gamma by its counit. All four original arguments are retained below. The parent remains the same theorem with the same hypotheses.

## Not duplicates

lem-sf-dualizing-composition-coefficient-mate vs lem-sf-mate: the latter's statement invokes the finite-level thm-sf-comp-composition and the obsolete ambient-adjoint restriction parenthetical; it has no coefficient-unit kappa/beta equation. The new child uses A4 on all four constructible coefficient stages and asserts that equation, not merely generic conjugation.

lem-sf-dualizing-composition-coefficient-mate vs lem-weil-boundary-dualizing-composition: the existing statement is finite-ring ordinary-etale ambient right adjoints, with pro-etale transport for closed immersions; it does not give all-stage constructible coefficient coherence for arbitrary f.

lem-sf-dualizing-composition-coefficient-mate vs thm-trf-dualizing-complex-composition: that is the finite coefficient admissible d:F->X assertion, without the all-stage Hom characterization and coefficient square.

lem-sf-dualizing-composition-coefficient-mate vs lem-sf-identification-coefficient-transport: the latter treats only the identity structure compositor and proves its counit normalization; the new node treats general f and the dualizing coefficient square.

lem-sf-dualizing-composition-coefficient-mate vs lem-coef-finite-dualizing: finite quotients identify the unit-valued dualizing objects individually there, not their composition mates for general f at all stages.

lem-sf-dualizing-composition-coefficient-mate vs prop-coef-integral-dualizing: integral existence, reduction and value-at-unit representation are given there, not the compatibility of the f/a_Y composition mate.

lem-sf-derived-hom-substitution-coherence vs lem-pur-derived-internal-hom-shift-left: the latter supplies a source-shift isomorphism natural in its target; the new node fixes the evaluation-defined coefficient/direct-image substitution square at all stages as well. It will reuse the existing shift fact, not replace it.

lem-sf-derived-hom-substitution-coherence vs lem-coef-slice-hom-source-shift: the existing statement is restriction to a slice of one ringed site with specified models, not coefficient extension/reduction and ordinary direct image.

lem-sf-derived-hom-substitution-coherence vs lem-sf-even-line-hom-shift: that is the tensor comparison for an even shifted invertible line, not substitution by arbitrary degree-zero target isomorphisms and coefficient maps.

lem-sf-derived-hom-substitution-coherence vs lem-sf-etale-hom-complex-pullback: the existing chain-level ordinary-etale inverse-image comparison is not the completed/rational/common-stage internal-Hom substitution and ordinary-direct-image coefficient square.

lem-sf-derived-hom-substitution-coherence vs def-sf-verdier-exchange-data: this is construction data and compatibility predicates only; it explicitly does not assert the stage or scalar conclusion. The new child proves a narrower, general substitution assertion with those actual evaluation normalizations.

Both new nodes vs fix-cor-verdier-exchange and sk-thm-sf-verdier-exchange: those restate the full exchange theorem; neither states these constituent Hom/mate coefficient identities, and neither is used as a proof dependency.

## Unfinished

The two new children deliberately await other workers' stage-1 proofs. The parent is a complete one-level assembly. Required remote dry run and delivery are performed after writing this report.

## Preserved returned arguments

The following is verbatim from the returned current repository node, not shortened or replaced by the new statements. It is the argument allocation record for the two future workers.

### Returned Step 1

The coefficient unit $\Lambda_s$ belongs to $D^b_{ctf}(s,\Lambda)$: at a finite stage it is the constant rank-one free module in degree zero, whose tensor with a degree-zero module is that module; at the integral stage its reductions are these same rank-one units, with the common Tor interval $[0,0]$; the field stages use the rationalized and common-stage units and their defining equality $D^b_{ctf}=D^b_c$ [def-weil-finite-tor-amplitude]. Axiom (A1) of [def-sf-datum] is imposed on the finite-Tor categories, so its right adjoint $Ra_T^!$ takes this unit to an object of $D^b_{ctf}(T,\Lambda)$, for $T=X,Y$. By [def-sf-pf] this object is $\omega_T$. The same typed axiom places $Rf_!M$ in $D^b_{ctf}(Y,\Lambda)$. Thus every dual and every input of the tensor–Hom theorem below has its required domain. No use of Verdier biduality (A6) is made.

Cited nodes: def-weil-finite-tor-amplitude, def-sf-datum, def-sf-pf.

### Returned Step 2

Use axiom (A4) of [def-sf-datum] at the composable pair
$X\xrightarrow fY\xrightarrow {a_Y}s$ to obtain the supplied comparison
\(\alpha:Ra_{X!}=R(a_Y\circ f)_!\xrightarrow{\sim}Ra_{Y!}Rf_!\).
For objects $K$ and $L$ in the finite-Tor categories, the three A1
adjunctions and their pasted units and counits give the natural chain
$$
\begin{aligned}
\operatorname{Hom}_X(K,Rf^!Ra_Y^!L)
&\cong\operatorname{Hom}_Y(Rf_!K,Ra_Y^!L)\\
&\cong\operatorname{Hom}_s(Ra_{Y!}Rf_!K,L)\\
&\xrightarrow{h\mapsto h\circ\alpha_K}
\operatorname{Hom}_s(Ra_{X!}K,L)\\
&\cong\operatorname{Hom}_X(K,Ra_X^!L).
\end{aligned}
$$
Thus Yoneda gives the mate isomorphism $Rf^!Ra_Y^!L\cong Ra_X^!L$;
this is the explicit conjugation calculation, with no appeal to the
finite-level composition theorem. Evaluating at $L=\Lambda_s$ and using
[def-sf-pf] gives
$c_f:Rf^!\omega_Y\xrightarrow{\sim}\omega_X$.

Cited nodes: def-sf-datum, def-sf-pf.

### Returned Step 3

Apply [lem-sf-tensor-hom] with the given $M$ and with $N=\omega_Y$, whose finite-Tor membership was checked in Step 1. Invert that canonical isomorphism, and follow it by the image of $c_f$ under the functor $Rf_*R\mathcal H om_X(M,-)$. The resulting composite is
$$
D_Y(Rf_!M)=R\mathcal H om_Y(Rf_!M,\omega_Y)
\xrightarrow{\sim}Rf_*R\mathcal H om_X(M,Rf^!\omega_Y)
\xrightarrow{\sim}Rf_*R\mathcal H om_X(M,\omega_X)=Rf_*D_X(M).
$$
The equalities use precisely the dualizing and Verdier-dual notation of [def-sf-pf]. Both arrows are isomorphisms, so this defines the required canonical isomorphism.

Cited nodes: lem-sf-tensor-hom, def-sf-pf.

### Returned Step 4

The tensor–Hom arrow in Step 3 has the naturality and finite-reduction, scalar-extension and shift compatibilities asserted in [lem-sf-tensor-hom]. For the second arrow, $c_f$ is independent of $M$, so bifunctoriality of internal Hom makes it natural in $M$. For a permitted coefficient comparison, apply it to the explicit unit–composition–counit Hom-adjunction chain in Step 2. Axiom (A5) of [def-sf-datum] identifies the images of those units, composition comparisons and counits with the corresponding ones after coefficient change. Substituting these three identities in that expression gives the same mate, hence the same $c_f$, after coefficient change; applying the internal-Hom comparison gives the commuting square for the second arrow. Here finite reduction is used only at finite/integral stages and scalar passage only on the domains specified by (A5). Finally, for a shift $M[r]$, the second arrow is $Rf_*R\mathcal H om_X(M[r],c_f)=Rf_*(R\mathcal H om_X(M,c_f)[-r])$ under the usual derived-Hom shift identification: a degree-zero map in the second variable is unchanged by shifting the first variable. Thus it has the same shift compatibility. Pasting these squares with those of the first arrow proves all asserted compatibilities of their composite.

Cited nodes: lem-sf-tensor-hom, def-sf-datum.
