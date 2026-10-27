# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-permissible-coordinate-chart.json`: existing statement unchanged; five-step assembly of 2257 characters, replacing the returned 4217-character proof.
- `dag/nodes/sec-trace-formula/lem-trf-parameter-blowup-algebra-regular.json`: statement, unsplit, no Mathlib match; chart regularity, exceptional quotient and complement.
- `dag/nodes/sec-trace-formula/lem-trf-parameter-blowup-coordinate-quotients.json`: statement, unsplit, no Mathlib match; simultaneous coordinate quotients, dimension drops and extension to local parameters.
- `citations.json`: a verbatim statement quote for every citation of every assembly step.

## Attachments

None. Searched `lean/WeilConjectures` for the blueprint tag, permissible charts, coordinate blowups and parameter charts. The matching project module `lean/Sheaf/AlgebraicGeometry/PermissibleCoordinateChart.lean`, theorem `AlgebraicGeometry.PermissibleCoordinateChart.permissible_coordinate_chart` at line 159, ends in `sorry` at line 202. Its docstring has the same five-step plan, and the seven conjuncts match the item's presentation, regularity, reduced boundary, local parameters, coordinate intersections, reduced marked union and strict-transform kernels. It is not an attachment. No Lean was written and no compiler was run.

## WANTED

None: ILO and the Stacks source files needed here are present.

## Repair and comparison with the returned baseline

The dispatcher supplied an empty sandbox (only its .brief marker files), not a retained delivery. There was no report, citations file, searches log or prior split to dry-run first. Copied the current item from the read-only shared repository, whose five proof steps have exactly the returned lengths 1068, 530, 1325, 872 and 422. No git command was run in that repository. The source, statement, Lean metadata, existing searches and blueprint fields have been retained. Delivery tools rebase the owned split fields onto the server's current main; all writes made directly by this worker are in this item's sandbox.

The return has one substantive instruction: spread the 4217-character argument across at least two comparable new unsplit nodes, retaining every argument and reducing the assembly to at most 3000 characters. The two new nodes have no proof steps or proof dependencies. They can be assigned separately: one proves regularity by the exceptional-divisor/complement argument, the other proves the substantially different simultaneous-coordinate quotient and cotangent assertion. Neither restates the whole parent: neither mentions the boundary B, the marked sub-boundary I, inverse images or strict transforms. The first has no boundary-intersection hypothesis at all; the second assumes chart regularity rather than repeating that argument. The normal rule against extracting a mere clause is superseded here by the explicit human re-split instruction, while its purpose is respected by using reusable algebraic statements with independent arguments.

Allocation: old Step 1's parameter permutation and chart presentation stay in assembly Step 1; its polynomial exceptional quotient, chart-generator injectivity, localization away from the generator and regular-local lifting above it belong to the first new node. Old Step 2's substitutions and support/reduction computation remain in Step 2, now with the full product formula. Old Step 3's two local cases, simultaneous cotangent independence, completion to parameters, regular quotients and codimension belong to the second new node. Its unit/empty local intersection case is explicit. Old Step 4's schematic strict-transform closure and all three index cases remain in Step 4, with the cancellation/kernel computation written out. Old Step 5's overlap compatibility, final union and empty-I case remain in Step 5. The original five-step proof is preserved verbatim below, to make the allocation inspectable.

The old Step 3 said that the chart relations alone imply cotangent independence. That sentence omits the needed regularity and dimension argument at nonclosed primes. I have not used it as a black box. The new statement isolates precisely the missing simultaneous assertion, and the following quotient argument explains why it is true without an unjustified cotangent inference.

## Arguments assigned to the new nodes (guidance, not proof fields)

For the regularity node, permute the parameters to start with t_j and the remaining center parameters. The existing regular-parameter theorem gives a regular sequence and a regular quotient by all center parameters. The existing 0BIQ presentation identifies the algebra with the blowup chart, so the existing chart-generator lemma makes multiplication by t_j injective. Modulo t_j the relations become t_i=0 for i in J, leaving a polynomial ring over the regular local parameter quotient. The polynomial regularity node, followed by localization, makes its local rings regular. The chart is Noetherian since it is a finite polynomial quotient of R. Away from t_j substitute u_i=t_i/t_j to obtain R[1/t_j]; every corresponding local ring is a localization of R. Above t_j use the singleton regular-sequence lifting criterion (00NU) with the regular exceptional quotient. These are all the arguments of old Step 1, with no coefficient field or smoothness assumption.

For the coordinate-quotient node, fix disjoint sets U of ratio labels and K of outside-parameter labels. Setting u_i=0 for i in U forces t_i=0, leaving

\[
A/(u_i:i\in U,t_k:k\in K)\cong
(R/(t_i:i\in U,t_k:k\in K))[u_h:h\in J\setminus(\{j\}\cup U)]/(t_h-t_j u_h).
\]

The base quotient is regular local, with the remaining parameters as parameters. This is another parameter chart with center labels J minus U, still containing j, and therefore is regular by the first node. If the exceptional coordinate is also set to zero, the quotient is instead the polynomial ring

\[
(R/(t_i:i\in J,t_k:k\in K))[u_h:h\in J\setminus(\{j\}\cup U)],
\]

again regular. The coefficient/variable maps in each direction give these presentations, not an appeal to the internal proof of a cited node. To check a simultaneous selected sequence, order the outside parameters first, then the selected ratios, and the exceptional parameter last if selected. After each prefix, the displayed presentation is a chart over the corresponding regular parameter quotient. The next outside parameter or ratio is a nonzerodivisor by the existing individual-coordinate lemma applied to precisely that smaller chart; the exceptional parameter is a nonzerodivisor by the chart-generator lemma. At primes containing all selected equations, all prefix quotients remain nonzero and localization preserves these injectivities. Dimension drops by one at each step. For the entire vanishing coordinate family at a fixed prime P, the final local quotient is regular, and the dimension drop equals the number of labels. Its cotangent dimension is therefore dim(A_P) minus that number. The kernel of the cotangent-space surjection is spanned by the selected coordinate classes; comparing dimensions in the regular source and quotient shows those classes are independent. Extend them to a cotangent basis and lift that basis to generators by Nakayama: in a regular local ring these are a regular system of parameters. If t_j is invertible the same presentation identifies surviving ratios with associates of original parameters; if it vanishes, the polynomial exceptional quotient and the injective exceptional parameter give the argument above. This replaces the old bare independence assertion while preserving both cases and every desired intersection/dimension conclusion.

## Not duplicates

Searched the whole DAG by `4.2.9`, `0BIQ`, coordinate intersections, cotangent independence and regular blowup charts, and searched all blueprint nodes with `tools/blueprint_refs.py search` for `blowup regular`, `coordinate hyperplanes`, `cotangent`, `blowup`, `regular system`, `parameter blowup` and `coordinate quotients`. No blueprint node states either new algebraic lemma. Their ancestor is lem-trf-local-term-locality; the via list prepends this item to its existing ancestor path.

- lem-trf-parameter-blowup-algebra-regular vs lem-trf-blowup-chart-regular-sequence-presentation: the existing theorem gives a presentation for a regular sequence in any ring; it does not give regularity of the chart from a regular parameter system.
- lem-trf-parameter-blowup-algebra-regular vs lem-trf-chart-coordinate-nonzerodivisors: injectivity on individual coordinate quotients does not assert regularity of the chart or its local rings.
- lem-trf-parameter-blowup-algebra-regular vs lem-trf-smooth-center-blowup-geometry: the latter is for smooth finite-type schemes over Q, while this algebra result includes arbitrary mixed-characteristic regular local rings.
- lem-trf-parameter-blowup-algebra-regular vs lem-sfb-local-surface-maximal-blowup-geometry: dimension-two maximal-center geometry does not cover arbitrary dimension and coordinate centers.
- lem-trf-parameter-blowup-coordinate-quotients vs lem-trf-chart-coordinate-nonzerodivisors: the latter gives one-coordinate injectivity only; the new lemma gives all simultaneous quotients, local parameters and exact codimensions.
- lem-trf-parameter-blowup-coordinate-quotients vs lem-trf-nc-coordinate-blowup-branch-drop: the existing result only controls ratio factors for a center consisting of the entire given boundary, and does not include the exceptional equation or unchanged outside parameters. Its proof uses this item, so citing it back would be circular.
- lem-trf-parameter-blowup-coordinate-quotients vs lem-trf-marked-controlled-blowup-charts: the latter assumes smooth finite-type Q-schemes and a controlled ideal; it does not imply the mixed-characteristic local algebra statement.
- lem-trf-parameter-blowup-algebra-regular vs lem-trf-permissible-coordinate-chart: the new generic algebra statement extracts only old Step 1's regularity argument under the explicit re-split instruction; transforms and all boundary arguments remain above it.
- lem-trf-parameter-blowup-coordinate-quotients vs lem-trf-permissible-coordinate-chart: the new generic algebra statement extracts old Step 3's independent local-coordinate argument, for every chart coordinate, under the explicit re-split instruction; it assumes chart regularity and says nothing about transforms.

## Mathlib reading

Every newly recorded query was run through the prescribed msearch.py command and is in searches.jsonl. Each lemma has LeanFinder, Loogle, source grep and LeanSearch plus a second LeanFinder phrasing. The existing item's previous searches are retained. All services responded. Loogle's unknown identifier for the project-specific parameter definition is recorded exactly, and does not by itself justify absence. LeanFinder's regular-sequence localization results do not identify blowup coordinates or prove their simultaneous parameter assertion. Read Mathlib/RingTheory/RegularLocalRing/Polynomial.lean: MvPolynomial.isRegularRing_of_isRegularRing proves polynomial regularity, already represented by lem-trf-polynomial-ring-regular-base; it is not a blowup-quotient result. Read RegularLocalRing/Defs.lean:75: iff_finrank_cotangentSpace characterizes regularity but supplies no coordinate independence. Read ReesAlgebra.lean:39: it defines the graded subalgebra, not chart regularity. LeanSearch's two ringKrullDim quotient lemmas only give dimension drop once regularity of an element has already been proved. None is an exact match or one-line specialization of either new statement; both remain unsplit, with zero new Mathlib leaves.

## Review by Q02

I read ILO VIII, Lemma 4.2.9 on printed page 121 (PDF page 127), including the regular coordinates, chart ratios, exceptional equation and transformed product; I also read Remark 4.2.2(i) on printed page 118 (PDF page 124), which requires regular intersections and exactly the stated codimension, rather than only regular ambient charts. The two new nodes isolate the algebra behind the source's phrase local coordinates. Both introduce R, its full parameter system, J and j themselves. They have statement-only payloads, complete definition dependencies, precise source places, inherited chapter/unit, and searched blueprint ancestry. There are no new definitions or unrecorded non-elementary facts hidden in the assembly.

Step 1 uses the actual statement of lem-weil-pbc-regular-local-generators-regular-sequence: it permits any permutation and says the parameters are a regular sequence. The actual statement of lem-trf-blowup-chart-regular-sequence-presentation gives the quotient and the generator images for any regular sequence. The first new node says exactly that this quotient is regular. Its hypotheses require only the already given regular local ring and parameter system, nonempty J and j in J; it does not require j to be a boundary index.

Step 2 uses the definition of scheme reduction, which is the identity on underlying sets with nilpotents removed. The equation calculation is written explicitly; containment of a finite product in a prime means some factor belongs to the prime. The exceptional exponent is |J intersect {1,...,r}|, positive by the original hypothesis, even if j exceeds r. Thus the step does not accidentally assume j lies in the boundary. The reduced union means the reduced closed subscheme on that union of supports, so no uncited scheme-theoretic pullback/intersection identity is being assumed.

Step 3 uses the second new node's exact local-parameter, quotient and dimension conclusions. The boundary labels form a subset of the full labelled coordinate family; the exceptional, ratio and outside labels are distinct. Its regularity hypothesis is provided by Step 1. For a selected intersection at P, its ideal is Q with epsilon indicating whether the exceptional equation was selected; the count c is precisely the number of selected labels. A selected equation outside P is a unit, giving the empty local intersection. All other selected equations are in the maximal ideal, as needed for parameter quotients and codimension. I specifically checked the new statement at nonclosed primes; it does not claim the displayed coordinates generate the maximal ideal by themselves.

Step 4 uses the opened statement of lemma-nagata-chart-extended-ideal-principal, I A[I/a]=(a), to identify the off-center open. The opened definition def-nagata-strict-transform explicitly requires schematic closure. The opened statement lem-trf-chart-coordinate-nonzerodivisors supplies injectivity separately on A/(u_i) and A/(t_k), under exactly our R,J,j hypotheses. Successive cancellation makes the localization kernel exactly the relevant coordinate ideal. This is the elementary closure computation, not a claim that topological closure suffices. For i=j the intersection of V(t_j) with D(t_j) is empty; no variable u_j is introduced.

Step 5 is the finite-union support substitution from Steps 2 and 4, including the exceptional inverse image of M. Restriction of the same intrinsic inverse image and closure explains overlaps; no new gluing theorem is used. I empty gives a unit product and H empty, so only the exceptional support remains. Both quoted nodes in Step 1 filed in other units are generic tools; split_report.tool_uses retains the parameter theorem and principalization tool needed here. The proof remains on the same ILO coordinate route; no chapter/unit or target is changed and no SGA source is used.

Small cases checked: d=1, J={j}, where the algebra is R, there are no ratios and the exceptional equation is the original parameter; J all indices, where there are no outside parameters and the exceptional quotient is a polynomial ring over the residue field; proper J and selected outside coordinates; empty U,K and epsilon=0, giving Q=0 and dimension drop 0; all ratio coordinates selected, leaving a singleton-center chart over the parameter quotient; primes on and off t_j; and mixed characteristic R=Z_(p)[x]_(p,x), J={p,x}, whose p-chart has relation x=p u, regular exceptional quotient F_p[u], and simultaneous p=u=0 quotient F_p. This checks the hypotheses that a characteristic-zero smooth theorem would miss. At the generic prime no displayed coordinate is required to be a parameter. For I empty and for i=j the strict-transform edge cases are explicitly covered.

Checklist B1-B10: statement-only new nodes; all data and notions introduced/cited; TeX and exact source places; searches run and candidate sources read; blueprint duplicates and Lean attachments checked. C1-C8: every non-elementary assembly inference is one of the cited statements, all opened; quotes copied verbatim to citations.json; no use of a cited node's proof; no new cycle or route replacement. D1-D5: this is the human-mandated extraction of two different algebra arguments, not movement of the whole item into one node; the assembly still carries the actual transform calculation. E1-E7: hypotheses and small cases above were checked, and the insufficient old cotangent inference was isolated and given the quotient/dimension argument above. No statement dispute or source correction was needed. No non-elementary assembly step exceeds 2000 characters.

## Unfinished work

The two new algebra lemmas are deliberately unsplit for other workers; there is no other unfinished requested work. Dry-run and delivery results are recorded by the delivery command, after this report.

## Returned proof retained verbatim

### Original step 1

Order the elements of J with j first. The regular-parameter node [lem-weil-pbc-regular-local-generators-regular-sequence] applies after this permutation: the sequence (t_j,(t_i)_{i\in J\{j}}) is regular, and R/(t_i:i\in J) is regular local. The chart presentation is the specialization of [lem-trf-blowup-chart-regular-sequence-presentation] with a=t_j and a_i=t_i. Its quotient by t_j is (R/(t_i:i\in J))[u_i\mid i\in J\{j}], which is regular by [lem-trf-polynomial-ring-regular-base] and the regular-local-to-regular-ring consequence in [lem-weil-pbc-regular-local-localization]. Multiplication by t_j on the chart is injective by the closed chart-generator lemma [lemma-nagata-chart-generator-regular]. If a prime P does not contain t_j, the chart localization is the corresponding localization of R and is regular by [lem-weil-pbc-regular-local-localization]. If P contains t_j, localize at P and apply [lem-exc-regular-local-lift-regular-sequence-quotient] to the nonzerodivisor t_j and the regular quotient just described. Thus every chart local ring is regular.

Cited nodes: lem-weil-pbc-regular-local-generators-regular-sequence, lem-trf-blowup-chart-regular-sequence-presentation, lem-trf-polynomial-ring-regular-base, lem-weil-pbc-regular-local-localization, lemma-nagata-chart-generator-regular, lem-exc-regular-local-lift-regular-sequence-quotient

### Original step 2

On the chart, the pullback of t_i is t_j for i=j, t_j u_i for i in J\{j}, and t_i for i not in J. The chart extended center ideal is (t_j) by [lemma-nagata-chart-extended-ideal-principal]. Therefore the pullback of t_1\cdots t_r has support exactly the union of t_j=0, u_i=0 for i in (J\{j})\cap\{1,\ldots,r\}, and t_k=0 for k\le r with k not in J. Passing to the reduction removes nilpotents but preserves this support by [def-weil-pbc-scheme-reduction], and the equations define closed immersions by [def-weil-closed-immersion].

Cited nodes: lemma-nagata-chart-extended-ideal-principal, def-weil-pbc-scheme-reduction, def-weil-closed-immersion

### Original step 3

Fix a prime P and a selected subset of the displayed hyperplanes. A listed equation that is a unit at P gives an empty local intersection. For the remaining equations, first consider P with t_j not in P: the chart is a localization of R, and the surviving u_i equations are associates of t_i because t_i=t_j u_i; the selected t_i and t_k classes are independent members of the cotangent basis supplied by the permuted parameter system. If t_j is in P, the chart relations give t_i=t_j u_i: when u_i is in P this term is in the square of the maximal ideal, and when u_i is a unit t_i is an associate of t_j. Hence the classes of the vanishing coordinates t_j, the u_i in P, and the t_k in P with k not in J are linearly independent in the cotangent space; extend them to a minimal generating set of the maximal ideal. The resulting regular system of parameters is a regular sequence by [lem-weil-pbc-regular-local-generators-regular-sequence]. Quotienting successively by the selected equations therefore leaves a regular local ring and lowers dimension by one for each equation; localization is covered by [lem-weil-pbc-regular-local-localization]. Thus each nonempty intersection is regular and has codimension equal to the number of selected hyperplanes, with codimension interpreted by [def-weil-pbc-krull-dimension-ring].

Cited nodes: lem-weil-pbc-regular-local-generators-regular-sequence, lem-weil-pbc-regular-local-localization, def-weil-pbc-krull-dimension-ring

### Original step 4

Use the strict-transform closure definition [def-nagata-strict-transform] with the complement of the center. On the j-chart the extended center ideal is (t_j) by [lemma-nagata-chart-extended-ideal-principal], so the part away from the center is D(t_j). For i=j, the relation t_i=t_j u_i forces every point with t_j=0 on V(t_j) to lie over the center, hence the chart contribution to the strict transform is empty. For i in J\{j}, on D(t_j) the equation t_i=0 is equivalent to u_i=0; its closure is V(u_i), because t_j is a nonzerodivisor on A_j/(u_i) by [lem-trf-chart-coordinate-nonzerodivisors]. For i not in J, the equation remains t_i=0 on D(t_j), and its closure is V(t_i), because t_j is a nonzerodivisor on A_j/(t_i) by the same node. Reduction and the closed-immersion interpretation are supplied by [def-weil-pbc-scheme-reduction] and [def-weil-closed-immersion].

Cited nodes: def-nagata-strict-transform, lemma-nagata-chart-extended-ideal-principal, lem-trf-chart-coordinate-nonzerodivisors, def-weil-pbc-scheme-reduction, def-weil-closed-immersion

### Original step 5

The standard charts are charts of one blowup [def-nagata-global-blowup], so the local descriptions agree on overlaps. Steps 2 and 3 give the reduced coordinate union and all scheme-theoretic intersections; Step 4 gives the exceptional component and each strict transform. If I is empty, H is empty and only the exceptional hyperplane remains. This proves the asserted chartwise statement, including the empty-product case.

Cited nodes: def-nagata-global-blowup, def-weil-pbc-scheme-reduction, def-nagata-strict-transform, def-weil-pbc-krull-dimension-ring

