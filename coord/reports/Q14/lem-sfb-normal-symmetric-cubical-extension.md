## Worker report

Q14, stage 1, 2026-10-24. Item: lem-sfb-normal-symmetric-cubical-extension. The imported statement and statement dependencies are unchanged. No Lean was written and no compiler, Lake, build tool or git command was run in the read-only repository. There was no prior item copy, report or search log to recover. No released repair note exists for this item.

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-normal-symmetric-cubical-extension.json, the five new files below, this report, and citations.json (17 entries, each checked against the actual cited statement). All work is in the assigned sandbox.

## New nodes

- lem-sfb-normal-group-vertical-cartier-descent: statement, unsplit, no Mathlib match. Normal-group geometry and vertical Cartier divisors; neither extension of cubical objects nor its full-faithfulness assertion is its statement.
- lem-sfb-rigidified-line-big-open-extension: statement, unsplit, no Mathlib match. Only existence away from a closed base subset of codimension at least two, without symmetry or a cubical structure. It does not assert extension across the remaining subset.
- lem-sfb-symmetric-line-power-prolongation: statement, unsplit, no Mathlib match. Local extension of some tensor power as a plain line; it neither removes that power nor supplies a cube, rigidification or ampleness.
- lem-sfb-cubical-symmetric-multiplication-square: statement, unsplit, no Mathlib match. The quadratic multiplication formula on a supplied cubical object over an arbitrary base; no extension claim.
- lem-sfb-semiabelian-multiplication-fppf: statement, unsplit, no Mathlib match. Flat surjectivity of multiplication, including noninvertible integers and the flat relation schemes used for descent.

Each new file has empty proof and proof_deps, null proof_origin, its own complete hypotheses, inherited chapter/unit and blueprint ancestry, and no claimed finished Lean declaration. New proofs are deliberately not supplied. The possible future proofs of these smaller inputs are discussed below, outside their statements.

## Attachments

None. Searched lean/WeilConjectures for the item id and the words cubical, cubist, Moret-Bailly, and symmetric line. There is no theorem for this item or for the five new inputs. Hits mentioning symmetric algebras are unrelated. A sorry declaration would not qualify as an attachment.

## Sources and WANTED

WANTED: Moret-Bailly, Pinceaux de varietes abeliennes, Asterisque 129 (1985), II 3.2.1--3.2.3 and II 3.3.3, for lem-sfb-normal-symmetric-cubical-extension and the vertical-Cartier, big-open, power-prolongation and multiplication inputs.

WANTED: Moret-Bailly, same volume, I 5.5, for lem-sfb-cubical-symmetric-multiplication-square.

WANTED: Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes, LNM 119 (1970), XI 1.13, for lem-sfb-symmetric-line-power-prolongation.

WANTED: Lan, Arithmetic compactifications of PEL-type Shimura varieties, revision of March 14, 2021, Sections 3.2.2--3.3.2, for a local copy of the online cross-check.

The original Moret-Bailly and Raynaud files named by the imported sources do not exist locally. I did not download or manufacture them. The complete Moret-Bailly PDF could not be opened by the web reader because its size exceeded that reader's limit; its indexed primary-source excerpt gives the opening of II 3.3.3, using a power extension and the I 5.5 multiplication formula. I do not claim to have read the unavailable remainder. Consequently proof_origin.by is agent, not document, and the new formulations are explicitly identified as agent formulations with originals WANTED.

I read Lan's revised thesis online at https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf. The imported reference to printed page 70 refers to a different pagination: in this revision the relevant page is printed 194 (PDF page 222). Proposition 3.3.2.2(1) states full faithfulness for a normal base; Theorem 3.3.2.3(2) states essential-image membership for a symmetric underlying torsor, without ampleness or a proper generic fibre. Proposition 3.2.3.1(2), printed 188, supplies the normal-base relative cube theorem. These conclusions match the item and the existing cube node. Lan quotes the extension results, rather than proving their full argument there, so this is a statement check, not a claim that Lan supplies my reconstructed proof.

I also read the local Stacks sources: algebra.tex lemma-criterion-normal, Tag 031S; lemma-apply-grothendieck, Tag 0337; lemma-apply-grothendieck-module, Tag 0338; and divisors.tex lemma-depth-2-hartog, Tag 0E9I. I verified their labels against tags/tags. They give exactly the depth and coherent-section extension used in step 5. Effective module descent is the existing node lem-pc-fpqc-descent, whose statement includes Tag 023T and rank-one descent, not just descent of sections. No SGA source is used.

## Searches

Before writing the new nodes I searched the whole DAG statements and titles for vertical Cartier divisors, normal-base line descent, codimension-one/big-open rigidified extensions, symmetric power extensions, quadratic multiplication, and semiabelian multiplication. I read the nearby existing nodes listed below. Whole-blueprint searches through tools/blueprint_refs.py covered cubical, cubist, vertical divisor, symmetric line, Cartier divisor, cubical power, rigidified, multiplication semiabelian and line extension. Searches giving Picard-curve rigidification or Cartier-divisor definitions did not state any proposed input. The current latest blueprint's unit and direct-image proof were read, particularly proof (3); its alteration/Picard supporting route is preserved. The ancestor command reports None for this imported ancestry chain; the existing null from.node is therefore retained, and each new via prepends this item.

For the item and every new node I ran msearch.py with LeanFinder, LeanSearch, Loogle and grep, and read the returned types. Every new node also has a second semantic phrasing. All current-session searches are in searches.jsonl; the exact stdout is retained in the sandbox and copied into the new files. All services answered. In particular the relative ring Picard definitions and unitsToPic lemmas do not state a divisor/line-bundle theorem on a smooth nonaffine scheme; ordinary tensor-power identities do not state the cubical multiplication formula; generic flatness, isomorphism-descent or locally-quasi-finite declarations do not prove flat surjective multiplication on a semiabelian family. There is no candidate close enough to be a one-line specialization, and no Mathlib leaf is claimed.

## Not duplicates

lem-sfb-normal-group-vertical-cartier-descent vs lem-sfb-smooth-integral-fibre-vertical-divisors: the existing node assumes a regular base and gives a Weil-divisor pullback identification on a space; the new input is a Cartier-divisor assertion over a merely normal base and includes the identity-section criterion. Normal is not replaced by regular.

lem-sfb-normal-group-vertical-cartier-descent vs lem-sfb-smooth-generic-trivial-line-descent: that node assumes regular separated finite-type schemes over a field and asserts descent of a line class. The new input allows singular normal bases and controls the actual Cartier divisor, needed for a specified isomorphism.

lem-sfb-normal-group-vertical-cartier-descent vs lem-sfb-regular-group-rigidified-line-extension: the existing extension equivalence requires regularity of the entire base; it cannot prove the normal-base divisor assertion.

lem-sfb-rigidified-line-big-open-extension vs lem-sfb-regular-group-rigidified-line-extension: the old node gives extension over a regular base; the new one spreads the trait extensions over a normal base while leaving a codimension-at-least-two closed subset. It asserts no open regular locus and no extension across that subset.

lem-sfb-symmetric-line-power-prolongation vs lem-sfb-symmetric-ample-power-extension: the old node requires an ample line on a proper abelian open and concludes ampleness of its extension. The new tensor-power input allows arbitrary symmetric lines and semiabelian generic fibres, and gives only plain invertible modules. Using the old node here would also create a cycle through this item.

lem-sfb-symmetric-line-power-prolongation vs lem-sfb-normal-cubical-generic-ampleness: the existing node takes a global cubical line as input and concludes ampleness; it cannot supply any power extension.

lem-sfb-cubical-symmetric-multiplication-square vs lem-sfb-semiabelian-cubical-rigidification: uniqueness/existence of a cube on a supplied rigidified line does not state its multiplication pullback formula.

lem-sfb-semiabelian-multiplication-fppf vs lem-sfb-semiabelian-invertible-multiplication: the existing theorem is over an algebraically closed field and requires the integer to be invertible. The new input includes integers divisible by residue characteristic, works over a varying normal base, and asserts fppf rather than etale descent geometry.

lem-sfb-semiabelian-multiplication-fppf vs lem-sc-mult-n-locally-quasi-finite: that node is only about an abelian variety over an algebraically closed field and local quasi-finiteness; it gives neither flatness/surjectivity nor the semiabelian relative statement.

The new nodes sharing the Moret-Bailly volume with the item serve distinct parts of its proof: vertical divisors, a big open, a power, the quadratic formula and the covering geometry. No node states either whole clause of the item, and the item still writes the argument that removes the power and crosses the codimension-two complement.

## Review by Q14

I reread delivery-errors B--E against the actual JSON and the sources just identified. The item is unchanged, including its absence of positivity assumptions. I opened every cited node and checked its statement, rather than relying on its title or proof. The explicit original-source limitations above apply to the agent formulations; they have not been represented as read literature proofs.

Step 1 uses the new normal-group vertical-Cartier statement for normality, density and D = p*e*D. The rational section is the specified isomorphism, not merely an isomorphism class. The two rigidifications trivialize its pullback along e, so the descended divisor is zero. The zero-divisor clause of the same node makes the extension an actual everywhere invertible section. The existing semiabelian-cubical-rigidification statement explicitly says that rigidification-preserving isomorphisms preserve cube structures. All its normal-base and geometric-fibre hypotheses are exactly the item's; regular-base divisor statements are not substituted here.

Step 2 uses the new big-open extension statement only for the plain rigidified line and the dimension of the base complement. The existing cube node supplies its cube, not the big-open lemma. The original symmetry need not preserve r, so I explicitly normalize it by its scalar on the identity section. Step 1 then extends that specified normalized isomorphism over V. No excellence hypothesis or openness of the regular locus is smuggled in.

Step 3 uses only the weaker tensor-power conclusion of power-prolongation. P is not assumed rigidified. The formula Q = P^d tensor p*(e*P)^(-d) provides its rigidification explicitly, and its restriction has exponent d squared. Tensor/pullback calculus comes from lem-weil-pbc-invertible-pullback-tensor. The new quadratic node requires cubical symmetry, which step 2 supplied, and no invertibility of d. The identification of Q with [d]*N_V is obtained by the already-proved full faithfulness, not from the statement of power-prolongation or from an unspecified construction in another proof.

Step 4 uses the full statement of the multiplication input: q is an fpqc cover, and R2/R3 are flat finitely presented locally Noetherian S-schemes. The isomorphism alpha_V is written as the two pullbacks of b with the indicated inverse, so its cocycle follows by cancellation. Quasi-finite is not confused with finite. A torsion kernel is not assumed reduced or smooth.

Step 5 uses Serre's normality criterion and the actual S2 definition to obtain base depth at least two outside V. The existing flat-local depth formula applies because these are Noetherian local rings and the relation schemes are flat over S. The Hom lines have the same depth as the corresponding local ring by a local rank-one frame. The cited Hartogs node assumes precisely this depth bound and finite quasi-coherent stalks; lines on the locally Noetherian schemes meet those assumptions. This short application of existing facts is not a new node. I checked the Stacks tags and read the source formulas.

Step 6 is elementary relative to the established section bijections: extend alpha and its inverse separately, compare their products with the identity, and compare the two triple-overlap composites. Both the isomorphism assertion and the cocycle are therefore proved, not hidden behind the word 'extends'. This step uses only conclusions already established in steps 4--5.

Step 7 uses lem-pc-fpqc-descent, whose statement gives effectiveness for quasi-coherent modules, rank-one descent, and full faithfulness for morphisms. It does not rely on the narrower etale algebraic-space descent node. Pullback along q fixes the identity, giving r_B from c and the supplied rigidification on Q. Thus the unique descended map over V respects r_B. The existing cube node supplies the cube on B and preservation by that map, so descent of a cube section on a possibly nonreduced relation scheme is not silently assumed.

Step 8 uses uniqueness from step 1 for all overlap isomorphisms, including their cocycle, and the same fpqc module-descent statement for the Zariski cover. This handles a base that is only locally Noetherian and need not be affine or quasi-compact. The cube theorem is applied to the glued rigidified line. Empty overlaps require no objects or extra hypotheses.

For each new node I checked self-contained hypotheses, definitions given inline or through statement dependencies, single TeX escaping, no proof hidden in the statement, no Mathlib match and no existing DAG equivalent. The planned proof of vertical-Cartier descent is the smooth connected-fibre height-one/divisor argument with the identity section detecting its coefficient. The planned big-open argument is extension on the height-one DVR local bases followed by finite-presentation spreading and gluing; it does not assert a regular open locus on a nonexcellent base. The power input is deliberately separated as the substantive Raynaud/Moret-Bailly input still to be split. The quadratic formula follows the cube finite-difference recurrence: L((m+1)x) tensor L((m-1)x) equals L(mx)^2 tensor L(x) tensor L(-x), and symmetry gives the exponent m squared. The multiplication input uses the fibrewise semiabelian isogeny property and flatness; its relation-scheme consequences are base change and composition. None is represented as an elementary theorem or a finished proof.

Small cases checked: U = S; S a field (the big open is all S); S a normal trait (again no codimension-two complement); the identity group; a split torus with the trivial rigidified line; an abelian scheme with a symmetric line; d = 1 (the relation is the diagonal and descent changes nothing); d divisible by the residue characteristic, especially multiplication by p on G_m in characteristic p (the kernel is nonreduced but the cover is flat). The latter case is why an etale or reduced-kernel argument was rejected. Negative-degree or nonample symmetric lines are allowed; the proof never applies an ampleness theorem. Normal singular surfaces are allowed and their codimension-two locus is exactly what the flat Hartogs calculation addresses. The five new statements are consistent in these cases.

No proof step exceeds 2000 characters (the maximum is 926). The off-unit citations are ordinary tensor, depth, Hartogs and effective-descent tools; they are declared in split_report.tool_uses for the maintainer's judgment and do not replace the unit's route. Existing statements were not edited. The imported ancestry helper returns None; the blueprint fields retain that ancestry and identify the supporting place. No statement dispute was found. Corrections during self-review were to normalize the symmetry, correct the power line by its identity pullback, use fpqc rather than etale descent, and write both inverse and cocycle extension checks. I also corrected the source pagination and recorded exact Stacks tags for the depth step.

## Validation and unfinished work

Server-only srvcheck check_dag: OK, no finding introduced by the sandbox or on its nodes. Server-only review_split: PASS. The required deliver.py dry run and push follow this report; their final outcomes are recorded below. No required mathematical part of the item's one-level split is left unfinished. The five unsplit inputs are intentionally future DAG items, with the unavailable original literature explicitly requested above.
