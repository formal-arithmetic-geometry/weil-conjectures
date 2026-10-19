# Q67 stage-1 delivery: lem-trf-smooth-at-point-differential-criterion

## 1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-at-point-differential-criterion.json`: statement, split; six proof steps, no Mathlib match for the full criterion. Preserved the statement, statement dependencies, source, created record and blueprint ancestry. Added the proof, proof dependencies, proof origin, fresh logged searches, split report and declared off-unit tools.
- `citations.json`: one entry for each use in each step, with the cited statement copied verbatim (including its hypotheses).
- `searches.jsonl`: the six actual msearch calls and their returned digests, retained unmodified.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. All the algebraic and affine geometric tools were already in the DAG. No unit record is changed: this item is a descendant of the unit's key node, not its statement node. The sandbox initially had no item or report to continue.

## 2. Attachments

None. Searches for the item id, its blueprint tag, pointwise smoothness and differential criteria in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration giving the whole item. The project SmoothFiber module gives whole-flat-morphism/whole-smooth-fibre results, which have stronger hypotheses than local flatness at the single point here. They are not attachments. The upstream master sorry declarations are not used as proof evidence.

## 3. WANTED

None: the Stacks sources used are present locally.

## 4. What was wrong or incomplete

The item had a correct statement and sources but no proof. It is exactly the equivalence (1) and (3) in Stacks Tag 01V9, `morphisms-lemma-smooth-at-point`. No statement dispute or correction was needed. The blueprint ancestry is inherited through the nodal-family/Fitting argument from `lem-trf-local-term-locality`, not a claim that the contracting-correspondence statement itself states this algebraic criterion.

The forward rank result, reverse differential-dimension criterion and flat/smooth-fibre lifting are all already separate DAG statements. Creating new scheme-level clauses for them would have duplicated existing tools or merely moved the two implications into children. This delivery instead writes out the affine reduction and the differential tensor calculation. In particular, it does not apply the globally flat / globally smooth-fibre criterion to data that are flat and smooth only at the selected points.

Mathlib was searched using leanfinder in two phrasings, loogle, leansearch and two local greps. All six searches succeeded, and their exact queries are in the item and searches.jsonl. The hits concern the general smooth/standard-smooth classes, the smooth locus, or the whole-fibre lifting theorem. I read the pinned local `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` and `Mathlib/RingTheory/Smooth/Fiber.lean`, especially `Algebra.IsSmoothAt.of_formallySmooth_fiber` at line 194: its source explicitly says it requires the whole fibre smooth. It does not state this item or its fibre cotangent-dimension comparison. The online names sometimes use `IsSmooth` where the pinned source uses `Smooth`; no match is inferred merely from a search description. Inherited searches are preserved alongside the fresh logged calls.

## 5. What remains unfinished

Nothing in this one-level stage-1 split. The already-existing unsplit or split algebra tools retain their independent statuses. No Lean was written, compiled or built. The required server dry run and direct delivery follow this report.

## Not duplicates

No new node was created, so there are no new/existing same-tag pairs to distinguish. Whole-DAG and whole-blueprint searches covered the item, differential criteria, smoothness at a point, and the smooth/flat-fibre route. The existing forward rank statement is `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`; the two reverse algebra statements are `lem-weil-pbc-differentials-dimension-bound-smooth-at-prime` and `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime`.

## Review by Q67

I read the chapter `sec-trace-formula` and unit `sk-i-curve-zero`, their current imported update, the ancestry and immediate Fitting parent, and Stacks `morphisms.tex` Tag 01V9 in full. Its actual proof uses smooth-flatness and the rank of differentials for the forward direction, base change of differentials, the field criterion 00TT and the flat-fibre lemma 00TF for the converse. I read 00TT and 00TF and their proofs in `algebra.tex`, 00RV for differential base change, 02G1 and 01UT for the affine differential sheaf, 01HV(6),(7) for ring and module stalks, 01JQ/01JR for the affine fibre and its open inclusion, and Topology 0055 for dimension at a point. I also read 01V6 and 02H6 to check agreement of the affine smoothness notion with the project's lifting definition, and 01I3 for the principal-localization open immersion. There are no new nodes whose sources would need a separate review.

For step 1 I opened the actual statements of `lem-pc-smooth-flat`, the differential-free-rank lemma, open-fibre-product and open-subspace dimension invariance. The rank lemma really gives a free affine differential module with rank equal to dimension in the fibre, rather than merely a locally free module of unspecified rank. Applied to the smooth neighbourhood U, it has exactly the smoothness hypothesis available. The open-fibre and dimension statements identify that rank with the original d. The relative differential definition explicitly gives its associated module on any affine chart, and the tilde-stalk localization statement identifies the stalk. Localizing the displayed basis produces the required generators without a hidden freeness theorem.

For step 2 I checked the finite-presentation definition really supplies a finitely presented affine chart, so I do not assert that a local stalk is a finitely presented algebra. The affine Spec-square statement identifies the contraction prime with s; affine-open stalk localization and Spec-map stalk localization identify the actual induced ring map with R_p to A_q. Thus the given flatness transfers to the exact map needed by 00TF. The same differential definition and tilde-stalk statement identify the given generator condition with that on M_q. These statements, rather than merely a definition of a stalk, support the identifications.

For step 3 the residue-field statement includes compatibility with the canonical point morphism, which is needed for the fibre product. The open-fibre-product statement permits arbitrary opens and has no separation assumption. The affine-fibre-product statement gives Spec of the actual tensor product, with its projections. The fibre definition says its first projection is a homeomorphism onto the point inverse image; consequently the selected prime is the unique one contracting to q, and is also the kernel of the evaluation into kappa(q) required in the 00TF statement. Open-subspace dimension invariance gives d on this affine fibre. I read the statement and blueprint source of `lem-kun-dimension-finite-type`: it applies to the finite type scheme Spec F, whose finite-type presentation is written explicitly; it is not applied to the potentially non-quasi-compact whole fibre. Homeomorphism invariance follows directly by transporting neighbourhoods and irreducible closed chains.

For step 4 I checked that the base-change node gives the F-linear form Omega(F/k) = F tensor_A Omega(A/R), not merely an unrelated R'-linear map. The calculation then uses L = kappa(Q) directly: it does not assume an unproved identification of two residue fields. Since Q contracts to q, every denominator of A_q becomes a unit in L. The two displayed maps explain the localization/tensor identification and its inverse on pure tensors. A finite generating family stays spanning after tensoring by the explicit coefficient expansion, with no flatness of L over A_q assumed. Thus no unjustified preservation of an exact sequence or appeal to Nakayama is hidden here.

For step 5 I read both cited algebra-node statements. The 00TT node takes precisely a finite type algebra over an arbitrary field, a prime and the cotangent-dimension inequality established in step 4; it does not require a closed point or a perfect field. The 00TF node takes finite presentation near q, local flatness at q and fibre smoothness at Q. All three are checked explicitly, the first with g=1. The prime is the kernel prime from step 3. Its conclusion and the definition of smoothness at a prime give a genuine smooth principal localization away from q.

For step 6 I checked that the principal-localization node asserts an open immersion of schemes, not just a homeomorphism of spectra. The affine smoothness equivalence gives smoothness over V. Instead of leaving composition with V into S as an uncited stability theorem, I wrote out the elementary lifting argument: a first order thickening has the same points, so its given map to S also factors through V, and the lift over V is already a lift over S. Affine finite-presentation neighbourhoods over V are the same neighbourhoods over S. The cited definitions of an open immersion, a first order thickening, formal smoothness and smoothness supply exactly these meanings.

The four off-unit tools declared in split_report are generic algebraic interfaces: the free differential-rank statement, field cotangent-dimension criterion, flat-fibre lifting and affine smoothness equivalence. They serve the Fitting-locus descendant on the existing ancestry; none replaces the unit's contracting-correspondence or specialization route. Other reused definitions, Mathlib leaves and closed dimension/stalk tools require no route replacement.

I tested the hypotheses against small cases. At a generic point of the affine line, d=1 even though the local ring has dimension zero: the proof consistently uses dimension of the fibre at the point, not dimension of its local ring. The finite purely inseparable extension F_p(u)[v]/(v^p-u) has d=0 and a nonzero differential module, so it fails the generator bound as required. At the node of Spec k[x,y]/(xy), the differential fibre needs two generators although d=1, again excluding the singular point. The nonflat quotient Spec F_p to Spec Z has d=0 and zero relative differentials but fails the separate flatness hypothesis, so the proof cannot incorrectly call it smooth. An empty fibre cannot contain the stipulated x. No reducedness, Noetherian base, perfection, global flatness or equidimensional-fibre assumption is introduced.

Finally I checked delivery-errors B through E against these files: there are no new nodes to be elementary duplicates or restated clauses, every cited statement was opened and supports what is taken from it, proof_deps is the union of uses, no argument relies on a cited proof instead of its statement, and every step is below 2000 characters. The statement retains precisely the hypotheses of 01V9. All writes are confined to this sandbox.
