# Q17: lem-sf-ringed-kflat-single-tensor-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-ringed-kflat-single-tensor-comparison.json`: statement, split into seven steps; not a Mathlib leaf. Statement and all eight statement dependencies retained verbatim.
- No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for each of the 17 step/node citations.
- `searches.jsonl`: actual Q17 search-command log, retained in the sandbox.

## Attachments

None. I searched the project `lean/WeilConjectures/` by the item tag, K-flat terminology, `QObjTensorSingle`, `tensorLeftCounit`, and single/total tensor names. `DerivedCategory.QObjTensorSingleFunctorObjIso` in `CategoryTheory/DerivedCategory/FlatModel.lean:202` provides the abstract categorical object comparison, but its declaration alone does not assert every naturality and specified site-descent normalization clause of this item. The scheme-specific `AlgebraicGeometry.nonempty_kFlat_single_tensor_representative` also has the wrong scope and only an existence conclusion. Neither is reported as an exact attachment. No compiler or axiom check was run.

## WANTED

None. The item source, current blueprint proof, and sources of the generic tools used here are locally available.

## Corrections and findings

The imported item had an empty proof, with a valid statement. There is no statement dispute and no weakening or change of hypotheses. I retained its inherited searches and added only searches run through the prescribed Q17 command. Two different semantic phrasings, LeanSearch, Loogle, and two source grep queries found ordinary flat-module exactness, projective-resolution Tor, sheaf monoidality, and underived total tensor; none gives the entire item's arbitrary-ringed-site comparison. I read Mathlib's `HomologicalComplex.tensorObj` and `tensorHom`, `Algebra/Homology/Monoidal.lean:48,60`: these are underived total tensor constructions.

The main issue is that the specified site's descent theorem computes on pairs of flat-term K-flat complexes, while this item deliberately allows a K-flat complex with nonflat terms and a completely arbitrary test module. I do not infer the stronger comparison from that restricted representative formula alone. The already existing `lem-sfb-derived-monoidal` explicitly states computation by replacing either argument by a K-flat resolution, as well as the two-variable derived universal property and lax localization. After verifying all its categorical hypotheses and reconciling the K-flat conventions, its natural multiplication supplies the required comparison. The specified descent theorem then fixes which derived tensor and normalization are used.

No unit record is changed: the item is a tool extracted from `lem-sf-reduction-flat-model`, not the key statement of `sk-lem-sf-flat-model`. I read the chapter and unit records and the current main-20261015 reduction proof. This supplies the arbitrary-test-module calculation needed in the reduction's final Tor-amplitude sentence without changing the bounded flat-model or coefficient-change route. No SGA source is used.

## Not duplicates

No new nodes were created. Whole-DAG keyword/tag searches and whole-blueprint searches for K-flat, tensor quasi-isomorphism, degree zero, and derived tensor found existing tools, which are reused. `lem-pc-kflat-derived-tensor-comparison` is scheme-specific; `lem-sfb-derived-monoidal` is the general categorical input; neither calls for creating a second version. `lem-pur-kflat-tensor-quasiiso-independent` already supplies the independent-universe quasi-isomorphism lemma, so none is created.

## Review by Q17

I read the item against Stacks `sites-cohomology.tex`, definition-derived-tor and its immediately preceding construction (06YU), the K-flat definition and quasi-isomorphism lemma (06YN, 06YP), and the flat-term resolution theorem (06YS). I also read the current blueprint reduction proof, its chapter/unit records, the statement and proof of the existing general derived-monoidal node, and that node's current blueprint source. All cited node statements were opened, and I checked that their exact asserted conclusions, rather than hidden arguments in their proofs, supply the following inputs.

Step 1 uses `def-weil-size-convention` to work on the allowed small skeleton, the Grothendieck assertion of `prop-pur-kinjective-resolutions-exist`, the symmetric closed additive tensor of `lem-pc-sheaf-modules-tensor-closed`, and the functorial flat resolution of `lem-trf-site-functorial-flat-resolution`. I checked the Grothendieck assertion in Stacks' section-unbounded (07A5), the tensor adjunction in sites-modules lemma-internal-hom-adjoint-tensor (03EO), and the independent-coefficient free-cover construction recorded by the functorial resolution node, in `lean/Sheaf/Algebra/Homology/KFlatResolutionIndependentCoefficients.lean`, including `hasFunctorialFlatResolution_kfi`. The site is essentially small in the coefficient universe and the skeleton makes the small-site hypothesis legitimate. Nothing here requires enough points, a scheme, constant coefficients, or equality of site and coefficient universes. Only the Grothendieck clause of the K-injective node is used; no property of forgotten injectives is inferred.

Step 2 checks a possible mismatch of definitions explicitly: `def-pc-kflat-complex` uses acyclic tensor tests, whereas `def-sfb-preserves-kflat-quasi-iso` uses two-sided preservation of quasi-isomorphisms. The statement of `lem-pur-kflat-tensor-quasiiso-independent` gives preservation for tensoring with P in the second slot, for precisely these independent universes and this total tensor. The signed interchange calculated in the step, using the symmetry asserted by the closed tensor node, gives the first slot. I recomputed both signs against `def-pc-tensor-complex-sheaves`; both routes have coefficients (-1)^(ij) on dy tensor x and (-1)^(ij+j) on y tensor dx. The converse is the direct test 0 to an acyclic X. This prevents treating the two K-flat meanings as interchangeable without proof, and requires no termwise flatness.

Step 3 uses the full statement of `lem-sfb-derived-monoidal`: the derived bifunctor, its localization multiplication, and computation by either K-flat argument. The one-factor computation applied to the identity resolution of P makes that multiplication invertible at (P,Y). Its naturality is the naturality of the lax localization/derived counit, so chain maps, including noninvertible ones, are covered. I checked every hypothesis against step 1 and every tensor/K-flat convention against step 2. I did not use the scheme-specific comparison as if it were a site theorem.

Step 4 uses exactly the natural representative comparison and transformation-extension clauses of `lem-weil-pbc-site-derived-tensor-descent`. Its flat-term restriction is sufficient here: on those pairs both comparisons are invertible, giving beta composed with mu. Extending that transformation and its inverse, then checking the two composites on the restriction, produces the uniquely normalized theta. This proves compatibility with the particular tensor fixed by the item and does not assume all K-flat complexes have flat terms. It does not appeal to any hidden construction in the descent node's proof.

Step 5 cites only the actual signed direct-sum definition. In each degree there is exactly one possibly nonzero summand, indexed (q,0); its inclusion and projection are inverse, its differential is d_P tensor 1, and its morphism is u^q tensor f. This elementary argument proves the single-factor identification and its naturality in place; no redundant node is made. The comparison is composed in the required direction.

Step 6 uses the natural multiplication of the general theorem and the natural theta obtained from the descent theorem. I wrote both naturality equations and composed them; their right edge is explicitly Q(T(u,f)). Thus naturality is proved for arbitrary maps u and f, rather than just isomorphisms, or maps having selected lifts to resolutions.

Step 7 uses the actual flat-term K-flat resolutions asserted by `lem-pc-kflat-resolution`, and the beta comparison and uniqueness supplied by the descent theorem. The displayed normalization equation follows by naturality and m=beta inverse on flat-term pairs. Its left precomposition is invertible because p,b are quasi-isomorphisms and beta is an isomorphism. Cancelling it proves agreement with the resolution construction for every auxiliary choice. The general theorem also computes using the identity resolution of P, so nonflat terms are allowed throughout. I checked the direction of beta and theta in this equation and in the definition of c.

For small cases I checked P=0, M=0, the zero coefficient ring, and P=R[0] with a nonflat M: the construction gives respectively zero or the usual tensor-unit comparison and never assumes M flat. On the one-object Z site, P=[Z --2--> Z] in degrees -1,0 and M=Z/2 gives [Z/2 --0--> Z/2], including the nonzero negative cohomology required by derived tensor. A contractible complex [N --1--> N] with nonflat N is K-flat but not termwise flat; tensoring with any M is again contractible, so it also satisfies the comparison. The signed direct-sum computation is degreewise, so no boundedness or finite diagonal hypothesis is hidden. Every proof step is below 2000 characters. The generic dependencies have no path back to this item. All off-unit statement tools are declared with a reason in split_report.tool_uses; definitions remain statement notions, not alternate routes.

I checked delivery-errors B through E: there are no new node forms to validate, no invented search records, no proof clause moved to a new node, no missing non-elementary inputs, no citation using a mere definition for an unproved theorem, no circular dependency, no extra flatness/boundedness hypothesis, and no coefficient-category substitution. `citations.json` excerpts were checked as literal substrings of the current cited statements.

## Unfinished

None in the stage-1 mathematical split. The required delivery dry run and push are performed after writing this report; tool output is the delivery record.
