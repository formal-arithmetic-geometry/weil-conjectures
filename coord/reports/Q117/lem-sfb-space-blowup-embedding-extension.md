# Q117 stage-1 delivery: lem-sfb-space-blowup-embedding-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-blowup-embedding-extension.json: item split, statement unchanged, seven explicit steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-common-admissible-blowups.json: statement, unsplit; no Mathlib match (088Q, algebraic-space version).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-qc-open-boundary-ideal.json: statement, unsplit; no Mathlib match (0855, algebraic-space version).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-blowup-chart-properties.json: statement, unsplit; no Mathlib match (084B, 085Q/R/S/T/Z, 083S).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-compose-admissible-blowups.json: statement, unsplit; no Mathlib match (086C).
- citations.json: one entry per step/node pair, with verbatim statements as quotes.
- searches.jsonl: searches actually run through msearch.py; the node entries preserve their queries, hits, digest, availability and verdict. write_split.py is a sandbox-only generation aid, not a delivered project file.

## Attachments

None. Searched the project WeilConjectures source for the exact item tag, blowup/embedding concepts, common modifications, boundary preparation and compositions. Existing common-modification, boundary-ideal and admissible-composition declarations work with schemes; none has the general algebraic-space hypotheses required by these nodes. A scheme-only result was not claimed as an attachment for an algebraic-space result. All new nodes are strictly smaller general inputs, and none is the projective-embedding extension conclusion.

## WANTED

None. All mathematical sources used are present in literature/stacks-project. No SGA source was used. No Lean file was written or compiled, and no build or git command was run in the read-only repository.

## Findings and corrections

The item statement is unchanged, including finite type (not finite presentation), potentially nonreduced spaces, no density hypothesis on U, the single ideal blowup on each original space, and the Zariski ideal on Z. Its proof was empty. The inherited blueprint ancestry is null; blueprint_refs.py ancestor confirms this rather than naming an invented blueprint ancestor. The latest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. The item is an inherited supporting compactification/Chow prerequisite, not the key unit statement; no unit or chapter file was changed. Searches of the blueprint for common modifications, admissible blowups, the relevant tags and finite-type ideals found only scheme analogues, which do not cover X an algebraic space.

## Source error

Stacks 088R's third paragraph says that since the two modifications are U-admissible blowups, U is schematically dense in both, citing 085T and 083S. That implication does not follow from admissibility: take X = Spec(k) disjoint union Spec(k), U its first component, and blow up the unit ideal. This is an admissible identity blowup but the second component remains, so O_X -> j_*O_U is not injective. The cited tags give density of the complement of the whole centre, which may strictly contain U. The stronger density needed here is repaired explicitly, without changing the item statement: after the common-blowups lemma, blow up a finite-type ideal cutting out exactly the complement of U in the common ambient space W. Its inverse image of U is schematically dense. Restrict to both open charts and compose the resulting admissible blowups using 086C. The common ambient remains separated over B. This is within the source's common-blowup route, not an alternative compactification theorem. The source's final 'small detail omitted' is written out using the zero pullback ideal in step 6.

## Not duplicates

lem-sfb-space-common-admissible-blowups vs lemma-nagata-common-modification: the existing construction and its interface take schemes X_i over a scheme; the new statement is 088Q for arbitrary algebraic-space X_i and even an algebraic-space base B.
lem-sfb-space-common-admissible-blowups vs def-nagata-common-modification: this existing definition constructs scheme data, not the algebraic-space existence theorem.
lem-sfb-space-qc-open-boundary-ideal vs lemma-nagata-qc-open-complement-ideal-exists: the existing node assumes a scheme; 0855 applies to a qcqs algebraic space.
lem-sfb-space-qc-open-boundary-ideal vs sk-lem-nagata-boundary-divisor: the existing statement is about a scheme and already asserts a boundary-preparing blowup; this node only produces a finite-type ideal on an algebraic space.
lem-sfb-space-blowup-chart-properties vs thm-nagata-global-blowup-proper: the latter concerns the constructed scheme blowup; the new statement includes representability, flat restriction, schematic density of the full boundary complement and the etale/Zariski comparison for algebraic-space blowups.
lem-sfb-space-blowup-chart-properties vs det-nagata-boundary-divisor-cartier: the latter concerns scheme blowups; this statement concerns any algebraic-space blowup, not only a chosen full-boundary ideal.
lem-sfb-space-blowup-chart-properties vs lem-sfb-space-blowup-embedding-extension: shared tags 085Q/R/T/Z supply blowup properties, but the new statement constructs no common ambient space, projective closure or extension of a prescribed immersion.
lem-sfb-space-blowup-chart-properties vs lem-sfb-space-chow-dense-modification: the latter is a Chow modification/projective-embedding existence result; this is general blowup calculus, and cannot alone prove either that node or this item.
lem-sfb-space-compose-admissible-blowups vs thm-nagata-composition-of-blowups: the existing node is scheme-only; 086C is for algebraic spaces and preserves the specified open.
lem-sfb-space-compose-admissible-blowups vs lemma-nagata-composition-center-ideal: the latter is a scheme construction's centre formula, not composition of two algebraic-space blowups.

lem-sfb-space-blowup-chart-properties vs lem-sfb-affine-etale-naive-cotangent-presentation: the existing statement identifies a naive cotangent complex for an affine algebra presentation; it says nothing about relative Proj or blowups.
lem-sfb-space-blowup-chart-properties vs lem-sfb-etale-finite-free-zariski-descent: the existing assertion descends finite locally free modules; it neither constructs blowups nor proves their representability, properness or Cartier boundary.
lem-sfb-space-blowup-chart-properties vs lem-sfb-scheme-big-fppf-quasicoherent-equivalence: the existing assertion compares scheme modules with big-fppf module sheaves; it gives no algebraic-space blowup or flat-blowup comparison.
lem-sfb-space-blowup-chart-properties vs lem-sfb-stack-quasi-coherent-scheme-restriction: the existing result constructs scheme-test restrictions of stack modules; its statement has no blowups or Cartier divisor.
lem-sfb-space-blowup-chart-properties vs def-trf-cartesian-line-presentation: the existing node defines families of line modules and their maps; it gives no theorem about blowup morphisms.
lem-sfb-space-blowup-chart-properties vs def-trf-space-module-scheme-restriction: the existing definition is restriction of a module to Zariski opens, without construction or properties of relative Proj.
lem-sfb-space-blowup-chart-properties vs lem-trf-cartesian-line-presentation-existence: the existing existence assertion produces presentations of line modules, not a blowup or any proper morphism.
lem-sfb-space-blowup-chart-properties vs lem-trf-cartesian-line-presentation-hom-descent: the existing statement uniquely lifts line-module morphisms to cartesian families; it has no geometric blowup conclusion.
lem-sfb-space-blowup-chart-properties vs lem-trf-cartesian-line-presentation-hom-existence: the existing statement lifts a line-module map to a family morphism; it contains none of the blowup properness or boundary assertions.
lem-sfb-space-blowup-chart-properties vs lem-trf-etale-framed-line-effective-gluing: the existing statement glues a line module from frames on an etale cover of a scheme; it gives no blowup or relative Proj.
lem-sfb-space-blowup-chart-properties vs lem-trf-etale-line-frame-transition-units: the existing result constructs transition units and their cocycle; it neither constructs the blowup nor proves any of its morphism properties.

## Review by Q117

I read the item against the entire statement and proof of Stacks 088R (spaces-more-morphisms.tex, lemma-blowup-to-find-embedding), as well as 088Q immediately before it. For the common-blowups node I read all of 088Q, including the graph closure, strict transforms, extension across open subspaces and the separatedness check by the four diagonal charts. This is a genuine smaller input: it handles two arbitrary spaces sharing an open, without a projective immersion or a proper target. Its centres are finite type by the 086B definition, not by a Noetherian assumption.

For the boundary-ideal node I read 0855 (spaces-limits.tex, lemma-quasi-coherent-finite-type-ideals): its hypotheses are exactly qcqs and a quasi-compact open. The new node does not claim that the reduced boundary ideal itself is finite type. For blowup-chart-properties I read the actual statements of 084B, 085Q, 085R, 085S, 085T, 085Z and 083S in spaces-divisors.tex. In particular 084B makes relative Proj representable, 085S assumes flatness (we use it only for open immersions), and 085Z needs the ideal finite type, not the space Noetherian. 083S gives injection on the small etale structure sheaf for the complement of the exceptional Cartier divisor. I also read descent.tex 03DX(2) and 05VG and the existing Zariski/etale equivalence node; this verifies the finite-type ideal comparison and avoids confusing etale ideals with the Zariski ideal required by the item. The source tag for the equivalence was checked against the tags file and corrected to 03DX during drafting.

For compose-admissible-blowups I read 086B and all of 086C: the original space must be qcqs and U quasi-compact; no density is required. Since both morphisms are identity maps over U, the isomorphism over the original space is forced to restrict to the identity there. I checked both extra blowups in step 3 are admissible by restriction of finite generating sets and the unit ideal on U; this is not an assumed finite-presentation property of f.

Step 1 uses projective-space-base-change-proper for the structural map of P, qcqs-source-products for passage along its quasi-separated map, and qcqs-permanence for quasi-compactness of a. I opened both statements: they apply to spaces as well as schemes and require precisely the qcqs hypotheses established. The scheme-theoretic-image definition and factor definition give the closed image and the equation i u = a; immersion-open-in-scheme-image gives the open factor for a quasi-compact scheme immersion. The source U is indeed a scheme because the prescribed immersion into the scheme P is representable. Closed-subspace-proper and proper-composition give Z proper over B. Neither requires Noetherianity or finite presentation. These are the actual clauses in the cited statements.

Step 2 uses the qcqs-permanence statement for U -> B, then 088Q in the new common-blowups node. It verifies all three spaces U,X,Z are separated of finite type over B. The diagonal restriction argument is elementary; properness of a closed diagonal supplies its quasi-compactness by closed-subspace-proper, and qcqs-source-products supplies absolute quasi-separatedness. The common W and both original spaces are therefore qcqs before any boundary ideal or composition theorem is invoked.

Step 3 cites exactly the new boundary-ideal statement for existence of K on W and the new blowup-properties statement for flat restriction, representability over a scheme chart, properness and density. The K used cuts out the ENTIRE complement W minus U, which is the essential correction. Restriction of finite generators and restriction of an injective sheaf map are explicit elementary operations. It does not assume arbitrary admissible blowups create density.

Step 4 uses the composition node with qcqs X and Z and the quasi-compact U checked in step 2. Its conclusion gives one finite-type ideal on each ORIGINAL space, rather than leaving a composite of blowups in the answer. The scheme clause in blowup-chart-properties explicitly returns the finite-type Zariski ideal and the ordinary scheme blowup on Z. This is stronger than merely knowing that D is an algebraic space; it is exactly the clause needed here.

Step 5 uses blowup properness, proper-composition, separated-fp-composition (only its separatedness clause), and proper-cancellation. I opened each cited statement. Proper-cancellation requires the TARGET over B to be separated; that target is T, which was just proved separated from T -> W and W -> B. Thus D -> T is both open and proper. The clopen test and the direct-factor structure-sheaf surjection are written out; no unprovided theorem about proper monomorphisms is being used.

Step 6 cites ideal-closed-subspace-correspondence for the actual pulled-back ideal and its factorization criterion, not merely a definition of schematic image. Its statement says base change is given by the image of the pulled-back ideal and that a source factors through V(I) if and only if its map from I is zero. Since H vanishes on U and O_A -> j_*O_U is injective, H = 0. That is a short elementary kernel argument from the cited facts. The fibre product is then A itself, hence its map to D is an open immersion on all scheme tests. This proves scheme-theoretic factorization, not the invalid assertion that containment of point images alone gives a closed-subspace factorization.

Step 7 uses blowup-chart-properties for representable properness and the isomorphism over the unit-ideal restriction. The composition isomorphisms restrict identically to U; the original common-diagram equation therefore gives b v s = u, not just an unspecified agreement of point images. The original projective immersion is preserved throughout.

The first delivery dry run listed eleven additional nodes sharing the general comparison tag 03DX. I opened all eleven statements and recorded their distinct cotangent, finite-free, module-restriction or line-presentation conclusions under Not duplicates; none states the geometric blowup lemma.

For small cases I checked: U empty (the full-boundary ideal may be zero and its blowup is empty; all final maps and equalities still exist), X empty, U = X (the common ambient may already equal a proper closure, and no density of a boundary component is assumed), nonreduced rings (injectivity is schematic, not topological density), and non-Noetherian qcqs bases (only finite-type ideals, not coherent ideals, are requested). For the blowup-properties statement, K = O gives the identity and K = 0 gives the empty blowup; the non-zero-divisor and density assertions are vacuous on the empty scheme. The flat-base-change clause was not enlarged to arbitrary base change. All seven item steps are shorter than 2000 characters, so no long step hides a separate comparison lemma. New nodes contain statements only, and their proof/proof_deps are empty. I searched the DAG and blueprint by tags and concepts before creating them; the Mathlib searches were run, their returned types read, and the ring-only Rees algebra / affine boundary criterion were not mislabelled as algebraic-space matches.

## Unfinished work

None in the one-level split. The four unsplit supporting statements intentionally remain stage-1 items for later workers. No Mathlib leaf or Lean attachment is claimed.
