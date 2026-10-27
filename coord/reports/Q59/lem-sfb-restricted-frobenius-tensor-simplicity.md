# Q59 stage-1 delivery: lem-sfb-restricted-frobenius-tensor-simplicity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-restricted-frobenius-tensor-simplicity.json: item; split in four complete steps; statement and statement dependencies unchanged. Original source, blueprint provenance and Q54 searches retained; actual Q59 searches appended.
- dag/nodes/sec-six-functors-basics/lem-sfb-restricted-module-infinitesimal-simplicity.json: new statement-only prerequisite; unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-p-isogeny-relative-frobenius.json: new statement-only prerequisite; unsplit, no Mathlib match.
- citations.json: six entries, one for each step/node citation, with verbatim clauses from the statements.
- searches.jsonl: unmodified output log of msearch.py. Some early differential searches remain logged as research; the JSON records precisely the searches relevant to the final statements.
- report.md and write_split.py: this report and the sandbox-only JSON preparation script.

There are two new nodes and zero new Mathlib leaves. The proof reuses the existing scalar-Schur and finite double-centralizer Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, Steinberg, highestWeight, restricted and Frobenius notions. The relevant Frobenius files concern scheme or field Frobenius, semilinear maps, or Weil representations; none states this algebraic-group tensor theorem. The item has no Lean audit declaration to attach.

## Wanted sources

WANTED: J. C. Jantzen, Representations of Algebraic Groups (2003), Part II, 3.14--3.17, for the restricted infinitesimal-simplicity prerequisite and the tensor-product theorem. The item already named this absent book; it has not been downloaded or claimed read.

WANTED: J. C. Jantzen, Moment graphs and representations, Sem. Congres 24 (2010), sections 5.1--5.2, pp.302--303, local copy for lem-sfb-restricted-module-infinitesimal-simplicity. Read the author's posted PDF online at https://math.au.dk/~jantzen/grnbl.pdf. Section 5.2 identifies the restricted weights using fundamental weights and states Curtis's infinitesimal-simplicity theorem. Its simplifying assumption is almost simplicity; the local Milne 22.54 is stated for semisimple simply connected groups. No large-characteristic restriction is used: Jantzen introduces p greater than the Coxeter number only later, in 5.9.

## Audit of the item and route

The sandbox initially had no item copy or report. Copied the live unsplit item and found no repair note. Read coord/brief-stage1.md, roles/worker.md, stages/1-dag.md, SETUP.md's chapter/unit/node distinction, GOAL.md, and delivery-errors.md B--E. Read the chapter and unit records and the current latest blueprint unit and direct-image proof, paragraph (3). The current unit uses proper and open direct images through compactification; this inherited chain is below its alteration/GIT/Steinberg prerequisite and changes no unit or chapter step.

The inherited blueprint ancestor command returns null. Preserved that null, kept its detailed from.place and via chain, and prefixed the item to via for both new nodes. Whole-DAG statement searches and tools/blueprint_refs.py searches for Steinberg, Frobenius kernel, restricted highest, infinitesimally, Lie simple, relative Frobenius reductive and Frobenius isogeny found no equivalent blueprint statement. Reused the existing scalar and density results instead of recreating them. In particular, lem-ag-lie-stable-subspace is about characteristic zero over Qbar_l and is not used in this positive-characteristic proof.

The item's statement is sound, and was retained. Its extra requirements f(U) subset U and a highest weight for W do no harm; the argument in fact only needs W simple, the torus condition on f, and the restricted highest weight of V. This is a proof of the given statement, with no hypotheses added to it.

## Source error

Milne, Algebraic Groups, 22.54, printed p.481, writes the restricted highest weight as a sum of coefficients less than p times the simple roots. This must say fundamental weights, or equivalently require each simple-coroot pairing to lie in [0,p). For example take S=SL_2 over an algebraic closure of F_3. The standard two-dimensional module has highest weight omega, while the simple root is 2 omega. The standard module is infinitesimally simple: the upper and lower infinitesimal root matrices generate the matrix units, so have no common proper nonzero invariant subspace. But omega is not an integral multiple of the simple root. This disproves the displayed root-coefficient version of the iff. The new prerequisite uses the correct pairing formulation, as also corroborated in Jantzen 5.2. This is a correction of a source typo, not a change to the already correct item statement.

Milne 22.52 and 22.56 nearby are not used. No SGA source is used or substituted into the route.

## Not duplicates

lem-sfb-restricted-module-infinitesimal-simplicity vs lem-sfb-restricted-frobenius-tensor-simplicity: the new statement concerns one module restricted to its tangent Lie algebra and has no tensor factor or homomorphism f; it does not state the item's tensor conclusion.

lem-sfb-restricted-module-infinitesimal-simplicity vs lem-sfb-restricted-highest-weight-dimension-product: the existing node is an integer dimension identity for three highest weights; it does not give Lie-invariant subspaces.

lem-sfb-scalar-p-isogeny-relative-frobenius vs lem-sfb-root-datum-isogeny-realization: the existing statement constructs some isogeny with prescribed root-data map and gives centrality/isomorphism criteria; it does not give uniqueness for a specified f or identify its relative-Frobenius factorization. The new statement is precisely that missing comparison and applies without representations.

lem-sfb-scalar-p-isogeny-relative-frobenius vs lem-sfb-isogeny-root-power-laws: root-coordinate power laws do not state a global isomorphism G^(p) -> G factoring a specified endomorphism; the new node packages the global isogeny-theorem comparison rather than duplicating a root-coordinate clause.

lem-sfb-scalar-p-isogeny-relative-frobenius vs lem-sfb-restricted-frobenius-tensor-simplicity: the common source place 23.25 concerns the group-scheme comparison; the item is tensor simplicity. Neither statement implies the other without additional results.

lem-sfb-scalar-p-isogeny-relative-frobenius vs lem-sfb-affine-group-frobenius-smooth-image: the latter concerns eventual smooth images of arbitrary finite-type group schemes, not a reductive isogeny's comparison with the first relative Frobenius.

## Review by Q59

I read local Milne 22(e), pp.481--482 for the item's intended Steinberg conclusion, 14.1, pp.279--280 for its linear algebra, 2.25--2.29 for the coordinate form of relative Frobenius, and 23.25--23.26, pp.492--493 for the comparison of isogenies with the same character map. The assembly is marked agent-written: I did not pretend to read the absent Jantzen book. The proof uses infinitesimal simplicity and ordinary linear algebra, not Steinberg's full tensor theorem as a new node with another name.

For the first new node I checked that the source's infinitesimal condition means simplicity for the differential, not just simplicity as a rational module. Its statement defines that differential using augmentation derivations. The simply connected hypothesis is essential, and is retained; no good-prime condition is added. I corrected the fundamental-weight typo described above. The online author source is [Jantzen sections 5.1--5.2](https://math.au.dk/~jantzen/grnbl.pdf).

For the second new node I checked Milne's full isogeny theorem, including the uniqueness assertion missing from the existing root-datum-realization node. The twist G^(p) has the same split root datum under the canonical torus-character identification. Relative Frobenius induces scalar p on characters. The root-data isomorphism therefore lifts to an isomorphism from G^(p) to G; compare its composite with relative Frobenius to the given f. Milne's uniqueness gives a target inner torus automorphism, which can be absorbed in that isomorphism. This explains why the new prerequisite is true without a chosen finite-field model and without Borel compatibility. This argument is a plan for the unsplit node, not a proof hidden inside its statement.

Step 1 cites precisely the new comparison, the existing semisimple-implies-reductive clause, and sbc-lem-smooth-geometrically-reduced. I opened all three statements and copied their exact clauses into citations.json. The group is smooth by hypothesis and its fibre over Spec F is S itself, so the reducedness result applies. I also read Stacks Tag 056T, varieties.tex lemma-smooth-geometrically-normal, which says a scheme smooth over a field is geometrically reduced. The coordinate injection is then the written pth-root calculation; it does not assume f is an isomorphism or reduced-kernel morphism. The differential vanishing is computed on dual numbers and is valid also for p=2. The only off-unit tool is the smooth-fibre reducedness node, declared in split_report.tool_uses.

Step 2 cites exactly the restricted infinitesimal-simplicity statement and the two existing Schur/density leaves. I opened their statements, checked faithfulness for the algebra A acting by inclusion, and checked that a simple A-submodule is an F-subspace because the scalar maps lie in A. The scalar endomorphism statement really identifies the entire ring End_A(V) with F. Thus an F-basis is a finite generating set over that endomorphism ring, precisely the finite hypothesis of the double-centralizer statement. This gives A=End_F(V). I read the Mathlib declarations at AlgebraRepresentation/Basic.lean:22--32 and SimpleModule/Basic.lean:559--592; their statements agree with the already existing leaves. I did not create new copies or count them as new leaves.

Step 3 is elementary after steps 1--2. The dual-number expansion shows explicitly why an S-submodule is stable under each differential operator and why W contributes zero. Stability under sums and products gives the full matrix algebra. The two matrix-unit inclusions prove N=V tensor Z, including d=1; there is no appeal to an uncited isotypic-submodule theorem.

Step 4 is elementary after the previous steps. I checked the argument over every test algebra R, not just F-points, since infinitesimal group schemes cannot be detected by F-points alone. Applying rho_V(s) inverse is valid because it acts only on the entire V factor of V tensor Z. The universal point over F[S] then gives the actual coaction inclusion. Applying the quotient W -> W/Z and the injective coefficient map f# proves Z is W-stable by an explicit basis calculation. This does not use semisimplicity of all representations or a false converse from Lie stability to group stability. The final nonzero tensor assertion follows from basis vectors.

I tested the new statements and every step on S=1 (all simple modules are one-dimensional), lambda=0, W trivial, SL_2 in p=2 and p=3, a product of two simply connected factors, and the torus/trivial cases of the new Frobenius comparison. A scalar-p isogeny of a torus has exactly the asserted Frobenius form. Composing a standard Frobenius with a torus inner automorphism is covered by h; no equality with a predetermined standard Frobenius is assumed. The characteristic-zero Lie comparison and exceptional root-length isogenies cannot be substituted for the scalar-p lattice condition. No long proof step exceeds 2000 characters; no extra subclaim is concealed in one. The two new prerequisites are neither elementary two-line statements nor clauses restating the item's tensor conclusion. Their proofs and proof dependencies are empty, as required for unsplit nodes. All six citations are verified as literal substrings of their node statements.

All new-node Mathlib searches were actually made through msearch.py, using LeanFinder, LeanSearch, Loogle and grep, with a second natural-language formulation. The hits were read. LieModule.IsIrreducible is only a definition; the simple-adjoint statement assumes a simple Lie algebra, and the Geck example is in characteristic zero. Perfect-field Frobenius equivalences and Witt-vector identities do not compare reductive group isogenies. Thus neither prerequisite has a Mathlib match. No service failure was re-labelled no match.

## What remains unfinished

The two prerequisites deliberately remain statement-only stage-1 queue nodes. No part of the item's four-step assembly is deferred to an unnamed assertion. No Lean has been written, compiled or built, and no repository or launcher file has been edited. Server dry-run validation and delivery follow this report.
