## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-semilinear-field-envelope.json: statement item, now split in nine steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- citations.json: ten entries, one per step/node citation, each quoting the complete verbatim statement of the cited node.
- searches.jsonl: five current command-generated search records. Historical searches in the item are retained.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint tag, field-envelope and compatible-pair language, semilinear/Semilinear, and the FieldTheory directory. The matches concern unrelated matrix descent or other compatibility constructions; none states this item with all its clauses. No compiler or Lake command was run.

## WANTED

None. All field sources used are in literature/stacks-project/fields.tex, read directly. The supplied source is explicitly an agent combination of these sources, so proof_origin.by is agent. No SGA source is used.

## Faults and corrections

The imported statement is sound and was retained verbatim. It had no proof. The main risk is confusing H with its image: a nonfaithful H need not be Gal(K/F), and arbitrary choices of individual automorphism lifts need not define a homomorphism H to Aut(M). The proof uses the faithful image only for the fixed-field theorem and then constructs J from all compatible pairs. It does not claim a section of rho.

A second risk is applying a fixed-field theorem for Galois extensions to a normal extension with inseparability. The general case uses the existing normal-extension fixed-field theorem, retaining the purely inseparable conclusion. The Galois fixed-field theorem appears only after proving the extra separability hypothesis in step 9.

No statement correction or route change was necessary. The inherited blueprint.from.node is null; the ancestor command confirms None. The place and via list are preserved. Searches of the whole imported blueprint for normal closure, fixed field, semilinear, and 09I3 give no equivalent item (the fixed-field/semilinear hits are unrelated coefficient or Frobenius nodes). Searches of the whole DAG by the source tags and field keywords found all ten existing dependencies. In particular the existing separable-permanence node avoids inventing another tower lemma. The existing common-normal-compatible-groups node concerns simultaneous fields and a different product group; its statement is not used as a substitute for the present proof.

## Not duplicates

No new nodes: no new/existing pairs to resolve. All needed facts already have DAG nodes, and are cited directly.

## Unfinished

No mathematical part remains. Independent maintainer review follows direct delivery.

## Review by Q25

I read the item against fields.tex Tag 09I3 (lemma-galois-over-fixed-field, lines 2727 onward), 09DT (lemma-normal-closure, 2086 onward), 0EXM (lemma-normal-closure-galois, 2704 onward), 0BME (lemma-lift-maps, 1946 onward), and 030M (lemma-normal-case, 3666 onward). I also read the auxiliary source arguments at 09G9 (finite spanning products), 09H8 (embedding count), 09HN (normality up the tower), 09HB (separable permanence), and 09H2 (separability up the tower). The supplied statement defines normality and fixed fields explicitly; its definition dependencies for fields, field extensions, towers, separable algebraic extensions and purely inseparable extensions were opened and checked. In particular the purely inseparable definition includes equality in characteristic zero.

For step 1 I opened lem-wf-finite-field-action-fixed-degree: it assumes an injective action and concludes finite Galois. The finite subgroup H_0=A(H), acting by its inclusion, satisfies exactly that hypothesis; its fixed field is exactly F by the displayed quantifiers. We do not apply its degree assertion to H itself.

Step 2 cites lem-weil-pbc-finite-extension-in-finite-normal-extension, whose statement supplies an extension of the given finite L/F that is finite and normal over F. The preliminary product-spanning computation proves the needed finiteness directly, rather than silently importing a degree theorem. Step 3 is the direct product, inverse and action calculation, with no external facts. The inverse calculation uses that A is a group homomorphism. It works even when A has a kernel.

Step 4 opens and uses lem-weil-pbc-finite-extension-finitely-many-embeddings with domain and codomain M over F. Its statement assumes only finite-dimensionality of the domain, not separability. Thus forgetting the inverse really bounds Aut_F(M). The Mathlib matches were also read in Fixed.lean (finite-dimensional fixed-field extension and finite automorphisms) and Galois/Basic.lean (of_fixed_field). These are ingredients, not a one-line proof of the entire item.

Step 5 opens lem-weil-pbc-normal-subextension-automorphism-extends. It requires both the ambient extension and the intermediate field to be normal over the bottom field. Both hold here: M/F by step 2 and K/F by step 1. A_h fixes F by the definition of F. The output automorphism is precisely the second coordinate needed in J. Normal/Basic.lean lines 213--235 confirm the lifting/restriction match returned by the searches. Step 6 is a direct mutually inverse pair of homomorphisms, not a citation of an unproved group-extension identification; it also checks equality of the actual actions on M.

Step 7 opens both lem-weil-pbc-normal-extension-normal-over-intermediate and lem-weil-pbc-normal-extension-fixed-field-purely-inseparable. The first says M/K is normal and algebraic; the second says exactly that the Aut_K(M)-fixed subfield is purely inseparable over K, without separability or a finite Galois assumption. Equality with M^N is established by the explicit action comparison in step 6. Finiteness of M/K follows by enlarging scalars on a finite spanning set; finiteness of M^N/K is the elementary subspace dimension bound. These elementary linear-algebra facts need no new node.

Step 8 opens lem-zl-separable-permanence and lem-weil-pbc-finite-galois-receiving-separable-extensions. The former supplies L/F separable from the two separable steps of the tower. The latter supplies a finite Galois M/F and an F-algebra embedding of L when applied to a singleton, so it truly gives the required extension of the specified L after identifying it with its embedded image. This is the normal-closure route already used by the item's source. Step 9 opens lem-sfb-separable-algebraic-intermediate-base and lem-weil-pbc-finite-galois-fixed-field. The former gives M/K separable from M/F separable. After adding step 7's finite and normal conclusions, the latter applies to M/K and says the fixed elements are precisely K. This proves the equality M^N=K for the same witnesses constructed in the separable case.

I checked B--E against the written files. Every cited node's exact statement is quoted in citations.json; no step relies on a cited node's proof or an existence clause absent from its statement. The proof_deps list is exactly the union of the uses lists. No self-reference or dependency on the parent semilinear-domination result was added. The two off-unit, non-Mathlib field-theory tools (purely inseparable fixed field and finite Galois receiving field) are declared in split_report.tool_uses with their uses; all other tools are existing Mathlib leaves or in the same unit. The statement is self-contained, the original metadata and searches remain, and no new unsplit node contains hidden proof text. Each step is shorter than 2000 characters.

Small cases checked: H trivial gives F=K and J=Aut_K(M); nontrivial H acting trivially gives J=H times Aut_K(M), so rho is still onto and its kernel is still the correct automorphism group. L=K permits M=K and J the graph of A. In characteristic p, with H trivial and L/K nontrivial finite purely inseparable, one may have M=L and Aut_K(M)=1, so M^N=M rather than K: the statement correctly claims only pure inseparability generally. In characteristic zero the general fixed field is K, consistently with the purely inseparable definition. Positive characteristic with p dividing |H| presents no division by |H| and is allowed by the faithful-image theorem. The separable case uses no perfectness hypothesis.

All five new Mathlib searches were made by the mandated msearch command and read as returned: two LeanFinder phrasings, LeanSearch, Loogle Normal/AlgEquiv.restrictNormal, and grep for semilinear normality/compatible automorphisms/restriction surjectivity. They return only individual fixed-field, lifting, restriction, normal-closure and Galois ingredients, and none gives all the compatible-pair envelope assertions by one-line specialization. No unavailable search was recorded as absence. No second agent was started, and no source or launcher file was written.
