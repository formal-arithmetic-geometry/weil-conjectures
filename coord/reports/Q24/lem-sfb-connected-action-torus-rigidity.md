## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-connected-action-torus-rigidity.json: item split in four steps; statement unchanged.
- lem-sfb-finite-torsion-hom-parameter.json: statement, unsplit; no Mathlib match.
- lem-sfb-torus-torsion-joint-injectivity.json: statement, unsplit; no Mathlib match.
- lem-sfb-field-extension-tensor-injective.json: statement, Mathlib leaf, Algebra.TensorProduct.includeLeft_injective, Mathlib/RingTheory/Flat/Basic.lean:410, with the inferred free/flat instances specified.

Also written: citations.json, containing a verbatim statement quote for each (step,node) citation; searches.jsonl is the search command's own log. No Lean was written or compiled. No repository or launcher file was edited and no repository git command was run.

Attachments: none. I searched the project source by the item tag, torus, multiplicative type, diagonalizable, groupLike and the supporting notions; the only torus word hit was an analytic-torus argument in FrobeniusModule/TraceBound. The HopfAlgebra/Cartier files concern characteristic-zero smoothness, not Cartier duality for diagonalizable finite groups. The occurrences of includeLeft_injective are applications, not declarations stating this leaf.

WANTED: none. Milne's Algebraic Groups PDF is present and was read locally.

## Sources and searches

Read Milne, Algebraic Groups (iAG2017), printed pp.243--244: Theorem 12.33, Lemma 12.35, Theorem 12.36 and Corollary 12.37 with their proofs; also pp.232--233, Lemma 12.4 and Theorem 12.9(a), for the explicit split character labels. The two non-leaf inputs isolate the finite-parameter and joint-injectivity assertions used in Theorem 12.36, not a new formulation of connected-action rigidity. The source proof applies the finite case to every torsion subgroup, then uses coordinate-ring injectivity; the split follows exactly that route.

For the finite parameter input I searched finite diagonalizable Hom schemes and constant Cartier duals in two natural-language phrasings, Loogle HopfAlgebra/GroupLike, AlgebraicGeometry grep and LeanSearch. The hits were Rep.diagonalHomEquiv, finite-group Tannaka and ordinary power maps, not Hom schemes of group schemes. For torsion detection I searched jointly injective quotient maps and intersections of torsion ideals in two phrasings, Loogle and grep, and LeanSearch. Polynomial.toLaurent_injective only embeds polynomials into Laurent polynomials and does not detect a Laurent polynomial by its torsion quotients. One initial Loogle query reported unknown identifier Ideal.Quotient; it was replaced by a valid LaurentPolynomial/injective query, which returned that same unrelated embedding. All queries and actual responses are recorded, with no fabricated searches or service verdicts.

For scalar-extension injectivity, natural language searches and Loogle returned includeLeft_injective. I read Mathlib/RingTheory/Flat/Basic.lean:410--415, Module.Flat.of_free at line 231, and Module.Free.of_divisionRing at Mathlib/LinearAlgebra/Basis/VectorSpace.lean:156. With R=S=k, left algebra B and right algebra K, the declaration is precisely the node; k -> K is injective by the field-extension definition, and the two named instances give flatness of B. A dedicated msearch grep verified line 410. Supplemental searches about vector-space flatness confirmed those instances; no extra node is needed for an inferred instance.

Before creation, searched the entire DAG statements/titles and sources for torus/tori (whole words, avoiding functorial), multiplicative type, diagonalizable, 12.33, 12.35, Cartier dual, joint injectivity, Laurent quotients, includeLeft_injective, and field-extension tensor injectivity. blueprint_refs searches over all chapters included torus, diagonalizable, finite diagonalizable, Cartier, Laurent, Laurent polynomial, schematically dense, group homomorphisms, tensor product map and includeLeft. The relevant blueprint match is the definition def-sc-gm-ga, which is cited. No blueprint node states either new non-leaf or the algebra-valued scalar-extension input. The current latest blueprint's sk-thm-sf-ctf-stability and direct-images proof were read; this is a supporting algebraic-group input deep below inherited proof (3), not a replacement of the chapter or unit route.

## Not duplicates

lem-sfb-finite-torsion-hom-parameter vs lem-sfb-split-torus-hom-matrices: the existing node classifies homomorphisms between split tori over a field, not families over arbitrary parameter schemes from finite mu_n powers. It gives neither the finite constant representing scheme nor the characteristic-dividing case needed here.

lem-sfb-finite-torsion-hom-parameter vs lem-sfb-connected-action-torus-rigidity: the new statement concerns finite torsion sources over arbitrary parameter schemes and has no connectedness or group action hypothesis. It alone does not prove the item; the proof still uses connectedness, the action identity and all torsion levels.

lem-sfb-torus-torsion-joint-injectivity vs lem-trf-lattice-torus-coordinates-action: the existing node constructs Laurent coordinates and torus actions, not joint injectivity of torsion quotient maps over a possibly nonreduced coefficient ring.

lem-sfb-field-extension-tensor-injective vs lem-weil-common-extension-fields-tensor-inclusions: the existing statement requires both tensor factors to be fields, while the coefficient algebra here is k[G x T] and need not be a field.

lem-sfb-field-extension-tensor-injective vs lem-weil-pbc-faithfully-flat-universally-injective: the latter assumes an arbitrary faithfully flat ring map and treats modules; this leaf has a field base and arbitrary algebra B and is an immediate specialization of includeLeft_injective with inferred instances, avoiding a separate proof of faithful flatness.

lem-sfb-field-extension-tensor-injective vs lem-sfb-directed-tensor-integral-embedding: the latter assumes a directed colimit with stagewise integral embeddings; it does not assert field-extension scalar injectivity for an arbitrary algebra.

No existing node has the same precise Milne 12.35 or 12.33 source assertion. The existing item's 12.36/12.37 source is intentionally shared by its supporting inputs, but their statements differ as explained above. No new statement is an elementary consequence of a cited existing result; the elementary connected-to-finite-constant argument and coordinate identifications remain in the item.

## Faults and unfinished work

No statement dispute or mathematical source error was found; no hypothesis was added or dropped. The old node had an empty proof and is now split. The existing blueprint ancestry has from.node null, confirmed by blueprint_refs ancestor. I retain that and its inherited via chain rather than assign a false ancestor; each new node has the item prepended to that chain and an exact additional source place. The unit and chapter files were not changed. The two non-leaf new nodes deliberately have statements only, with empty proof and proof_deps, as required for a one-level split. They remain future items. Nothing else is unfinished.

## Review by Q24

I compared the unchanged item with Milne 12.37: its affine smooth geometrically connected group and torus are within the source's scope; passing to the algebraic closure is justified by the explicit affine scalar-injectivity leaf rather than a claim about geometric points. Smoothness is retained although this proof does not need it. The identity section ensures the parameter scheme is nonempty.

Step 1 uses exactly the scalar-extension embedding stated in lem-sfb-field-extension-tensor-injective, the affine product tensor formula stated in lem-weil-pbc-fibre-product-affine-spectra, and the bijective spectrum/ring-map correspondence stated in def-weil-affine-spectrum. These statements were opened and read. It subtracts the two coordinate images and tests their tensor image. The passage to a split torus uses the item's own definition; geometric connectedness supplies connectedness of G over the algebraic closure. No descent-existence theorem is invoked.

Step 2 uses the full natural family-classification bijection in lem-sfb-finite-torsion-hom-parameter, not just a classification of field-valued maps. I checked it against Milne 12.35 and the explicit split diagonalizable character description of 12.4/12.9: the index is s by r matrices modulo n, so is finite and constant even if n is divisible by the characteristic. def-sc-gm-ga supplies mu_n as a scheme-theoretic subgroup and its power relation; def-weil-connected-scheme states precisely the open-and-closed partition property used. The preimage partition forces factorization through the single open Spec K component as a scheme map, so nilpotents of X cannot create an unexamined deformation. Evaluation at the identity picks the inclusion, and the natural bijection identifies the entire family with that constant inclusion. This is a use of the new node's statement, not its unprovided proof.

Step 3 uses the affine product formula and the group/roots coordinate formulas of def-sc-gm-ga. The statement of lem-weil-pbc-algebra-tensor-pushout-universal-property supplies the algebra multiplication and pure-tensor universal property used in the finite-monomial comparison. I wrote both inverse maps explicitly. Iterating the product formula is legitimate since every factor and X are affine. Imposing t_i^n=1 makes t_i invertible with inverse t_i^(n-1), so the restriction maps are the actual quotient maps in the detection node, rather than merely maps agreeing on points. There is no assertion about arbitrary infinite tensor/product interchange.

Step 4 uses exactly the equivalence for f,g in lem-sfb-torus-torsion-joint-injectivity, then the affine spectrum correspondence already read. I checked the detection statement against Milne 12.33 and the final paragraph of 12.36. For arbitrary B the underlying finite-support argument still works: choose n greater than the spread of all exponents in the finite support; distinct support exponents have distinct residues modulo n, so no coefficients merge in the free group-algebra quotient. This checks that extending coefficients to B does not silently tensor an infinite product and does not require B reduced or a domain. This explanatory check belongs here; the new node itself contains a statement only.

Small cases: n=1 gives the trivial torsion source and the one-point Hom parameter; r=0 or s=0 gives one matrix label and the unique homomorphism; d=0 proves the trivial-torus case without exclusions. For positive characteristic p, mu_p is nonreduced but its characters remain indexed by Z/pZ, so replacing it with its geometric points would be wrong and was not done. For B with nilpotents, coefficient reduction in the group-algebra basis still detects those nilpotents; the zero ring B also satisfies the detection and tensor-injectivity statements. As a necessity check, a disconnected acting group Z/2 can act on G_m by inversion; connectedness cannot be omitted. Ordinary multiplication of G_m on itself fails the homomorphism-in-T hypothesis, as Milne 12.39(b) observes.

I checked B--E with the actual node statements open: all new objects are introduced, notions have definition citations or explicit inline definitions, TeX uses single mathematical backslashes, searches were actually run, every cited node appears in proof_deps and has a verbatim quote in citations.json, there is no citation back to the item, and neither supporting non-leaf restates the item. The four steps are all below 1000 characters, so no long-step hidden-lemma exception is needed. Corrections during self-review: added the Mathlib scalar-extension leaf to avoid an uncited descent assertion; specified scheme-valued Hom classification rather than field-valued Hom; expanded the quotient coordinate comparison to avoid a pointwise density gap. The item's statement was not changed.
