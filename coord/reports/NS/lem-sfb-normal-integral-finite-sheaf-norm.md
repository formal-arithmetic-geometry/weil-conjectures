## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-integral-finite-sheaf-norm.json`: statement, split into six proof steps; unchanged statement and statement dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-norm-minpoly.json`: statement, Mathlib leaf. The determinant norm is multiplicative, has the scalar power formula, and is the signed minimal-polynomial constant coefficient to a positive power.
- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-minpoly-fraction-descent.json`: statement, Mathlib leaf. Minimal polynomials of integral elements descend to an integrally closed domain, with monicity and annihilation.
- `citations.json`: one exact statement quotation for each of the 20 step citations. `searches.jsonl` retains the actual search-tool log. No Lean or repository files were written.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item tag and by sheaf-norm names found no declaration stating this item. The existing finite-locally-free norm constructions require local freeness, which is absent here. Mathlib's integral-closure norm declarations do not establish the structure-sheaf theorem for an arbitrary integral source.

## WANTED

None.

## Findings

The seeded statement is correct and was preserved. Its empty-open clause is harmless: both rings of sections on the empty open are singleton rings. Integral schemes themselves are nonempty, so the finite generic field extension has positive degree. No normality of the source, local freeness, separability, Noetherian condition or quasi-separatedness was added.

The imported node had no proof. Its inherited blueprint ancestor is null; the permitted `blueprint_refs.py ancestor` command explicitly returned None. I retained the existing ancestry and place, prepending the item to the new leaves' via lists, and searched the whole imported blueprint by norm/minimal-polynomial concepts and source labels. No equivalent imported node was found. This item is not the unit's key statement, so no unit realization file is changed.

## Source error

The last paragraph of Stacks 0BD3 writes a monic polynomial ending in b_m, then calls its constant coefficient b_0, and omits the sign in the field-norm formula. The signed formula is N(a)=((-1)^m b_0)^e, as in Stacks 0BIH, not b_0^e in general. For example, a=1 in the degree-one extension Q/Q has minimal polynomial T-1: its constant coefficient is -1 and its norm is 1. Our proof names the constant coefficient b_0 consistently and retains the sign. This repairs a calculation in the source proof; the theorem and its vanishing consequence are unchanged.

## Not duplicates

lem-sfb-finite-field-norm-minpoly vs def-fd-additive-character: the shared Tag 0BIF is only a trace reference in the character definition; that node defines additive characters and gives no field-norm formula.

lem-sfb-finite-field-norm-minpoly vs lem-a1-finite-field-trace-frobenius-sum: the shared Tag 0BIH is used there for a finite-field trace sum; that statement asserts no norm identity, and it restricts L to a finite set. Our statement is the norm formula for arbitrary finite-dimensional field extensions, including inseparable ones.

The other keyword/declaration hits were also opened: `lem-a1-finite-locally-free-norm-characteristic-polynomial` asserts a norm polynomial and annihilation for finite locally free affine algebras, not the signed minimal-polynomial power formula; `lem-trf-finite-extension-bounded-powers-polynomial` concerns a normed-vector-space bounded-powers criterion over a complete nonarchimedean field; `lem-weil-pbc-finite-normal-cover-sup-normal` proves normality of a supremum; `lem-weil-pbc-etale-residue-polynomial-lift` clears denominators in a residue-field polynomial. None states either new leaf. There is no existing node with Tag 00H7.

## Review by NS

I read Divisors Tag 0BD3 (statement and whole proof) together with both norm conditions in Section 0BCX. For the two algebra leaves I read Algebra Tag 00H7, Fields Definition 0BIF and Lemmas 0BIG and 0BIH, and checked the actual Mathlib declarations against all hypotheses. In Mathlib I read `Norm/Defs.lean` lines 60–101, `Norm/Basic.lean` lines 65–68, `Norm/Transitivity.lean` lines 229–248, `IntermediateField/Adjoin/Basic.lean` lines 384–387 and 438–467, `Minpoly/IsIntegrallyClosed.lean` lines 36–59, and `Minpoly/Basic.lean` at monic and aeval. The norm formula is a one-line rewrite through the simple-extension norm and its canonical power basis; the basis has generator x and minimal-polynomial degree, with `minpoly_gen` identifying the polynomial. Multiplication and one come from the actual monoid-hom norm, the scalar formula is `Algebra.norm_algebraMap`. For the second leaf, Q=minpoly R s has exactly the claimed coefficientwise image, and `minpoly.monic` and `minpoly.aeval` give its two remaining clauses. The fraction-field scalar towers are the induced inclusions, not arbitrary additional data. Each new leaf has logged LeanFinder, Loogle, LeanSearch and grep searches; the results were read, and the second phrasing on the item found only normalization/integral-norm candidates.

For step 1 I opened the statements of finite/integral morphisms, surjective morphisms, affine spectra, Spec residue-map naturality, affine function-field fractions, and finite-domain fraction degree. They supply exactly the finite affine rings, point-surjectivity, prime contraction, canonical generic fractions and finite extension used. Injectivity of B→A is proved using a prime over (0), not assumed. The generic field maps are compatible because the continuous surjection maps the generic point to the generic point, and fraction extensions are unique.

For step 2 I checked that `lem-sc-integral-scheme-stalks-in-function-field` gives injective stalk embeddings with the same fraction field for arbitrary integral schemes, not just curves. `lem-sc-function-field-sections-glue` states the needed section existence for every rational function locally in the stalk images. Applying the given normal-stalk definition to a monic polynomial over B supplies that local membership. These give affine normality in three direct implications, so no new node is made for it. The section-gluing lemma is declared as a generic tool from another unit in `split_report.tool_uses`; no route of the unit is replaced.

For step 3 I checked that the existing finite-algebra-integrality statement says every element of a module-finite algebra satisfies a monic polynomial, and that the new descent leaf needs only an inclusion of domains with integrally closed target base. These hypotheses were obtained in steps 1–2. The new norm leaf is used with K/L in the proof's notation; its positive exponent and sign place the norm in B. Multiplication, one and the scalar identity descend along the injective map B→L. These are the only non-elementary algebraic inputs; neither new node states a clause of the scheme theorem.

For step 4 the cited injectivity node says generic germs detect equality of sections on every nonempty open. Thus the same field norm makes the affine norms agree on nested affines. Covering each overlap by affines proves their agreement there; an affine intersection is never presumed. Step 5 uses the structure-sheaf axiom contained in the scheme notion to glue, and checks restriction, multiplication, one and the scalar formula by the uniqueness of gluing. Empty opens are handled explicitly.

For step 6 I opened the affine vanishing-prime statement and Spec residue-field naturality: the former gives vanishing iff membership in the point prime, and the latter gives contraction at the image point. The descent leaf supplies an actual annihilating polynomial in A, not just a polynomial in a larger field. Factoring its positive-degree terms by a_U shows b_0 lies in the source prime; since b_0 belongs to B, it lies in the contracted prime. Raising it to the positive exponent in the signed norm formula preserves membership. This proves vanishing at the image point for all sections after affine restriction.

I checked identity maps (degree one, norm equal to the original function), zero and unit elements, inseparable finite extensions (the formulas make no separability assumption), empty opens, and non-flat finite covers of a normal base. For example the scalar formula and vanishing argument still apply in characteristic p to a purely inseparable extension, with its repeated minimal-polynomial roots; no product over distinct embeddings is used. Both new statements concern domains/fields, so zero rings are deliberately excluded by their explicit hypotheses. No step exceeds 2000 characters. The item statement is unchanged, and every uses entry has an exact quotation in citations.json. Nothing remains mathematically unfinished in this one-level split.

## Unfinished work

None for this stage-1 item. The maintainer independently reviews this direct delivery.
