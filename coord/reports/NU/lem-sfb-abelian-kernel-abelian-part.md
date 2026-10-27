# Stage-1 report: lem-sfb-abelian-kernel-abelian-part

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-kernel-abelian-part.json`: statement, split into six steps; arbitrary-field statement retained verbatim; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-subvariety-separable-definition.json`: new statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-galois-closed-subscheme-descent.json`: new statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `citations.json`: 19 entries, one for each node cited by each proof step; every quote is copied verbatim from the corresponding statement.

Two new nodes, zero Mathlib leaves. No unit record changed: this auxiliary is not the unit's key statement.

## Attachments

None. The live project source under `lean/WeilConjectures/` was searched for the blueprint tag, kernels, abelian varieties, subvarieties and descent. No project declaration proves the complete item, or either new lemma, without sorry. Existing project declarations with sorry are not attachments. No Lean was written, compiled or built.

## Literature wanted

WANTED: J. S. Milne, *Abelian Varieties*, January 2, 2022, https://www.jmilne.org/math/xnotes/AVs.pdf, Section 12, printed p.19, second unnumbered lemma after Proposition 12.1 (finite separable definition of a geometric abelian subvariety), for `lem-sfb-abelian-subvariety-separable-definition` and step 3 of this item. This article was read through the web interface, not downloaded into the repository. It is distinct from the locally available longer course notes `literature/milne-abelian-varieties_AV.pdf`. Its finite separable extension can be replaced by a finite normal closure inside the fixed algebraic closure. The item's assembled proof is marked agent-written because its local source flags the missing imperfect-field argument.

## Findings and repairs

The imported item is true as stated; no statement change or STATEMENT-DISPUTED is needed. Its original local source, Chapter I pp.42–43, footnotes 10–11, explicitly leaves the imperfect-field justification open. Merely taking the reduction and identity component over k would not supply that justification. The split instead takes them over an algebraic closure, isolates finite separable definition as a real supporting lemma, proves invariance, and descends along a finite Galois extension. It never identifies D with the reduction of K over k. No simple-factor or isogeny-decomposition result is used: that would run backwards through the item's own parent.

The closed-subset descent node cannot descend the nilpotent scheme structure. The new descent input therefore concerns ideals and closed subschemes, including subgroup structures. The finite-extension restriction of the existing property-descent node is respected: it is applied to E/k, not the infinite algebraic closure. The dimension-convention comparison is cited before using the local-ring version of zero-dimensional finiteness. The inherited source, blueprint fields and searches were retained; the current blueprint was read from `literature/blueprint/latest/`, main-20261023-1620, and the new nodes' via lists prepend the item. The ancestor utility returns null for this inherited auxiliary chain; that result is retained rather than inventing a blueprint ancestor.

## Unfinished work

No part of the item's stage-1 split is left unfinished. The two new supporting lemmas intentionally have statements and searches only, as required for one-level splitting. They remain unsplit for subsequent stage-1 work. No further attachment or Mathlib leaf was claimed.

## Not duplicates

lem-sfb-abelian-subvariety-separable-definition vs lem-sfb-abelian-kernel-abelian-part: the new lemma is a finite separable field-of-definition result for an arbitrary geometric abelian subvariety; it does not mention kernels or equidimensional abelian parts and does not restate a clause of the item.

lem-sfb-abelian-subvariety-separable-definition vs lem-sfb-abelian-closed-subgroup-reduced-component: the existing node constructs the reduced identity component over an algebraically closed field; it asserts no field of definition over an imperfect ground field.

lem-sfb-abelian-subvariety-separable-definition vs lem-sfb-abelian-field-extension: the existing node preserves an abelian variety under extension of scalars; it does not descend a geometric subvariety.

lem-sfb-galois-closed-subscheme-descent vs lem-weil-pbc-galois-invariant-closed-subset-descends: the existing statement gives only a closed topological subset; the new statement descends the full ideal sheaf and closed subgroup structure.

lem-sfb-galois-closed-subscheme-descent vs lem-pc-descent-finite-flat-closed-subschemes: the existing node assumes the subschemes are finite locally free of a fixed degree over the base; the positive-dimensional abelian subvariety used here does not satisfy that assumption.

lem-sfb-galois-closed-subscheme-descent vs sk-thm-picard-descent: clause D2 has the same finite-flat-degree restriction; D1 concerns modules, not effective descent of arbitrary closed subschemes as stated.

lem-sfb-galois-closed-subscheme-descent vs thm-pd-fpqc-local-properties: the latter descends properties of a scheme already given over k, and does not construct that scheme.

lem-sfb-galois-closed-subscheme-descent vs lem-weil-pbc-tensor-field-extension-galois-invariants: the latter identifies invariant elements of a scalar-extended vector space; it does not descend stable subspaces or ideal sheaves.

The whole DAG and blueprint were searched by abelian subvariety, subvariet, finite separable/abelian, Galois/subgroup and closed/descent concepts. No equivalent blueprint statement was found. The new lemmas use Milne places rather than a shared Stacks tag; no same-tag pair is introduced. The newer Milne article's separable-definition lemma is not its regular-extension descent theorem: a purely inseparable part of an algebraic closure cannot be discarded by invoking regular-extension descent.

## Review by NU

I read the item's local source in Milne's abelian-variety course notes, I Proposition 10.1 and the discussion following Remark 10.2, including both imperfect-field footnotes. For the new separable-definition lemma I read Milne's 2022 article, Section 12, p.19: its torsion-density argument supplies a finite separable field of definition, independently of simple-factor decomposition. Passing to the finite normal closure gives exactly the finite Galois formulation recorded in the new statement. For the new closed-subscheme descent lemma I read Milne's Algebraic Groups Appendix A.64–A.66, pp.580–581. A.65 applies to closed subschemes of finite-type schemes, not just reduced subvarieties; its affine proof descends invariant ideals. The group assertion descends multiplication, inverse and identity: their required factorizations through the descended closed subscheme hold after faithfully flat field extension, hence the offending ideal images are zero already before extension. This preserves the full subgroup scheme structure.

In step 1 I opened `lem-sc-kernel-subgroup`, `def-sc-abelian-variety`, `lem-weil-pbc-closed-immersion-proper` and `def-weil-proper-morphism`. Their statements give respectively the closed kernel, properness of A, properness of its closed subscheme K, and finite type. The unit gives nonemptiness directly. Step 2 uses the actual arbitrary-field-extension statement of `lem-sfb-abelian-field-extension`, the closed-immersion base-change statement, the fibre-product definition, and the algebraically-closed hypothesis of `lem-sfb-abelian-closed-subgroup-reduced-component`. That last hypothesis is satisfied only after passing to Omega. Its statement supplies both the closed abelian subgroup C and the dimension equality used later; nothing about descent is attributed to it.

In step 3 the new separable-definition node is applied to precisely the closed abelian subvariety obtained in step 2. All its hypotheses are present: A is over k, Omega is a fixed algebraic closure, and C is a closed subgroup and abelian over Omega. In step 4 I opened `lem-weil-pbc-normal-subextension-automorphism-extends` and checked that E/k and Omega/k are algebraic normal extensions. The lifted automorphism preserves K, its reduction, and the component of the identity. Equality of the two closed subschemes before extension is proved explicitly on ideals, using injectivity into scalar extension; it is not inferred from equality of points or supports. The new descent statement is cited there only for its precise invariance criterion, and is applied in step 5.

For step 5 I read `thm-pd-fpqc-local-properties`: it assumes a finite extension, and E/k is finite. C_E is an abelian variety, so the proper, smooth, connected and finite-type hypotheses really hold. `def-sc-abelian-variety` then gives the desired conclusion for D. The factorization through K is written out by vanishing of ideal images after extension to Omega and injectivity before extension; the quotient of affine coordinate rings proves the resulting immersion is closed. Compatibility of group maps follows after composing with the closed subgroup inclusion into A. These are short ideal and universal-property arguments, not additional hidden descent lemmas.

In step 6 I read `lem-kun-dimension-extension` and checked finite type separately for D and K, established in steps 5 and 1. It allows arbitrary field extensions, so Omega/k is allowed here. The dimension equality in step 2 links them. I read `lem-pc-scheme-dimension-local-rings` to compare the topological chain convention with the local-ring convention of `lem-pc-dim-zero-finite-over-field`; I then checked the latter's properness and dimension hypotheses on K. Its statement imposes no reducedness assumption. The underlying Stacks sources read for these uses were Tags 02FY, 04MU and 06LH; the closed-immersion and smooth-descent sources were also checked at Tags 01QR and 02VL. Each cited statement is present verbatim in `citations.json`; all 19 step/node pairs were checked against their files, and proof_deps is exactly their union.

I tested the item on f=0 (D=A), the identity (D=0), product projection (the positive-dimensional kernel factor), and inseparable finite isogenies such as multiplication by p in characteristic p (K can be nonreduced and D=0). The new separable-definition statement allows E=k when k is algebraically closed, and applies to both 0 and all of A. It does not assume k perfect. The new Galois descent statement allows E=k and empty closed subschemes in its general clause; in characteristic p it preserves ideals of nonreduced subgroups, so it is stronger than descent of supports in exactly the necessary way. A finite field extension is used for effective invariance and property descent, and no claim about invariants over a purely inseparable closure is made.

I checked delivery-errors B–E against these files: the two new nodes are independent supporting results, not clauses of the target, elementary observations remain explicit steps, no existing general node covers either new statement, no false Mathlib match or unrun search is recorded, no upstream sorry is treated as a proof, every black-box non-elementary input is a cited node, and off-unit generic tools are declared. All steps are shorter than 2000 characters (maximum 858), and the existing dependency direction is respected. The server-side check_dag run before writing this report returned OK with no finding introduced by the sandbox or on its nodes. The required full delivery dry run follows this report.
