# Stage-1 delivery: lem-trf-iterated-transform-exceptional-support

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-iterated-transform-exceptional-support.json`: item, statement, split; Mathlib verdict no match. Four proof steps reuse existing nodes.
- `citations.json`: seven step/node entries, each quoting the existing statement verbatim.
- `searches.jsonl`: unmodified output log of the required msearch commands.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id and for strict-transform/module/sheaf terminology. The project contains scheme strict-transform constructions and module power-torsion results, but no declaration stating the two successive module-transform support assertion with all its hypotheses and conclusions. The scheme transform is not a module-transform attachment. No Lean was written or compiled.

## WANTED

None. All sources used are already present under literature/.

## Corrections and scope

The item's statement is correct and unchanged. Its original proof was empty. I supplied the Cartier-factor argument and the support-set equality; the latter does not require an unproved assertion that images commute with inverse images. The singleton fibres of the first blowup away from its centre supply the reverse inclusion. No hypothesis of quasi-compactness, quasi-separatedness, flatness or finite presentation was added. No other node or unit record was edited.

The source tag mapping was checked in `literature/stacks-project/tags/tags`: 080I is divisors-lemma-strict-transform-composition-blowups, 080H is divisors-lemma-strict-transform-different-centers, 02OS is divisors-lemma-blowing-up-gives-effective-Cartier-divisor, and 07ZP is properties-lemma-sections-supported-on-closed-subset. The proof follows these Stacks results, not a prohibited route. The nearest blueprint ancestor and inherited via chain were checked with blueprint_refs.py. The main-20261015 ancestor supplies the existing provenance chain rather than a second statement of this auxiliary blowup lemma. Whole-blueprint searches for strict transform, exceptional and 080I found no blueprint node stating this item in another form; same_as remains empty.

## Not duplicates

No new nodes. Reused `lem-trf-strict-transform-different-centers` (080H) and `lem-trf-strict-transform-sheaf-kernel` (080D plus supported-section saturation), rather than creating duplicate support-removal or Cartier-factor lemmas. The general invertible-factor blowup isomorphism and exceptional-divisor principalization are also existing nodes. The support-set equality is a short elementary step, not a new node.

## Review by Q133

I read the item against divisors.tex, Tag 080I, especially the last paragraph of its proof. That paragraph uses 080H with the first exceptional divisor, so I also read the statement and proof of 080H and the definition 080D, as well as 02OS and properties.tex 07ZP. I read the chapter, unit, current blueprint ancestor, worker contract, three levels and delivery-errors B through E. There are no new node sources to audit.

Step 1 uses the actual statement of thm-nagata-blowup-principalizes-center: the finite-type quasi-coherent ideal becomes invertible and is generated locally by a nonzerodivisor. Thus E is an effective Cartier divisor on S1. It also uses the statement of lem-trf-strict-transform-sheaf-kernel, which explicitly provides both quasi-coherence of F1 and absence of local sections supported on the inverse image of the first centre. This verifies exactly the hypothesis on F1 for 080H; I do not assume that ordinary pullback preserves support-freeness, which is false in general.

Step 2 uses lemma-nagata-blowup-invertible-factor for the isomorphism of the two second blowups and lem-trf-strict-transform-different-centers for equality of the two quotient kernels. I checked all its arguments: base S1, centre ideal J finite type, Cartier divisor E with ideal L, morphism f1, coefficient F1 quasi-coherent, and no sections supported over E from step 1. The comparison node states equality of kernels of quotients of the same pullback under the specified isomorphism; the step takes exactly that statement. The product ideal is finite type by the explicit displayed local generators, and its zero set is the union by the elementary prime-ideal test. Equal kernels give the stated canonical quotient isomorphism.

Step 3 applies the support-freeness clause of lem-trf-strict-transform-sheaf-kernel to the product centre. The module F1 and the product ideal meet its quasi-coherence and finite-type assumptions, verified in steps 1 and 2. It does not assume global surjectivity on sections. The induced isomorphism of fibre products is over S1, so its inverse image of the product centre is precisely f2 inverse c inverse of the union. The fibre-product node defines the universal property; associativity follows immediately by mapping either iterated product to the same pairs with equal images in S. Restriction-compatible module isomorphisms then transfer vanishing for every open W.

Step 4 uses only the complement-isomorphism statement of thm-nagata-global-blowup-complement and an explicit pointwise calculation. A point s outside Z has a unique inverse image under b. If it is the image of a point of Z1, then c(t) must equal that point; over Z, membership in E is immediate. This proves both inclusions without needing properness, a scheme-theoretic union assertion, or a factorization through a closed subscheme. Its elementary marking refers to this short set argument from the cited isomorphism, not a new geometric theorem.

I checked the small cases. F=0 and empty X give immediate vanishing. If I is the unit ideal, b is the identity, E is empty and the result reduces to support-freeness for one transform. If J is the unit ideal, the second transform is unchanged and the assertion reduces to the first one. A zero or nilpotent centre ideal has empty blowup, so assertions on that space are vacuous. For a Cartier first centre b can be an isomorphism with E nonempty: the first module transform still kills E-supported sections, so the proof correctly retains the centre rather than using only the blowup morphism. No flatness of f is used. Empty Z1 and loci meeting E also satisfy the pointwise set argument.

I checked C1/C4 against every cited statement and wrote a verbatim quotation for each citation. No new node relabels a clause of the item, and no cited proof is being mined for a stronger claim. Each step is under 2000 characters. The only off-unit nonclosed geometric tool is principalization of the blowup centre; it is declared under split_report.tool_uses because the trace-formula unit provides no replacement for this generic blowup fact. The remaining off-unit blowup tools have closed Lean audits. The current Mathlib search log records all four required services and a second semantic phrasing. Their returned signatures concern structure-sheaf localization, presentations or abstract supports, not the required module-transform assertion; none is an attachment or a one-line leaf. Earlier searches on the item were retained.

## Unfinished work

None within the one-level split. The reused unsplit dependencies remain existing queue items. Delivery validation and push are performed by the prescribed delivery tool.
