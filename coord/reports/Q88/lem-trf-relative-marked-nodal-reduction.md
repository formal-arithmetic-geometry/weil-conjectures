# Worker report: lem-trf-relative-marked-nodal-reduction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-relative-marked-nodal-reduction.json`: repaired item proof and dependencies; the statement is unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-dejong-relative-marked-semistable.json`: repaired source input, retaining the closed boundary and the (T') clause; no Mathlib match.
- `dag/nodes/sec-trace-formula/def-trf-projective-bundle-morphism.json`: new definition of the EGA/ILO projective-bundle convention; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-projective-bundle-to-h-projective.json`: new Stacks 087S conversion statement; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-h-projective-composition.json`: new Stacks 01WE composition statement; no Mathlib match.
- `citations.json`: verbatim quotations for every cited node in every proof step.

## Attachments

None. The source and slopmaster2 searches still contain no sorry-free declaration for this item or for the new geometric statements.

## WANTED

None. ILO Exposé IX and the cited Stacks files are present locally.

## Not duplicates

- `lem-trf-dejong-relative-marked-semistable` vs `lem-trf-relative-marked-nodal-reduction`: the new node is the ILO projective-bundle-convention existence theorem with its own closed nowhere-dense (T'); the item converts projectivity, renames (T'), and obtains finite etaleness.
- `def-trf-projective-bundle-morphism` vs `def-kun-projective`: the new definition uses a closed immersion into (mathbf P_S(mathcal E)) for a finite-type quasi-coherent module, whereas `def-kun-projective` uses finite projective space (mathbf P^N_S).
- `lem-trf-projective-bundle-to-h-projective` vs `lem-trf-h-projective-composition`: the former is Tag 087S and requires an ample invertible sheaf on the base; the latter is Tag 01WE and composes two H-projective morphisms.
- `def-trf-projective-bundle-morphism` vs `def-pc-projective-morphism`: both cite Tag 01W8, but the existing node defines the finite-projective-space H-projective convention with quasi-compactness, while the new node records EGA projective-bundle projectivity via a finite-type quasi-coherent module.
- `lem-trf-projective-bundle-to-h-projective` vs `lem-trf-relative-marked-nodal-reduction`: the item cites 087S only as a source for its projectivity conversion; the new node states the reusable conversion theorem with its ample-base hypothesis.
- `lem-trf-projective-bundle-to-h-projective` vs `lem-weil-pbc-finite-separable-base-refinement`: the existing node concerns separable base refinement and uses 087S only in its proof source; the new node states 087S itself.
- `lem-trf-projective-bundle-to-h-projective` vs `lem-trf-alteration-relative-curve-preparation`: the existing node is a relative-curve preparation theorem whose source mentions 087S; the new node is the standalone projectivity conversion.
- `lem-trf-h-projective-composition` vs `lem-trf-relative-marked-nodal-reduction`: the item cites 01WE only as a source for conversion; the new node states the reusable composition theorem.
- `lem-trf-h-projective-composition` vs `lem-weil-pbc-isomorphism-finite`: the existing node uses 01WE for the elementary fact that an isomorphism is finite; the new node states composition of H-projective morphisms.
- `lem-trf-h-projective-composition` vs `lem-trf-alteration-relative-curve-preparation`: the existing node is a curve-preparation theorem whose source mentions 01WE; the new node is the standalone H-projective composition theorem.

- `lem-trf-dejong-relative-marked-semistable` vs `lem-trf-plurinodal-alteration`: the existing node is a trait tower/field alteration theorem; this node is one relative curve over a projective excellent base with a marked divisor and a bad-base subset.
- `lem-trf-dejong-relative-marked-semistable` vs `lem-trf-projective-nodal-family-geometry`: the existing node analyzes an already-given nodal family; this node asserts existence after alterations.

## What was wrong or corrected

The returned E2 fault was correct: ILO IX Theorem 1.2(iv) and (vi) give a closed nowhere-dense (T'), smoothness over (Y'\setminus T'), and (a^{-1}(Z)\subset D\cup f'^{-1}(T')); they do not give containment in the nonsmooth locus. The source node now states those exact clauses, and item Step 3 sets (T:=T'). This also removes the invalid construction (T=f'(\mathrm{Sing}(f'))).

The returned B3 fault was corrected by adding the explicit EGA/ILO projective-bundle definition (Stacks 01W8), retaining the hypothesis that (Z) is a closed subscheme, and adding the two real conversion statements for Tags 087S and 01WE. Step 2 now proves the conversion through the ample line bundle on (Y), H-projectivity of (b), composition to (Y'\to\operatorname{Spec}R), an ample line bundle on (Y'), and H-projectivity of (f'). It does not use `def-kun-projective` as a definition of the source convention.

The returned C1/C2 faults were corrected by making Step 2 non-elementary and citing each conversion and ample-line-bundle input. Step 4 now cites the etale definition, the existing unramified-to-locally-quasi-finite statement, and the proper-plus-locally-quasi-finite finiteness criterion. Every citation has a verbatim quote in `citations.json`.

## Review by Q88

I reread ILO Exposé IX Theorem 1.2 at printed pp. 130–131, especially clauses (i), (iii), (iv), (v), and (vi), and the paragraph defining a nodal curve. The repaired source node now matches its hypotheses one by one: proper dominant excellent integral Noetherian schemes, a smooth irreducible one-dimensional generic fibre, and a nowhere-dense closed (Z) with etale generic fibre. It records the trivial-group specialization, the projective-bundle convention, the closed (T'), smoothness off (T'), and the exact boundary inclusion. I checked the ordinary-double-point convention against the same paragraph.

For Step 1, the source node supplies the alteration square, properness and generic finiteness of (a), projective-bundle projectivity of (b) and (f'), the nodal fibre clauses, the marked Cartier divisor, and the (T') boundary clauses. For Step 2, I read Stacks Definition 01W8 and Lemma 087S and 01WE in `morphisms.tex`; the new definition node states the EGA projective-bundle notion, 087S converts it over a base with an ample invertible sheaf, and 01WE composes H-projective maps. The existing projective-ample node supplies the ample sheaf on (Y) and, after composition, on (Y'), using the closed immersions supplied by `def-kun-projective`. Step 2 therefore has all hypotheses in force and no longer hides the ample-sheaf input.

For Step 3, I checked that it is only the permitted renaming (T:=T'): the cited source node explicitly says (T') is closed and nowhere dense, (f') is smooth off it, and the boundary lies in (D\cup f'^{-1}(T')). For Step 4, I read the etale definition (02GI), the existing statement of unramified morphisms being locally quasi-finite (02V5), and the proper locally quasi-finite finiteness criterion (02LS); these exactly justify the finite etale conclusion. I tested the edge cases (Z=\varnothing), (T'=\varnothing) for a smooth family, and the identity projective-bundle/H-projective conversion on projective space. The four proof steps are now supported by the listed nodes, have no false singular-locus inference, and introduce no cycle or forbidden source.

No Lean files, compiler, Lake, or build tools were used.
