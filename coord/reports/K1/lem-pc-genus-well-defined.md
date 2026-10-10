1. Files written

- `dag/nodes/sec-picard-framework/lem-pc-genus-well-defined.json`: repaired split statement.
- `dag/nodes/sec-picard-framework/lem-pc-projective-base-change.json`: new unsplit statement node; Mathlib search verdict no match; corrected its source to Tags 01WF and 01K5.

2. Attachments

None. The source declaration `finiteDimensional_H` mentions this blueprint item in its docstring, but has a properness hypothesis and is not the item's exact statement.

3. WANTED:

None.

4. Problems found

The original step 1 did not establish that the base change is a curve: it omitted dimension one, separation, finite type, and reducedness. Step 2 omitted the properness hypothesis of the cited cohomology theorem. The projectivity node cited Tag 02V6, which treats Stacks' broader projective-bundle convention, while this project defines projective as H-projective and quasi-compact. I repaired the two proof steps and changed that node's source to Tags 01WF and 01K5. The item statement is unchanged.

5. Unfinished work

None in this one-level split. The new projectivity statement remains unsplit, as required for a new non-Mathlib node.

## Review by K1

I read the item's blueprint proof and the `sk-thm-picard-rr` unit, the Stacks source for Tags 01WF (H-projective base change) and 01K5 (quasi-compact base change), and the statements of every DAG node cited below. The item's hypotheses are a field, a smooth projective curve, and geometric irreducibility; its conclusion is finite-dimensional first structure-sheaf cohomology, matching the blueprint. The new node's arbitrary scheme base change is exactly the scope of 01WF and 01K5 together: a closed immersion into relative projective space remains such after base change, and quasi-compactness remains true. I searched the DAG and blueprint for this statement before creating it, then recorded LeanSearch, Loogle, and a Mathlib-source grep; no exact Mathlib theorem was found.

In step 1, `lem-pc-algebraic-closure-exists-unique` supplies the algebraically closed extension, and `def-pc-base-change` identifies its fibre product. The starting `def-pc-smooth-projective-curve` gives a smooth and projective structure morphism and a curve as defined in `def-pc-curve`, so the starting hypotheses of the stability results hold. `lem-pc-proper-base-change` clause (2) preserves smoothness, and `lem-pc-projective-base-change` preserves projectivity for this project's convention. `lem-pc-dim-base-change` applies because X is a curve over a field and gives dimension exactly one. `lem-pc-projective-proper` makes X proper; then `lem-pc-proper-base-change` clause (1) makes its base change proper, whose separated and finite-type clauses are exactly `def-weil-proper-morphism`. `sbc-lem-smooth-geometrically-reduced` applies to smooth X over Spec k and makes its fibre geometrically reduced, hence its base change to the chosen algebraic closure reduced. `def-pc-geometrically-irreducible` gives irreducibility there. The nonempty curve and its geometrically irreducible base change meet the nonempty requirement of `def-pc-integral-scheme`; reduced plus irreducible gives integral. Thus all conditions of `def-pc-curve` and `def-pc-smooth-projective-curve` hold over the algebraically closed field. `lem-pc-curve-coherent-finiteness` then applies to the coherent structure sheaf at degree one. No cited node is used for more than its statement says.

In step 2, `def-pc-smooth-projective-curve` supplies projectivity and `lem-pc-projective-proper` supplies the properness hypothesis of `lem-sc-flat-base-change-coherent`. A field extension is flat, the structure sheaf is quasi-coherent, and its pullback under base change is the structure sheaf of the base-changed scheme. With these hypotheses checked, the cited theorem at i=1 gives the displayed isomorphism. Step 3 is elementary linear algebra: a finite independent set remains independent after a field extension, so an infinite-dimensional space cannot become finite-dimensional after extension.

For the returned C1/E1 point, I added the dimension, properness, separation, finite-type, reducedness, and integrality citations in step 1 and in `proof_deps`. For C1/C4, I made properness and the structure-sheaf pullback explicit in step 2. For B5, I replaced Tag 02V6 in the new node's `source.place` and in step 1's source. The other-unit generic facts `lem-pc-projective-proper` and `sbc-lem-smooth-geometrically-reduced` are declared in `split_report.tool_uses`; neither is supplied by a node of `sk-thm-picard-rr`. The projective-base-change statement holds for the identity base change and for P^1 over any field extension; the item's P^1 case has H^1(O)=0. These small cases expose no missing hypothesis or false conclusion.
