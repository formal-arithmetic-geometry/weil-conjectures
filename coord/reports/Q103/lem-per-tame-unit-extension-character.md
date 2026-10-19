## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-tame-unit-extension-character.json: statement item, split into seven steps; no exact Mathlib match.
- No new nodes or Mathlib leaves. citations.json records every proof-step citation with the verbatim statement read. searches.jsonl retains the executed searches.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the item id, tame/Kummer terminology, unit extension, principal units and character splitting found no declaration stating the item. The p-adic principal-unit logarithm is a different result.

## Wanted literature

None. Read the local ILO arXiv-1207.3648 PDF, Exposé VI §§3.4–3.7, especially printed pp.74–75 (PDF pp.80–81), and Stacks algebra.tex Tags 04GF (definition-henselian), 04GG (lemma-characterize-henselian), 06RR (lemma-uniqueness). The local current-blueprint ancestor proof and unit/chapter records were also read.

## Source error

The item statement is unchanged and is true. ILO VI 3.7(a), p.75, prints z(g1 g2,a) = (g1 z(g2,a)) z(g2,a). Its last factor must be z(g1,a). For example over C, let H=C2 act trivially on C and act on E=C^××Z by the sign character in the second coordinate, with s0(m)=(1,m). Then z(1,1)=1 and z(t,1)=-1. The printed formula with g1=1,g2=t would give -1=1. Step 2 derives the correct cocycle identity directly from the action.

The sentence after the cocycle square also cannot mean that the original arbitrary cocycle is the unique lift of its residue character. Principal-unit cocycles can be nontrivial coboundaries. For example A=C[[t]], H=C2 acting by t↦-t, b=1+t, E=A^××Z, and the action h(u,m)=(h(u)(h(b)/b)^m,m) gives z_h(1)=(1-t)/(1+t), which reduces to 1 but is not a root of unity. The conclusion is obtained after changing the chosen section. Steps 5–7 give that change explicitly. No assertion about the target, the unit, or its route is changed.

## What was corrected

The empty proof was replaced by the concrete root-lifting, finite-product, and section-adjustment argument. No cohomology-vanishing assertion is used as an uncited theorem. Existing henselian-local-root-lifting and simple-root-uniqueness nodes are cited for exactly their statements, rather than using the definition of henselianity as a theorem. The imported statement dependencies and provenance were preserved. The proof_origin follows ILO, with the implicit finite-product coboundary calculation expanded. All new search records correspond to actual msearch.py calls; the first Loogle query had an unknown capitalized identifier, explicitly recorded as invalid and followed by a valid query. The inherited Q131 searches were retained rather than claimed as searches run by Q103.

## Not duplicates

No new nodes were created. The global blueprint searches for unit extension, principal unit, cocycle and character, and DAG searches for simple roots, henselian lifting, principal units, lattice extensions and the source terms found the two generic algebra tools used here. lem-per-divisible-unit-lattice-extension enlarges a lattice through an n-divisible subgroup and does not impose an H-action or construct a character. lem-per-very-tame-equivariant-sharp-chart is the parent and spreads the resulting germ; lem-per-very-tame-local-kummer-quotient concerns invariants after such a chart is given. Neither is used circularly. The principal-unit logarithm node concerns deep units in finite p-adic extensions; it is not used.

## Review by Q103

I checked the item against ILO VI 3.7(a), pp.74–75: the exact unit extension and trivial action on L produce the cocycle; the residue action is trivial; the order n is invertible; and the output is a character and an adjusted splitting. The source abbreviates the cohomology calculation. The split instead writes its finite-product computation in full. Finite freeness and the sharp monoid hypothesis are retained as stated, although the given initial section means the adjustment needs only an abelian L and the unit stability of M. There is no need for Noetherianity, a domain assumption, completeness, or trivial H-action on A itself.

Step 1 uses the statement of lem-weil-pbc-henselian-local-root-lifting in direction (i)⇒(ii) for T^n-u, residue 1; I opened that node and confirmed it gives existence for a monic polynomial with a simple residue root. Its hypotheses follow from the strictly henselian assumption and n∈A^×. I also opened lem-weil-pbc-simple-root-uniqueness: it says two roots in the same residue class agree when the derivative is a unit. This supplies the uniqueness needed for r, whose multiplicativity and H-equivariance are then direct equations of nth powers and residues.

Step 2 defines the unit-valued ratio using exactness and derives its cocycle identity by applying g to h(s0(l)); no outside theorem is used. Step 3 multiplies the residue homomorphism identity over H and reindexes the finite product; this proves nth torsion without an uncited Lagrange or cohomology theorem.

Step 4 cites those same two opened algebra statements, this time for T^n-1 and the nonzero residue value. The derivative n times a power of a nonzero root is nonzero. Products of the unique lifts prove both multiplicativities; the trivial action on k puts h(zeta) in the same residue class as zeta, proving all roots of unity fixed. The existing strict-local-roots-of-unity node was read but not cited: its statement gives cardinality/cyclicity and the unit difference property, whereas the two simple-root statements give precisely the lift and uniqueness required here.

Step 5 explicitly defines the residual principal-unit cocycle and its finite product P. Reindexing gives g(P)/P=d_g^{-n}; the sign is checked before choosing b. Step 6 uses simple-root uniqueness once more, now for T^n-d_g^{-n}, to deduce g(b)/b=d_g^{-1}. This sign is essential: b multiplies s0 in Step 7. Step 7 checks the section, membership in M on L_+, and the action equation by direct multiplication. The commutator quotient and tensor factorization use the defining universal properties, not a new lemma. Every proof-step dependency is quoted verbatim in citations.json, and proof_deps is their union.

I tested H=1 (n=1, all cocycles and corrections equal 1), L=0, M consisting only of units, the field A=C with a nontrivial sign character, and the nontrivial principal-unit coboundary over C[[t]] just described. For that last example the product correction kills the principal part with the inverse sign required in Step 6. I also checked that the root argument permits nilpotents, for example A=C[epsilon]/(epsilon^2), because it only uses a unit derivative. If n is not invertible uniqueness fails (in characteristic p, (1+epsilon)^p=1 when epsilon^p=0); that excluded case confirms the hypothesis is used at exactly Steps 1,4,6.

Against delivery-errors B–E: there are no new statement-only nodes to validate; all notions already have the item's existing definition dependencies or are ordinary group/ring constructions. No new node repeats a clause of the item. The only non-elementary cited inputs have been read and their hypotheses checked above; no step uses a dependency's proof. Neither parent nor descendant is cited, so the generic algebra tools introduce no cycle. Each step is below 2000 characters; the finite-product calculation is written in separate routine equations, not hidden behind a comparison or a claimed cohomology vanishing. No SGA source or route is used.

## Unfinished work

None in the mathematical split. Required server checks and direct delivery are run after this report is written.
