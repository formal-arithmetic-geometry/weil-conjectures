## What changed

Removed the first worker's two new sorry theorems and their node files, and
restored the original declaration, imports, signature, and docstring verbatim.
Added a STATEMENT-DISPUTED comment to the original theorem. No theorem or
definition statement is changed. This is a counterexample report, not a proof.

## Proved and sorry left

Holes closed: none (0 of the original 1).
Holes added: none; split off: none.
The original `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
remains sorry, with node `lem-sbc-stalk-normalization-depth-two-section-flat-core`.
Removed the invalid proposed `flat_neighborhood_from_stalks` and
`normalization_stalk_flat_at_section`; neither is counted as proved.

## No longer needed

No original imports, nodes, or modules are pruned. The two rejected proposed new
nodes `new-flat-neighborhood-from-stalks` and
`new-normalization-stalk-flat-at-section` are removed before delivery.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original item drops the rational-point/split-section
hypothesis used by Stacks Tag 0EYJ. Its conclusion is false, even with a normal
Noetherian base and an identity smooth family. The first worker's new pointwise
lemma repeats that false conclusion at the closed point. The first worker's
flat-neighbourhood lemma is also unjustified: a finite morphism need not be of
finite presentation, and its source Tag 0396 defines covering families, not
openness of flatness. The proposed new nodes had empty search records, placeholder
Lean statements, no complete docstring proofs, and the original node was not
updated to the proposed proof. The original target docstring had also been
shortened without a reason. All these proposed changes were removed.

## Second reading by N2

1. Compared the entire sandbox module with the repository module by diff. The
original theorem's signature was unchanged by the first worker. After this
reading the only Lean difference is a comment marking that theorem disputed;
its original proof and docstring are restored. No definition or public import
changes; no change records are needed.

2. Compiled the first worker's module with lcompile.py: no errors, but three
letI style warnings and two new sorry theorems. No forbidden constructs or hollow
definitions. The revised module is compiled again and its original declaration's
axioms checked in a scratch copy. Its sole remaining hole is the original theorem,
not a new purported proof.

3. Read https://stacks.math.columbia.edu/tag/0EYJ and
https://stacks.math.columbia.edu/tag/0EY9. Tag 0EYJ explicitly uses a rational point
and the Galois action to split the section fibre. Those hypotheses are absent
from both the item and the proposed pointwise lemma. Tag 0396 was opened and is
unrelated. Searched with msearch.py leanfinder (finite quotient quadric cone
punctured spectrum normalization not flat), loogle (AlgebraicGeometry.Flat), and
grep (flat locus); no exact theorem supports the split. Also read Mathlib's
Normalization.lean and searched the upstream EtaleTorsor.lean and local morphism
modules. No new statement is retained.

Counterexample, hypothesis by hypothesis: let k = Q, B = k[x,y], and
A = k[x^2,xy,y^2] = k[a,b,d]/(ad-b^2). Put S = C = Spec A, c = identity,
sigma = identity, s = m = (a,b,d), and U = S minus {m}. S is affine, integral,
Noetherian and quasi-separated; c is smooth, quasi-compact and quasi-separated,
and sigma is a section. The generic point lies in U. Since the only point
outside U is s, the minimal-boundary condition holds. The hypersurface local
ring A_m is Cohen-Macaulay of dimension two, hence has depth two.

Let PA be the restriction of Spec B -> Spec A to U. B is finite over A:
1,x,y generate it, since every monomial of even total degree lies in A and
every odd monomial is x or y times an even one. U = D(a) union D(d).
On D(a), B_a = A_a[T]/(T^2-a), with T=x and y=b/T; its derivative 2T is a unit.
The same calculation with T=y proves etaleness on D(d). Thus PA is finite etale.
The omitted rational-point hypothesis fails: its generic fibre is a nontrivial
quadratic field extension of Frac A.

The source of PA is the punctured affine plane, whose global sections are B:
B_x intersect B_y = B in k(x,y). All of B is integral over A, so the relative
normalization used in Mathlib's normalizationDiagram is exactly Spec B. The
pullback n over Spec A_m is Spec(B tensor_A A_m) -> Spec A_m and is finite.
For the identity family, the section's closed point is m. Its generic rank is
two (the involution x -> -x, y -> -y fixes Frac A), whereas its closed fibre is
k[x,y]/(x^2,xy,y^2), of dimension three with basis 1,x,y. A finite flat module
over a Noetherian local ring is free; if this module were flat, its rank would
be two and its closed fibre dimension two, a contradiction. The source has
only one point over m, so the proposed pointwise flatness also fails. Any flat
open neighbourhood would imply this flatness at m. This is a mathematical
counterexample; no Lean formalization of its algebra is claimed.

4. Read dag/units/sk-prop-input-spreading.json, including its depth-two step:
that route explicitly uses the rational-point hypothesis and G-action to split
the punctured section. Its realized arrays are empty and are unchanged. The
rejected split cannot implement the unit route because it omits that input.
No original dependency is pruned and no alternate unit route is substituted.
The empty cover and identity cover would be flat, but the degree-two cover above
shows the arbitrary-cover claim fails; testing only split covers would miss it.

5. Read the original item node and both proposed new nodes. The original node
already has the same missing hypothesis as its Lean declaration. Its proof text
claims splitting by a rational section and translates which its statement never
supplies. The two proposed nodes do not justify the new proof (and the original
proof_deps still listed the depth lemmas). Removed both new nodes. Since the
original theorem is left open and disputed, its existing node's planned proof,
proof_deps, and proof_origin are retained, with the precise fault reported here.

Changes by this reading: removed the false decomposition and its two new holes,
restored the original docstring and proof, and marked the unchanged original
statement disputed with the explicit counterexample. There is no proof progress.

Validation: the revised module compiles without warnings. A scratch-copy
`#print axioms` reports exactly propext, Classical.choice, Quot.sound, and
sorryAx for the unchanged open theorem. The delivery dry run passed compilation
and preflight, classified CODEX because of the new STATEMENT-DISPUTED report.
