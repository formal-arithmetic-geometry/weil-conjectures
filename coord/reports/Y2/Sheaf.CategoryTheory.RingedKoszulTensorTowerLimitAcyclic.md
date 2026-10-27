## What changed

Proved the original `CategoryTheory.ringedKoszulTensorTower_limit_comparison_isIso`
from the strictly ordinary-complex inclusion theorem in the new module
`Sheaf.CategoryTheory.RingedKoszulRoosInclusion`. The original signature and all
public imports are preserved. All added imports in the item are proof imports.

The completed part is the finite split-perfect tensor calculation and the entire
resolution/comparison argument, without assuming exact countable products. The
positive Koszul complexes have support [0,r] by two-row total-term induction.
Their dual terms are finite free by the existing Hom-single and finite-free
lemmas; the proof explicitly converts their finite coproduct into a finite
product and supplies the splitting required by the split-perfect tensor theorem.
Thus each level of the tensor tower is K-injective.

For a quasi-isomorphism between towers with K-injective levels, the product maps
are quasi-isomorphisms because both ordinary products represent derived products.
Naturality of `piComparison` proves this by conjugating to the product of the
localized level maps. The cone and shift constructions give the same conclusion
for the Roos fibre. Resolve the tower by a K-injective tower with injective terms.
The existing injective-term Roos inclusion is a quasi-isomorphism; its proof uses
split transitions and a short exact sequence, without exact products. Naturality
of that inclusion then proves that the ordinary-limit resolution map is a
quasi-isomorphism. Finally the naturality square of `D.comparison`, and its
specified invertibility on K-injective towers, give the desired isomorphism.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ringedKoszulTensorTower_limit_comparison_isIso`.
The item now has zero holes. Added one hole:
`CategoryTheory.quasiIso_ringedKoszul_roosComparison`
(node `lem-weil-pbc-ringed-koszul-roos-inclusion`). This is a decomposition, with
net zero holes closed, rather than a complete proof of inverse-limit acyclicity.
All private helpers in the item are proved. The complete sandbox compiled cleanly:
3.8 seconds for the new module and 17.6 seconds for the item, before removing the
unused development import; the delivery gate recompiles the final packet.

The remaining theorem is about a specified map between ordinary complexes. It
has no `D`, no derived-limit functor, no right-derived universal property and no
normalization against a chosen derived functor. Its source is Stacks 0A0A and
0949. Its docstring and node give the telescope/Hom proof including both cone
legs and the signed normalization of the explicit Roos map. The comparison
argument needed to pass from that chain calculation to every presentation D is
proved here, rather than moved into the new theorem.

## No longer needed

Removed the unused proof import `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
from the development version. No existing public import was removed and no module is withdrawn. The original
node's direct dependencies `lem-weil-pbc-ringed-koszul-colimit-hom-ordinary-limit`,
`lem-pc-complex-hocolim-colimit` and `lem-pur-rhom-well-defined` are now needed only
below the new ordinary-complex inclusion node. They remain its explicit proof
dependencies and are not globally pruned. The product K-injective,
split-perfect tensor K-injective, strict-tower resolution and Koszul-system
nodes remain needed. The existing finite dual Koszul term proof is reused by
proof-only `import all`, without editing its public interface or duplicating
its private helpers. No source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies do not themselves state the chain-level identification
of Hom of the telescope with the specified ordinary-limit-to-Roos map. The
ordinary Hom/colimit theorem states a natural isomorphism of limits, while the
strict-tower derived-limit theorem states a derived Roos triangle. Their
normalization with the actual map cannot be obtained merely by naming those
results. This precise ordinary-complex calculation is the remaining node.

The already proved full strict Roos descent interface assumes exact countable
products. Applying it here would add an unavailable hypothesis. Instead the
proof uses derived products only for the two families of K-injective levels;
this is why no exactness of arbitrary products enters the completed argument.

The unit record `sk-thm-properbasechange` and its realized steps are unchanged.
No target statement, definition, consumer interface or adopted source file changes.

## New nodes

`lem-weil-pbc-ringed-koszul-roos-inclusion`, realized by
`Sheaf.CategoryTheory.RingedKoszulRoosInclusion`: the canonical ordinary Koszul
limit inclusion into the explicit Roos fibre is a quasi-isomorphism on
K-injective coefficients. Source: Stacks sites-cohomology 0A0A and derived 0949.
Blueprint-wide searches for Koszul and telescope found no duplicate ordinary-chain
statement; the new node retains the original node’s completed-pullback ancestor.
LeanSearch returned general internal-Hom and colimit/limit universal properties;
LeanFinder returned unrelated injective-resolution comparisons; Loogle returned
the general right-derived universal-property API; source searches found no
signed strict Koszul telescope/Roos map theorem. The existing exact-product Roos
comparison has an extra exactness hypothesis, and HomComplexMappingCone treats
the other variable. The new node is strictly the ordinary-chain-map step.

Edge cases checked against the argument: r=0 gives the constant unit tower;
zero and invertible generators require no division or nonvanishing hypothesis;
I need not have injective terms; the site need not have exact countable
products. Only the chosen tower resolution has injective terms.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
