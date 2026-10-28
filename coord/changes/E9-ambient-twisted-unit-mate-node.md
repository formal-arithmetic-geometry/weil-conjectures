# lem-sfb-ambient-twisted-unit-mate

## Reason

The existing DAG prose describes composition of unshifted rational Tate-line comparisons,
while its existing Lean attachment, module docstring, theorem, and parent all identify the
ambient twisted-unit mate equation. Correct that metadata to the unchanged Lean statement.
The proof uses Mathlib unit_mateEquiv, exchange naturality, and unit naturality.

## Old

For a prime l, a finite rational coefficient index c or the algebraic-closure index, and composable scheme arrows f:X→Y and g:Y→Z with l invertible in every residue field of X,Y,Z, let Λ=(coefficient l c).X and L_A=line l c A as in [def-sfb-rational-tate-pullback-comparison]. Then the canonical underived internal-module compositor c_f,g:(f≫g)*≅g*⋙f*, followed by f* of lineComparison(g) and lineComparison(f), equals lineComparison(f≫g). This is an equality of unshifted module maps, before taking degree-zero complexes, derived functors, shifts, exchange mates or adjunction units.

## New

Let $\Lambda$ be a commutative condensed coefficient ring and let $\square$ be a chosen cartesian square with edges $g':X'\to X$, $f':X'\to Y'$, $f:X\to Y$, and $g:Y'\to Y$. Write $L_t=Lt^*$ and $R_t=Rt_*$ for the ambient internal-module derived pullback and pushforward, $\theta:L_{f'}\circ L_g\to L_{g'}\circ L_f$ for the canonical pullback comparison, and $E:L_gR_f\to R_{f'}L_{g'}$ for its right mate [def-weil-pbc-ambient-ringed-exchange]. For $A\in D(\mathrm{Modules}(\Lambda,Y))$, $B\in D(\mathrm{Modules}(\Lambda,X))$, $B'\in D(\mathrm{Modules}(\Lambda,Y'))$, $Q\in D(\mathrm{Modules}(\Lambda,X'))$, isomorphisms $e:L_fA\simeq B$, $e_2:L_{f'}B'\simeq Q$, and maps $j:L_gA\to B'$, $d:L_{g'}B\to Q$, suppose that, writing composites left to right, $\theta_A\gg L_{g'}(e.\mathrm{hom})\gg d=L_{f'}(j)\gg e_2.\mathrm{hom}$. Define $u_f(e)=\eta_{f,A}\gg R_f(e.\mathrm{hom})$ and $u_{f'}(e_2)=\eta_{f',B'}\gg R_{f'}(e_2.\mathrm{hom})$, the specified scalarTwistedUnit maps [def-sfb-rational-p1-scalar-chern-maps]. Then $L_g(u_f(e))\gg E_B\gg R_{f'}(d)=j\gg u_{f'}(e_2)$.

The Lean signature is identical. This is a DAG statement correction only, not a change
to any definition or target. The correction source and complete list of citing nodes are
in statement_change. The schema calls its attribution "E9 stage 2"; this is the stage-3
worker repairing the statement metadata.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AmbientTwistedUnitMate | E9 | Same theorem signature; replace its sorry by a categorical proof. |
| Sheaf.Paper.ScalarComponentFromTrace | F6 | Direct importer and citing DAG parent; no signature or behavior change. |
| Sheaf.Paper.ScalarP1UnitMateComponent | unclaimed | Direct importer and citing DAG parent; no signature or behavior change. |

The read-only downstream --uses search found 709 transitive importers and no call of
ambient_twisted_unit_mate outside its own module in the shared snapshot. All remain
compatible because the Lean declaration is preserved. The two removed redundant public imports
remain transitively re-exported through RationalP1ScalarChernMaps. The private import all
of the derived source module is unused and was removed. The two
parent nodes are lem-sfb-scalar-component-from-trace and
lem-sfb-rational-p1-scalar-chern-base-change-unit-component-core; both uses still hold.

## Status

landed 20261028T034738-L-3539653 2026-10-28 (merge of deliver/E9/Sheaf.Paper.AmbientTwistedUnitMate)
