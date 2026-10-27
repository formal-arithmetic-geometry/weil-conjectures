## Worker report

The module `Sheaf.Paper.RefinementInverseMateComparisons` states
`AlgebraicGeometry.RefinementInverseMateData.refinement_inverse_mate_comparisons`.
It has one postponed theorem, with proof `sorry`, and four helper constructions:
`restricted`, `restrictedGamma`, `theta`, and `compare`. `RefinementInverseMateData`
merely bundles the hypotheses of this item; it is not a second proper/open calculus.
In particular it has no interchanges for arbitrary proper/open squares and no tower data.
The supplied mates on the ambient categories need not be invertible.

The original node is unchanged outside `lean`; no correction, new node, or dependency
repair is needed. No theorem is proved. All helper data is constructed, with no sorry
or arbitrary choice of an isomorphism: `asIso` inverts the already supplied restricted
natural transformation, whose inverse is unique. The sole sorry carries all eight
proof steps of the node in its docstring.

Clause-by-clause rendering (Lean uses diagrammatic composition `≫`, the reverse of
the node's functional-order notation):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Schemes X,Y and separated finite-type f | `{X Y : Scheme.{u}} {f : X ⟶ Y}`, with `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` on the theorem. The latter two classes are finite type. |
| f admits a compactification | `[IsCofiltered (Compactification f)]` includes nonemptiness, so this already supplies existence; no independent compactification choice is made. |
| Objects and proper refinements of Comp(f) | The actual upstream `Compactification f` category and `Compactification.Refinement` are used. `r.hom`, `r.i_hom`, `r.hom_g` give the ambient proper map and its two triangles. |
| Common refinements and equalizing parallel arrows | Mathlib `IsCofiltered` on precisely that category supplies both, with its nonemptiness clause justified by compactifiability. |
| Categories D_W and fixed universes | `T.D`, `T.category`, and explicit independent universes `u v w`; schemes are in u, category objects in w and morphisms in v. D is written on the ambient type of schemes; only X,Y and the compactifying schemes enter the assertion. Any assignment on the schemes involved can be extended on unused schemes by a terminal category, without changing any of these expressions or requiring comparisons on extra squares. |
| Proper functors R_u | `T.R p [IsProper p]`; no preservation or exactness assumption. |
| Natural invertible compositors c_(v,u) | `T.comp p q pq h : T.R pq ≅ T.R p ⋙ T.R q`. The named composite `pq` and proof `h` avoid casts. The node's R_v R_u is diagrammatically R_u followed by R_v. |
| Unital compositors | `T.rId`, `T.left`, `T.right` state identity normalization with the necessary natural proper unitors. No strict equality between R_id and the identity functor is imposed. |
| Compositor associativity | `T.assoc` is exactly the displayed equation at every object, with all three composite-map equalities explicit. Natural transformations are equal exactly when all their components are equal. |
| J_c for every compactification | `T.J c : T.D X ⥤ T.D c.Z`. |
| Natural gamma_r for each refinement | `T.gamma r : T.J d ⟶ T.J c ⋙ T.R r.hom`. |
| gamma_1 = 1 | `T.gammaId`, with `T.rId` inserted to identify the codomain with J_c. This is the normalized identity equation, not a strictification assumption. |
| Vertical-pasting equation | `T.gammaComp r s M`: gamma_(rs) then the compositor equals gamma_s then R_s(gamma_r), for every M in the ambient D_X. |
| E full in D_X | `E : ObjectProperty (T.D X)`, using exactly Mathlib `E.FullSubcategory` and inclusion `E.ι`. No closure or nonemptiness condition is imposed. |
| Invertible mates only on E | `hE` quantifies over r and `M : E.FullSubcategory`; there is no assertion about objects outside E. `restrictedGamma` uses `Functor.whiskerLeft` and `NatIso.isIso_of_isIso_app` to invert precisely the restriction. |
| F_c = R_(p_c) J_c on E | `T.restricted E c = (E.ι ⋙ T.J c) ⋙ T.R c.g`. |
| Specified formula for theta_r | `T.theta E hE r` first uses `isoWhiskerLeft` of `T.comp r.hom d.g c.g r.hom_g`, then reassociates, then uses `isoWhiskerRight` of `(restrictedGamma ... r).symm` with `T.R d.g`. This is the node's formula verbatim in diagrammatic order. |
| theta_id = 1 | First conjunct: `theta ... (𝟙 c) = Iso.refl (restricted ... c)`. |
| theta_(rs) = theta_r then theta_s | First part of second conjunct is equality of `.hom` natural transformations. |
| Explicit four-factor expression | Second part of second conjunct, for every `M : E.FullSubcategory`: c_(p2,r), c_(p3,s) at R_r J_c M, R_p3 R_s(gamma_r inverse), then R_p3(gamma_s inverse). These are exactly the four factors in the node, reversed to diagrammatic order. Together with the previous equality this identifies both sides with that expression. |
| Parallel refinements give equal transformations | Third conjunct, arbitrary `a b : c ⟶ d`, compares their theta `.hom` transformations. It does not assert a=b or cartesianness. |
| C_12 on a common refinement | `compare r s := (theta r).symm ≪≫ theta s`, without choosing any span. |
| Independence of d,a,b | Fourth conjunct universally quantifies over two arbitrary vertices and both pairs of arrows, and equates the resulting natural isomorphisms. |
| C_23 C_12 = C_13 | Fifth conjunct uses arbitrary spans for all three pairs, with equality in the functor category. |
| C_11 = 1 | Sixth conjunct permits any vertex and both arrows into c, not merely the identity span. |
| No evaluation detection | There is no evaluation functor, faithful functor, or equality-detection hypothesis anywhere. Component equations for the supplied coherence axioms and explicit formula are ordinary natural-transformation extensionality. |

Dependency interfaces read and used:

- `def-nagata-category`: `CategoryTheory.Category` in
  `Mathlib.CategoryTheory.Category.Basic` (its full `CategoryStruct` and category-law
  signatures were read). The upstream refinement-category import exposes it.
- `def-weil-compactifications-refinements`:
  `AlgebraicGeometry.Compactification.Refinement` and
  `AlgebraicGeometry.Compactification.category`, from
  `WeilConjectures.Compactification.RefinementCategory`. Its source and docstrings,
  and `WeilConjectures.Compactification.Defs`, were read. Properness of `r.hom`
  is already an upstream instance. No private compactification definition is used.
- `def-weil-size-convention`: the existing record explicitly marks this a
  metatheoretic convention, with no Lean object to import. Independent explicit
  universes implement it; the upstream `ModuleDerivedCategory` convention docstring
  was also read, but that unrelated derived category is not imported.
- Mathlib's `ObjectProperty.FullSubcategory`, `ObjectProperty.ι`, `NatIso`,
  `NatIso.isIso_of_isIso_app`, whiskering and functor associators are reused.

Sources opened: `literature/stacks-project/more-etale.tex`, the complete statement
and proof of 0F7C and the common-refinement portion of 0F7J;
`literature/stacks-project/flat.tex`, 0ATU statement and proof. As the node explicitly
says, these motivate the abstract argument: their geometric existence or derived
hypotheses are not imported as extra assumptions. The source's warning that a
non-dense compactification refinement need not be cartesian is respected.

Edge cases checked before drafting and again against the resulting signature:
E may be empty or all of D_X; no inverse is taken outside E. D_X itself may be
empty. X may be empty, and compactifications may have extra components, with no
density or Cartesian-refinement requirement. No qcqs/Noetherian assumption is
added to X or Y: cofilteredness is explicitly assumed, not deduced geometrically.
The identity refinement and repeated endpoints are included. Parallel arrows may
be distinct. Spans have arbitrary vertices and arbitrary arrows, with no choices
fixed. The single-compactification and identity-morphism cases are included.
Category object and morphism universes remain independent (only the structure's
expected `linter.checkUnivs` bundling warning is suppressed locally, as in the
existing ProperOpenCalculus module). No coefficient ring, torsion bound or
boundedness condition exists in this abstract assertion.

Searches made using the prescribed wrapper (full results in `searches.jsonl`):

- LeanFinder: `Inverse pseudofunctor compositor invertible refinement natural transformations cofiltered common refinement comparisons cocycle` — 8 hits, including `Pseudofunctor.mapComp'₀₁₃_inv_app`, `mapComp'₀₂₃_inv_app` and Join/Grothendieck formulas. They give parts of compositor algebra, not the whole theorem with E-restriction and cofiltered span cancellation.
- Loogle: `CategoryTheory.IsCofiltered, CategoryTheory.IsIso` — 4 eventual-constant limit results, none the supplied inverse-mate assertion.
- LeanSearch: `Cofiltered category inverse natural transformation compactification refinement span comparison cocycle` — 8 hits on cofilteredness, cospans and filtered/cofiltered limits; none states the item.
- Wrapper grep: `cofiltered.*(iso|cocycle)|refinement.*cocycle` in CategoryTheory — 4 unrelated files (Galois/Prorepresentability, GrothendieckAxioms/Basic, Functor/Flat, Limits/Shapes/Countable).
- Local rg in both `lean/WeilConjectures` and `lean/Sheaf`: inverse-mate/refinement-comparison terms; inspected `ProperOpenCalculus` and `CompactificationRefinementCoherence`. The former assumes invertibility on all categories and all proper/open squares; the latter adds tower/staircase conclusions and uses those stronger hypotheses, so neither states this item. Also inspected the specialized derived `ProperOpenRefinementData`, whose coefficient and normalized K-injective data are unrelated to this abstract interface.
- Exact node-id grep in `lean/WeilConjectures` returned no occurrence. Exact new declaration-name searches in Mathlib, both project source trees and `dag/lean_names_upstream.json` returned no collision.

Validation: prescribed `scompile.py` compile of the module, followed by the prescribed
`deliver2.py --no-push` preflight and per-file compile. No direct repository writes,
git commands, local/global builds or launcher-tool edits were used. No node faults
or `STATEMENT-DISPUTED` findings.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
