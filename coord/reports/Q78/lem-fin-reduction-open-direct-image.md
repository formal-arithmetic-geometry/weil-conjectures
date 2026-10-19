## Worker report

The module `Sheaf.SecSmoothPurity.FinReductionOpenDirectImage` states
`AlgebraicGeometry.Etale.finReductionOpenDirectImage`.  It uses the canonical
reductions `U.nilradical.subschemeι` and `X.nilradical.subschemeι`, and the induced
map of reductions
`(U.nilradical.subschemeι ≫ j).liftNilradical :
U.nilradical.subscheme ⟶ X.nilradical.subscheme`.  For every commutative ring
`Λ : Type (u + 1)`, every pair of schemes `U X : Scheme.{u}`, and every open
immersion `j : U ⟶ X`, the theorem gives a `Nonempty` natural isomorphism of
functors on `Sheaf _ (ModuleCat.{u + 1} Λ)`:
`lowerStar ... j ≅ upperStar ... U.nilradical.subschemeι ⋙
lowerStar ... ((U.nilradical.subschemeι ≫ j).liftNilradical) ⋙
lowerStar ... X.nilradical.subschemeι`.  A component is the required
Λ-linear isomorphism `j_* F ≅ r_* j_red,* s⁻¹ F`; naturality in `F` is the
naturality field of the natural isomorphism.  No reducedness, Noetherianity,
finite type, finiteness, or constructibility hypotheses occur.

The `Λ` hypothesis is rendered by `(Λ : Type (u + 1)) [CommRing Λ]`.  The scheme
objects and their common universe are `{U X : Scheme.{u}}`; the open immersion
hypothesis is `[IsOpenImmersion j]`.  The direct image is
`lowerStar (ModuleCat.{u + 1} Λ) j`; inverse image is
`upperStar (ModuleCat.{u + 1} Λ) U.nilradical.subschemeι`; the reduced open map
is the displayed `liftNilradical`; and the ambient reduced direct image is
`lowerStar (ModuleCat.{u + 1} Λ) X.nilradical.subschemeι`.

Dependency declarations used: `AlgebraicGeometry.Etale.lowerStar` and
`AlgebraicGeometry.Etale.upperStar` from
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; schemes and
`IsOpenImmersion` from Mathlib; `Scheme.nilradical`,
`IdealSheafData.subscheme`, `IdealSheafData.subschemeι`, and
`Scheme.Hom.liftNilradical` from
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
`ModuleCat` and its Abelian structure come from
`Mathlib.Algebra.Category.ModuleCat.AB`.

Edge cases checked: `U` and `X` are arbitrary schemes, including the empty
scheme and nonreduced schemes; `j` can be the identity open immersion; `Λ` can
be the zero commutative ring; and no finiteness or Noetherian assumption is
introduced.  The common universe `u` is retained for schemes and
`u + 1` for module coefficients.

Searches for an existing declaration: `msearch.py ... leanfinder` with query
“open immersion direct image reduction small etale module sheaves” returned only
Zariski module-restriction and étale-site declarations, with no match;
`msearch.py ... loogle` for `AlgebraicGeometry.Etale.lowerStar,
AlgebraicGeometry.Etale.upperStar, Scheme.Hom.liftNilradical` returned no hits;
`msearch.py ... grep` for `reduction.*direct.*image|direct.*image.*reduction`
in `Mathlib/AlgebraicGeometry` returned no hits; and `rg` over
`WeilConjectures/` and project `lean/Sheaf` found no statement of this
comparison (the only reduction hit was an unrelated equivalence lemma).

No `STATEMENT-DISPUTED` flag or node fault.

## Second reading by Q78

The node and module were read together.  The theorem binds exactly the ring,
coefficient universe, two schemes, and open immersion named by the node.  Its
left functor is `j_*`; the right composite applies inverse image along the
reduction of `U`, then direct image along the induced reduced open map, then
along the reduction of `X`, exactly in the node's order.  `Nonempty` of a
`NatIso` supplies one natural componentwise module isomorphism for every `F`.
No hypotheses or conclusion clauses were added or omitted, and the canonical
`liftNilradical` map is the induced `j_red`.
