## Worker report

The module `Sheaf.AlgebraicGeometry.ProperEtaleRelationFiniteNeighbourhood` states
`AlgebraicGeometry.exists_finite_etale_restricted_relation_neighbourhood` with proof
`sorry`.  It uses the existing scheme, étale, fibre-product, closed-immersion,
residue-field, finite-morphism, and open-immersion notions; it introduces no new
definition.  The theorem has the following direct rendering of the node.

* The affine schemes are `T U R : Scheme.{u}` with `[IsAffine T]`, `[IsAffine U]`,
  and `[IsAffine R]`; the structure maps are the explicit `fU : U ⟶ T` and
  `fR : R ⟶ T`.
* Local quasi-finiteness is
  `Scheme.Hom.IsLocallyQuasiFinite fU`.
* The two relation projections are `s t : R ⟶ U`, with the over-`T` equations
  `s ≫ fU = fR` and `t ≫ fU = fR`, and hypotheses `Etale s` and `Etale t`.
* The pair map is `j : R ⟶ pullback fU fU`, with its two projection equations
  `j ≫ pullback.fst fU fU = s` and
  `j ≫ pullback.snd fU fU = t`, together with `IsClosedImmersion j`.
* For every test scheme `H` over `T`, `hrel` gives `_root_.Equivalence` on the
  subtype of maps `H ⟶ U` over `T`; related maps are exactly those represented by
  a map `r : H ⟶ R` whose composites with `s` and `t` are the two maps.  This is
  the functor-of-points equivalence-relation clause.
* For the selected `u : U`, `p` is defined as `fU u`.  The conclusion gives
  `T'`, an étale `f' : T' ⟶ T`, and `p' : T'` with `f' p' = p` and
  `IsIso (f'.residueFieldMap p')`.
* `Uo Wo : (pullback fU f').Opens` satisfy `IsCompl Uo Wo`.  The point
  `u' : Uo.toScheme` has base-change projections `u` and `p'`, and the induced
  map `Uo.ι ≫ pullback.snd fU f'` is finite over `T'`.
* `Ro Wro : (pullback fR f').Opens` satisfy `IsCompl Ro Wro`, and
  `Ro.ι ≫ pullback.snd fR f'` is finite over `T'`.  Since an `Opens.toScheme`
  carries its induced open-subsheme structure, these are the required open and
  closed decompositions.
* `s0` and `t0` are the canonical base changes of `s` and `t`.  The iterated
  pullback `Q` is
  `pullback (pullback.snd Uo.ι s0 ≫ t0) Uo.ι`; the map `q : Ro.toScheme ⟶ Q`
  is an isomorphism, its composite to `R0` is `Ro.ι`, and its two endpoint maps
  factor through `Uo`.  The endpoint maps `q ≫ q₁ ≫ p₁` and `q ≫ q₂` are étale.
  Thus `Q` is exactly the restricted relation
  `U' ×_{U×_T T',s} (R×_T T') ×_{t,U×_T T'} U'`.
* The final `∀ H hH, _root_.Equivalence` is the restricted equivalence relation
  on maps to `Uo.toScheme` over `T'`, with endpoints given by those two
  restricted projections.

The statement dependencies used are: `AlgebraicGeometry.Scheme` and
`Scheme.Hom` from Mathlib (`def-pc-scheme`); `Scheme.Hom.IsLocallyQuasiFinite`
from `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`
(`pqf-def-quasifinite`); `AlgebraicGeometry.Etale` from
`Mathlib.AlgebraicGeometry.Morphisms.Etale` (`def-weil-etale-morphism`);
`CategoryTheory.Limits.pullback`, `.fst`, and `.snd` from
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
(`def-pc-fibre-product`); `AlgebraicGeometry.IsClosedImmersion` from
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
(`def-weil-closed-immersion`); `Scheme.residueField` and
`Scheme.Hom.residueFieldMap` from `Mathlib.AlgebraicGeometry.ResidueField`
(`def-weil-residue-field`); `AlgebraicGeometry.IsFinite` from
`Mathlib.AlgebraicGeometry.Morphisms.Finite`
(`def-weil-finite-integral-morphism`); and the induced open subschemes
`Scheme.Opens`/`IsOpenImmersion` from
`Mathlib.AlgebraicGeometry.OpenImmersion` (`def-weil-open-immersion`).

I checked the edge cases used by the source argument: the diagonal relation on
`U = T = Spec(k)`, the total relation on a two-point finite scheme, a point with
non-rational residue field, the empty object scheme (where the point hypothesis
is vacuous), and non-reduced affine bases.  The statement does not require the
chosen finite piece to be relation-invariant; the final relation is its endpoint
restriction, as in the node.  The pullback clauses retain the canonical maps and
the induced scheme structures.

Searches for an existing declaration were run with `msearch.py` on 2026-10-18:

* LeanFinder query “finite clopen étale restricted equivalence relation of affine
  schemes over a locally quasi-finite base” returned only generic étale and étale
  locus declarations (`AlgebraicGeometry.Etale`, `AlgebraicGeometry.IsEtale`,
  and related instances), with no theorem of this shape.
* Loogle query `"IsFinite", "Etale", "Equivalence"` returned zero hits.
* Mathlib grep query `Equivalence.*IsFinite|IsFinite.*Equivalence` under
  `AlgebraicGeometry` returned zero hits.
* `rg` over the project’s `lean/Sheaf` and `lean/WeilConjectures` found no
  declaration of this item; it found only the parent module’s use of the DAG id.

`STATEMENT-DISPUTED:` none.  The declaration compiled cleanly with the required
`scompile.py` wrapper; the only proof placeholder is the theorem’s expected
`sorry`.

## Second reading by NU

The module and node were reread against every clause of the stage-1 statement.
The affine hypotheses, both structure maps, over-base equations, étaleness,
closed pair map, pointwise functor-of-points equivalence relation, residue-field
isomorphism, clopen object and relation decompositions, finiteness over `T'`,
canonical restricted iterated pullback, étaleness of both restricted projections,
and the restricted equivalence relation all appear explicitly.  No source
hypothesis or edge case was dropped, and no auxiliary definition or duplicate
declaration was introduced.

## Maintainer review fix (2026-10-18)

The node's conclusion begins "there exist an affine scheme $T'$", and the parent
`lem-a1-separated-locally-qf-space-representable` uses an *affine* étale
neighbourhood $(T',p')\to(T,p)$. The delivered conclusion omitted this clause.
The fix adds the conjunct `IsAffine T' ∧` in front of `Etale f'`; nothing else is
changed. The fixed file compiles cleanly per file (nt_compile.py, 1.9 s, no error).
