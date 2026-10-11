## Worker report

The module states the rational-point unramified criterion using the local rings at `f x` and
`x`, their explicit `k`-algebra structures, and the stalk algebra homomorphism `φ`. The
hypothesis `hφ` identifies `φ` with the stalk map induced by `f`; `hmax` records that the
maximal ideal maps into the maximal ideal. The conclusion is the equivalence between
`AlgebraicGeometry.FormallyUnramified f` and surjectivity of Mathlib's
`Ideal.mapCotangent` on `m/m²`. The theorem proof is `sorry`, as required at stage 2.

The node's finite-type hypothesis is `[LocallyOfFiniteType f]`; the source's points are
represented by `x` and `f x`, with local rings given by scheme stalks. The cotangent map is
`Ideal.mapCotangent (maximalIdeal ...) (maximalIdeal ...) φ hmax`, and its surjectivity is
`Function.Surjective`. The extra explicit algebra and ideal-map hypotheses are necessary to
make the induced map well-typed in Lean. `FormallyUnramified` is the Mathlib morphism notion.

Dependencies used: `def-weil-pbc-scheme-conventions` (scheme and locally finite type
conventions), `def-sc-scheme-tangent-space` (point/tangent-space context), and
`def-weil-unramified-morphism` (unramified morphism notion). Mathlib declarations used are
`AlgebraicGeometry.FormallyUnramified`, `Scheme.Hom.stalkMap`, `IsLocalRing.maximalIdeal`,
and `Ideal.mapCotangent`.

Edge cases checked include zero cotangent spaces (the surjectivity predicate remains valid),
empty schemes (the theorem is point-indexed, so has no cases without `x`), and arbitrary
universe `u`. The Mathlib map allows zero ideals and zero modules.

Searches: LeanFinder query “unramified at a rational point if and only if cotangent map is
surjective” returned only ring-level `FormallyUnramified` declarations and no scheme-point
criterion; Loogle query “Ideal.Cotangent.map, AlgebraicGeometry.FormallyUnramified” returned
no hits; grep query `cotangent.*unramified|unramified.*cotangent` over Mathlib returned no
scheme-level match. Project grep found no existing declaration for this node.

STATEMENT-DISPUTED: the imported prose does not introduce explicit local-ring algebra
structures or an induced cotangent-map definition, so these binders are required for a
well-typed Lean rendering; `hφ` and `hmax` express the intended induced map and its
locality.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The module and node were checked together: every
Lean binder corresponds to the morphism, finite-type condition, point, stalk local rings,
k-algebra structures, induced stalk map, and cotangent-surjectivity clause described above.

## Second reading by E1

The node introduces a field `k`, schemes `X,Y` over `Spec k`, a morphism `f` over
`Spec k` locally of finite type, a point `x` and `y=f(x)`, rationality of both points,
and the equivalence between unramifiedness at `x` and surjectivity of the cotangent map.
The Lean renders these as `[Field k]`, `[X.Over (Spec (.of k))]`, `[Y.Over
(Spec (.of k))]`, `[f.IsOver (Spec (.of k))]`, `[LocallyOfFiniteType f]`, `x`, and residue
field ring isomorphisms `iY` and `iX`; `φ` with `hφ` identifies the stalk map and `hmax`
provides the ideal-map premise. The conclusion is exactly `FormallyUnramified f ↔
Function.Surjective (Ideal.mapCotangent ...)`.

The first reading found a mismatch: arbitrary stalk `Algebra k` instances did not express
that the schemes are over `k` or that the points are `k`-rational. I repaired the Lean and
node by adding the over-base instances, the over-base condition on `f`, and explicit residue
field isomorphisms. The node's statement was corrected accordingly; its sole citer
`lem-sc-finite-flat-unramified-tangent-criterion` still holds.

Edge cases checked: arbitrary universe `u`; zero cotangent spaces (surjectivity remains
well-defined); empty schemes (the point binder makes the assertion vacuous when no point
exists); and no restriction on characteristic.

Searches repeated: LeanFinder for “unramified morphism rational point cotangent map
surjective”, Loogle for `FormallyUnramified CotangentSpace`, and grep over Mathlib and
`WeilConjectures/` for `cotangent.*unramified|unramified.*cotangent`; no existing
scheme-point criterion was found.

## Statement corrected

Old statement: Let f:X\to Y be a morphism locally of finite type between schemes over a field k [def-weil-pbc-scheme-conventions], and let x\in X and y=f(x) be closed points with residue fields equal to k. Then f is unramified at x [def-weil-unramified-morphism] if and only if the induced k-linear map on cotangent spaces [def-sc-scheme-tangent-space] \mathfrak m_y/\mathfrak m_y^2\to\mathfrak m_x/\mathfrak m_x^2 is surjective.

The old Lean omitted the over-k structure and encoded rationality only by arbitrary stalk
Algebra instances, so it did not match the source. Following `varieties.tex`,
lemma-injective-tangent-spaces-unramified, the corrected statement adds schemes over
`Spec k`, an over-k morphism, and explicit residue-field isomorphisms. The citer
`lem-sc-finite-flat-unramified-tangent-criterion` holds under the corrected hypotheses.

## Stage-2 review by R-ruc0954 (FIX, statement correction reverted)

The delivered Lean and its statement correction were both wrong, and the second reading did not catch it:
- Conclusion: `FormallyUnramified f` is a global property of f, not "unramified at x". Now
  `∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (U.ι ≫ f))`,
  the recorded Mathlib match of def-weil-unramified-morphism applied on an open neighbourhood (as in the ÉTALE AT A POINT form).
- Rationality: abstract ring isomorphisms `κ(x) ≃+* k` are not k-rationality (H7: the corrected prose "residue fields isomorphic to k"
  makes the lemma false: k = Q(t_1,t_2,...), f = A^1_k → Spec k, x the generic point, κ(x) = k(s) ≅ k, m_x = 0 so the cotangent
  map is surjective, but Ω is nonzero at x). Restored the base statement (`--revert-statement`) and used the landed M1 form
  (`Function.Bijective (pX.residueFieldMap x).hom`, explicit `pX pY hf`, closed-point hypotheses as in cee2b9ba5).
- Arbitrary `[Algebra k (stalk)]` instances with a free `φ` and `hφ`/`hmax` are dropped: the cotangent map is
  `Ideal.mapCotangent … (f.stalkMap x).hom.toIntAlgHom …`, verbatim the landed M1 cotangent map.
