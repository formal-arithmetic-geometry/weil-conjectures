## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleIntegralModelsAfterShrinking` states
`AlgebraicGeometry.exists_finite_etale_integral_models_after_shrinking`, with one `sorry`
and no new definitions. The node statement is unchanged. The theorem docstring includes
all seven steps of the node's proof and the cited intermediate results.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| An integral scheme C | `(C : Scheme.{u}) [IsIntegral C]` |
| C is Noetherian in the finite affine cover sense | `[IsNoetherian C]`; Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with a finite affine cover by Noetherian coordinate rings. |
| A nonempty affine open U in C | `(U : C.Opens) (hU : IsAffineOpen U) (hUne : Nonempty U)`; its inclusion is `U.ι`. |
| A finite etale surjection T to U | `{T : Scheme.{u}} (g : T ⟶ U.toScheme) [IsFinite g] [Etale g] [Surjective g]`. |
| A nonempty affine open W in U | `∃ W : U.toScheme.Opens, IsAffineOpen W ∧ Nonempty W ∧ ...`; its map to C is `W.ι ≫ U.ι`. |
| A nonempty finite index set A | `∃ (A : Type u) (_ : Finite A) (_ : Nonempty A) ...`. |
| Integral schemes Y_a | `(Y : A → Scheme.{u})` and `∀ a, IsIntegral (Y a) ∧ ...`. |
| Finite maps q_a to C | `(q : ∀ a : A, Y a ⟶ C)` and the conjunct `IsFinite (q a)`. |
| V_a is exactly Y_a times_C W | Every occurrence is the chosen Mathlib object `pullback (q a) (W.ι ≫ U.ι)`. No arbitrary replacement open is quantified. |
| Each V_a is nonempty | `Nonempty ↥(pullback (q a) (W.ι ≫ U.ι))`. |
| Each V_a is an open subscheme of Y_a | `IsOpenImmersion (pullback.fst (q a) (W.ι ≫ U.ι))`, for the canonical first projection. |
| An isomorphism T times_U W to the disjoint union of the V_a | `∃ e : pullback g W.ι ≅ ∐ (fun a : A ↦ pullback (q a) (W.ι ≫ U.ι)), ...`. Mathlib's scheme coproduct is the disjoint union. |
| The isomorphism is over W | `e.hom ≫ Sigma.desc (fun a : A ↦ pullback.snd (q a) (W.ι ≫ U.ι)) = pullback.snd g W.ι`. |
| The whole inverse image of W is identified, rather than just a smaller open | The target of `e` is the coproduct of the full chosen pullbacks. Inverse image commutes with a disjoint union, so this is precisely the whole restriction of the family of Y_a, with its canonical structure map to W. |

The isomorphism is expressed as a scheme isomorphism with its compatibility equation;
this is exactly an isomorphism of W-schemes, without introducing additional Over data.
No density, normality, separatedness of C, choice of generic point, or constant-degree
hypothesis is imposed on the inputs. No integrality of V_a beyond what follows from its
being a nonempty open in Y_a is added to the conclusion.

Statement dependency declarations read and used:

- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral` in
  `Mathlib.AlgebraicGeometry.Properties`; its nonemptiness and domain sections definition.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`. The scheme hypothesis is the standard equivalent
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`, whose finite
  affine-cover equivalence was read at lines 280--315.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`; `U.ι` and `W.ι` are the canonical open inclusions.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`. Affineness is expressed using Mathlib's
  `IsAffineOpen` in `Mathlib.AlgebraicGeometry.AffineScheme`, which means that the open
  subscheme is affine; `IsAffine` means its canonical map to the spectrum of its global
  sections is an isomorphism.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, affine with finite section ring maps.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; the recorded name is used, not its deprecated
  `IsEtale` alias.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, surjectivity on points.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst` and
  `pullback.snd` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, using
  the scheme pullback instance from `Mathlib.AlgebraicGeometry.Pullbacks`.

The public imports supply these notions and Mathlib's scheme coproduct. Non-public
imports retain the modules for the node's recorded proof dependencies, including the
finite-factorization theorem, generic-fibre density, reduced scheme-theoretic image,
reduced induced closed subscheme and etale fibre theorem. The current upstream etale
fibre module was read with `scompile.py --source
WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`, since that path is
absent from the older local source tree. Mathlib proof leaves are imported from their
recorded source modules.

Source check: read `literature/stacks-project/more-morphisms.tex` at
`lemma-quasi-finite-separated-pass-through-finite` (Tag 05K0, lines 12456ff), which gives
the quasi-compact open immersion followed by a finite map. The additional integral
component refinement and the seven-step reduced-closure proof are explicitly in the
item's source/proof record; the delivered docstring retains that refinement rather than
mistaking the plain Zariski Main Theorem for the full item.

Edge cases checked:

- Empty C is excluded by `IsIntegral C`, exactly as in the node's definition.
- Empty U is explicitly excluded. Consequently an empty T cannot satisfy the surjectivity
  hypothesis. Empty W and empty A are explicitly excluded in the conclusion.
- A one-component cover, including the identity cover, is permitted by the finite nonempty
  index type; there is no lower bound of two components and no demand that W be proper.
- No normality is assumed, so intersecting closures before shrinking remain permitted.
- All characteristics are allowed. There is no coefficient field or prime in the signature.
- `A : Type u` is adequate for any finite family, by relabeling, and scheme pullbacks and
  coproducts remain in `Scheme.{u}`. The universe u is explicitly declared and all binders
  are explicit; auto-implicits are disabled.

Searches before writing (all through the prescribed wrapper unless a path is specified):

1. LeanFinder query: `A finite etale cover of a nonempty affine open of an integral
   Noetherian scheme admits integral finite models whose disjoint union restricts to the
   entire cover after shrinking`. Eight hits: affine transition limit auxiliary covers,
   `Scheme.AffineCover`, `Scheme.Hom.normalizationOpenCover`, the affine characterization
   of finite morphisms and affine open covers. None states the finite integral family
   with this cartesian coproduct conclusion.
2. Loogle query: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsIntegral`. Zero hits.
3. Grep query: `integral.*model|finite.*etale.*shrink|finiteEtaleIntegral` under
   `AlgebraicGeometry`. Six hits, all integral Weierstrass models or the integral model of
   affine space; none matches.
4. LeanSearch query: `Finite etale covers extend after shrinking to a disjoint union of
   integral schemes finite over a Noetherian integral base`. Eight hits: etale algebras
   over fields, scheme etale definitions and topology, finite morphisms, etale base change
   and the Noetherian finite-affine-cover criterion. None is the item.
5. `rg` of the upstream `WeilConjectures`, project `lean/Sheaf` and
   `dag/lean_names_upstream.json` for the item id and the candidate declaration names found
   no declaration; the one project hit is the consumer's natural-language proof citing
   this node. Broader concept searches found unrelated coefficient integral models and
   projective-space integral models.
6. Direct source inspection confirmed the listed Mathlib dependency signatures and
   docstrings, the Noetherian equivalence, pullback API and scheme coproduct instance.

No new nodes, dependency repairs, statement corrections or disputed statements were needed.

## Second reading by N6

Author self-check with the node and finished module open; independent mathematical review
is the maintainer's subsequent review, as specified in this worker's brief. The input
hypotheses match: integral Noetherian C, nonempty affine U and finite etale surjective g.
The output matches: nonempty affine W, finite nonempty A, integral Y_a, finite q_a, and
nonempty open canonical pullbacks. The isomorphism's displayed compatibility equation
was checked against the canonical W-projections on both sides. In particular its target
contains every point of each pullback, so it does not weaken the full inverse-image
clause. No mismatch or node change was found.

## Validation

`scompile.py N6 lem-per-finite-etale-integral-models-after-shrinking` compiled both the
sandbox form (2.3 seconds) and the library form (2.5 seconds) cleanly, with no warnings.
An initial elaboration ambiguity was repaired by writing `Nonempty ↥(pullback ...)`,
explicitly coercing the scheme to its underlying type. The signature in the node was
regenerated verbatim from the final module. The prescribed `deliver2.py --no-push`
dry-run passed preflight and compilation (`OK`, temporary commit `1637174c96`), with
exactly the report, item node and one Lean module staged.
