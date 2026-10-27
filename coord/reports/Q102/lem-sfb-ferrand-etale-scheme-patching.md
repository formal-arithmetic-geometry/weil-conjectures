## Worker report

The module `Sheaf.AlgebraicGeometry.FerrandEtaleSchemePatching` states
`AlgebraicGeometry.ferrand_etale_scheme_patching`, with `sorry` as its entire proof.
There are no definitions, additional postponed theorems, new nodes, dependency repairs,
or statement corrections. Only the assigned node's `lean` field changes.

Sources read: `literature/stacks-project/more-morphisms.tex`, Situation 0ECI
(`situation-pushout-along-closed-immersion-and-integral`), Tags 0ECK
(`lemma-pushout-functor`) and 0ECL (`lemma-pushout-functor-equivalence-flat`).
The accepted node's ten-step proof extends the flat affine counit to arbitrary etale
sources by Zariski gluing. The declaration docstring carries all ten steps and the
corresponding node names, including the restricted affine-neighbourhood check in step 5.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Scheme S and S-schemes Z, X, T | `(S : Scheme.{u}) (Z X T P : Over S)` |
| S-morphisms i and j | `(i : Z ⟶ X) (j : Z ⟶ T)`; `.left` is the scheme morphism |
| Closed immersion i | `[IsClosedImmersion i.left]` |
| Integral j | `[IsIntegralHom j.left]`, with no finiteness hypothesis |
| Each fibre image lies in one affine open of X | `h : ∀ t : T.left, ∃ A : X.left.Opens, IsAffineOpen A ∧ ∀ z : Z.left, j.left z = t → i.left z ∈ A` |
| Given scheme pushout P, with induced map to S | `P : Over S`, S-morphisms `a : X ⟶ P`, `b : T ⟶ P`, and `hs : IsPushout i.left j.left a.left b.left` in schemes |
| Schemes X', T' and maps u, v | `(X' T' : Scheme.{u}) (u : X' ⟶ X.left) (v : T' ⟶ T.left)` |
| Separated etale u, v | `[IsSeparated u] [Etale u] [IsSeparated v] [Etale v]` |
| Isomorphism of restrictions over Z | `φ : pullback u i.left ≅ pullback v j.left`, with `hφ : φ.hom ≫ pullback.snd v j.left = pullback.snd u i.left` |
| Z' and its specified component maps | `pullback u i.left`, `pullback.fst u i.left` and `φ.hom ≫ pullback.fst v j.left`; no substitute overlap is chosen |
| Existence of P' and its induced r | `∃ (P' : Scheme.{u}) (a' : X' ⟶ P') (b' : T' ⟶ P') (r : P' ⟶ P.left), ...` |
| P' is the scheme pushout | `IsPushout (pullback.fst u i.left) (φ.hom ≫ pullback.fst v j.left) a' b'` |
| Induced map is separated and etale | `IsSeparated r ∧ Etale r` |
| Canonical X' comparison is an isomorphism | `IsPullback a' u r a.left` |
| Canonical T' comparison is an isomorphism | `IsPullback b' v r b.left` |
| Canonical Z' comparison is an isomorphism | `IsPullback (pullback.fst u i.left ≫ a') (pullback.snd u i.left) r (i.left ≫ a.left)` |
| Comparisons respect phi and all projections | These are cartesian squares of the actual specified maps, not arbitrary isomorphisms. The primed pushout uses the supplied `φ.hom`; its commutativity, `hφ`, and the three squares give the compatibility with both overlap projections. |
| Arbitrary etale q : U → P | `∀ (U : Scheme.{u}) (q : U ⟶ P.left), Etale q → ...` |
| Inverse-image square is a scheme pushout | `IsPushout` of the two maps induced by `(Over.pullback q).map` on `i` and `j`, with cocone maps `pullback.snd a.left q` and `pullback.snd b.left q` to U |
| No separatedness or quasi-compactness for q | Neither occurs in the quantified converse |
| No additional global hypotheses; empty schemes allowed | No Noetherian, finite-type, surjectivity, nilpotence, nonempty, or quasi-compact assumption occurs |

`IsPullback` is an exact encoding of each specified canonical comparison being an
isomorphism: it says the cone with those two projections is limiting. Its unique
comparison to Mathlib's chosen pullback is therefore invertible; conversely an
invertible comparison gives this limit property. It also records both projection
equations, which a bare existence of an isomorphism would lose. The first two squares
make r the induced map; the primed universal property ensures uniqueness. Composing
r with `P.hom` gives precisely the induced S-structure on P', so the existential
scheme presentation loses no S-scheme data.

Mathlib's `Over.pullback q` presents inverse images as Z ×_P U, X ×_P U, T ×_P U.
Their canonical symmetry isomorphisms identify this square with the node's written
order U ×_P Z, U ×_P X, U ×_P T. The maps are the same canonical inverse-image maps
under these symmetries. No alternative construction or choice of a map is introduced.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- The finite/integral dependency records `Mathlib.AlgebraicGeometry.Morphisms.Finite`
  with both finite and integral declarations. Its integral clause is
  `AlgebraicGeometry.IsIntegralHom` in `Mathlib.AlgebraicGeometry.Morphisms.Integral`;
  both modules are imported, and only integrality is assumed.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`; the specialization to a span is Mathlib's `IsPushout`
  from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- Separatedness was defined inline by the node; the existing exact Mathlib predicate
  `AlgebraicGeometry.IsSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.Separated`
  is literally the condition that `pullback.diagonal` is a closed immersion.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `CategoryTheory.Over.pullback`,
  its object/map formulas, and `Over.homMk` express the canonical inverse-image square.

All recorded proof-dependency modules are imported without `public`, except those
already imported publicly for the statement. In particular the delivery uses
`exists_ferrand_scheme_pushout` from `Sheaf.AlgebraicGeometry.FerrandSchemePushout`
as its future existence input, not as a replacement for the patching assertion.
The two proof nodes `lem-sfb-fibre-product-algebra-etale` and
`lem-sfb-patched-module-base-change` currently have neither a Lean record nor a
Mathlib match and supply no notion needed to type this statement; there is no
module to import for them. Their mathematical steps remain in the proof docstring.

Edge cases checked before drafting:

- Z empty: the overlap remains the empty pullback and the assertion becomes the
  expected componentwise gluing on a disjoint union; nothing requires nonemptiness.
- X, T, X', T', P or U empty: all quantifiers and categorical universal properties
  still type. Empty fibres in `h` impose only containment of the empty image.
- Infinite integral fibres: `h` concerns the entire fibre, not a finite selection;
  integrality is not replaced by finiteness.
- Identity component maps with the canonical overlap: the theorem includes the
  original square and gives its identity patching.
- Non-separated etale q, and an infinite disjoint union of etale sources: no
  separatedness or quasi-compactness binder excludes these cases in the converse.
- Non-separated component schemes over S: only the relative maps u and v are
  separated; no absolute separatedness or separatedness over S is assumed.
- No surjectivity of i, j, u, v or q is assumed.
- The single explicitly declared universe `u` sizes all schemes in the same category;
  there is no independent smaller test-object universe making a universal property
  vacuous, and every variable is explicitly bound.

Searches actually run:

- `msearch.py ... leanfinder "Etale schemes glue across a pushout along a closed
  immersion and an integral morphism, and arbitrary etale base change preserves
  the scheme pushout"`: 8 hits, including the etale category's pullbacks, etale
  stability, and `Scheme.GlueData.gluedScheme`; none states Ferrand patching.
- `msearch.py ... loogle "AlgebraicGeometry.Etale, CategoryTheory.IsPushout"`:
  successful search, 0 hits.
- `msearch.py ... grep "Ferrand|pinching|[Ee]tale.*[Pp]ushout|[Pp]ushout.*[Ee]tale"
  AlgebraicGeometry`: successful search, 0 hits.
- `msearch.py ... leansearch "Separated etale schemes patch over a Ferrand pushout
  of schemes along a closed immersion and an integral map"`: 8 hits concerning
  separatedness and integral-map permanence, no patching result.
- `rg -n` over `lean/Sheaf` and `lean/WeilConjectures` for Ferrand, pinching,
  the prospective declaration name, and etale/pushout combinations: Ferrand scheme
  existence, invertible-module pinching, ring-algebra etale pushouts and open gluing
  exist; none states this node. In particular
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Gluing` was opened: its
  `exists_pullback_inl_iso` assumes both gluing maps are open immersions and finite
  etale input, unlike the present closed-integral setting.
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent` was also opened:
  `CommRingCat.exists_isPushout_of_etale` is descent along a filtered ring colimit,
  not the scheme pushout here.
- `grep -rn "lem-sfb-ferrand-etale-scheme-patching" lean/WeilConjectures`:
  no match. The exact-name `rg` search likewise found no existing declaration.

No disputed statement or node fault was found.

Validation: the prescribed `scompile.py` compiled the module separately in module
mode as both sandbox and final library module, with no warnings or errors.
The final library compilation took 6.4 seconds.

## Second reading by Q102

A separate reading pass by the same worker compared the node and completed signature;
this is not represented as an independent agent review. The assignment reserves the
independent review for the maintainer and explicitly forbids starting other agents.

This pass checked the affine-neighbourhood quantifiers, closed versus integral
hypotheses, the four relative etale/separated instances, and the equation making phi
over Z. It checked that P is a pushout in schemes, not merely in the over category,
and that the three cartesian squares refer to the exact specified overlap maps.
It checked the unrestricted etale quantifier in the converse, the orientation of
both inverse-image arrows, and the cocone projections to U. The initial compiler
pass detected that those last two projections were incorrectly written as `fst`;
they were changed to `snd`. No statement correction or further mismatch was found.
