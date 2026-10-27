## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceLqfAtlasRefinement` states
`AlgebraicGeometry.AlgebraicSpace.space_lqf_atlas_refinement` with one `sorry`.
No definitions, dependency repairs, or statement corrections are needed.
The five proof steps of the node are included in the theorem docstring.

Hypothesis and conclusion correspondence (all notation in this table is explanatory,
not new Lean notation):

| Node clause | Lean rendering |
| --- | --- |
| Schemes S and T,B,U over S | `{S : Scheme.{u}} (T B U : Over S)` |
| S-morphism b:B→T | `(b : B ⟶ T)` in `Over S` |
| Algebraic space X over S | `(X : AlgebraicSpace S)` |
| f:X→h_T and a:h_U→X | Natural transformations `f : X.obj.obj ⟶ yoneda.obj T` and `a : yoneda.obj U ⟶ X.obj.obj` |
| a representable surjective étale | `ha : IsEtale a`, `hs : IsSurjective a`; both predicates already include scheme-test representability |
| h_Z(H)=Mor_S(H,Z) | `yoneda.obj Z` on `(Over S)ᵒᵖ` |
| Induced U→T | `yoneda.preimage (a ≫ f)`; this is the actual Yoneda inverse, with no arbitrary map supplied |
| X_B=X×h_T h_B | `Limits.pullback f (yoneda.map b)` on underlying presheaves |
| U_B=U×T B | `Limits.pullback (yoneda.preimage (a ≫ f)) b` in `Over S`; its underlying scheme is the scheme fibre product, via the forgetful functor's preservation of pullbacks |
| Canonical h_UB≅h_U×X X_B, compatible with both projections | First existential isomorphism `e`; its first equation gives `yoneda.map (pullback.fst ...)`, and its second gives `aB`. These determine the isomorphism by the pullback universal property |
| Induced a_B | Existential `aB`, determined by the preceding two projection equations. The next equation identifies its B-projection with `yoneda.map (pullback.snd ...)` |
| a_B representable surjective étale | `IsEtale aB ∧ IsSurjective aB` |
| Every scheme D→X_B | `∀ (D : Over S) (t : yoneda.obj D ⟶ Limits.pullback f (yoneda.map b))` |
| Canonical test isomorphism over h_D | `∃ e : pullback t aB ≅ pullback (t ≫ pullback.fst ...) a`; its first projection equation is the identity over h_D. The second equation gives the projection to h_U, so it specifies the canonical isomorphism |
| Every representable étale chart v:h_V→X_B | `∀ (V : Over S) (v : yoneda.obj V ⟶ ...), IsEtale v → ...` |
| Common fibre product represented by W | `∃ (W : Over S) (p : W ⟶ V) (q : W ⟶ U_B), IsPullback (yoneda.map p) (yoneda.map q) v aB` |
| p surjective étale and q étale | `Etale p.left ∧ Surjective p.left ∧ Etale q.left` |
| Composites to B agree | `p ≫ yoneda.preimage (v ≫ pullback.snd ...) = q ≫ pullback.snd ...`; equality is in `Over S`, equivalently equality of the scheme maps |
| If U_B→B is locally quasi-finite, so are W→B and V→B | Final implication uses `Scheme.Hom.IsLocallyQuasiFinite` for the second scheme projection, for `q.left ≫ (pullback.snd ...).left`, and for the Yoneda inverse of `v` followed by the B-projection |
| No separatedness or quasi-compactness assumptions | None appears in the binders or conclusion requirements |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsSurjective`. The latter two use the
  existing `IsRepresentableWith` scheme-test squares; no replacement predicates are defined.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. This statement dependency is publicly imported.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal property. Used both for schemes over S and for presheaves.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, meaning quasi-finite at
  every point with the local finite-type requirement of Stacks 01TD.
- Proof imports: `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` supplies the
  recorded `schemeSpace`; `Mathlib.CategoryTheory.Yoneda` supplies
  `CategoryTheory.Yoneda.fullyFaithful` and `yoneda.preimage`;
  `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource` supplies
  `Scheme.Hom.isLocallyQuasiFinite_etale_source`.

The sheaf pullback is stated on underlying presheaves, as in the existing scheme-test
interfaces. Sheaf limits are computed on underlying presheaves, so this does not
change the object or omit sheaf compatibility. `IsPullback` is exactly representability
of the common fibre product with the specified projections, rather than an
unconstrained choice of a representing scheme or of an isomorphism.

Sources read: `spaces-morphisms.tex`, labels
`lemma-base-change-quasi-finite-locus` (0ABM), `lemma-local-source-target` (03MJ),
`definition-locally-quasi-finite` (03XJ); `descent.tex`, label
`lemma-locally-quasi-finite-etale-local-source` (03X4). The pulled-back-atlas
section formulas and common-refinement argument agree with these source passages.

Edge cases checked: empty B gives empty pullback schemes and the empty common
refinement; an empty chart V is permitted; an empty atlas forces X to be empty
by its surjectivity hypothesis. No nonemptiness, finiteness of the atlas,
quasi-compactness, Noetherian condition, or separated diagonal is assumed.
All schemes use the same arbitrary universe u, exactly as the recorded
algebraic-space framework; no further universe equality is imposed. The chart v
is not required to be surjective. The conclusion needs surjectivity only for p,
not q. The implication uses the Stacks predicate, not Mathlib's weaker
`LocallyQuasiFinite` predicate.

Searches actually run with `msearch.py Q105 lem-a1-space-lqf-atlas-refinement`:

- LeanFinder: `Pullback of an etale surjective algebraic space atlas and common scheme refinement detecting locally quasi finite morphisms`.
  Eight hits, including scheme-level `instLocallyQuasiFiniteSndScheme`,
  `instLocallyQuasiFiniteFstScheme` and étale site declarations; no match for this
  atlas, its canonical test isomorphisms, and common refinement.
- Loogle: `"pullback", "yoneda"`. Five hits, including
  `PullbackCone.isLimitCoyonedaEquiv` and generic square/sheaf lemmas; no exact match.
- Grep through Mathlib AlgebraicGeometry: `atlas|AlgebraicSpace`. Zero hits.
- LeanSearch: `An algebraic space atlas pulled back along a scheme morphism has a common etale refinement with every chart`.
  Eight hits, including `Scheme.Cover.pullbackCoverOver'`,
  `Scheme.Cover.pullbackCoverOver`, and generic sheaf refinement lemmas; none states
  the algebraic-space result.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  atlas/refinement and atlas/pullback patterns: no existing statement.
  More general searches for `schemeSheaf`, Yoneda pullbacks, and
  `IsPullback ... yoneda` located the reused framework and generic interfaces,
  not another statement of this node. `dag/lean_names_upstream.json` was checked
  for `atlas_refinement`, `atlasRefinement`, and `space_lqf_atlas` with no match.

Validation: prescribed `scompile.py` passed both sandbox and library-mode checks
without errors or warnings. The module has a single theorem with proof `by sorry`,
explicit universe and binders, and no local notation, private data, or proof construction.

## Second reading by Q105

Author's second reading, as required by the dispatcher's no-other-agents instruction;
this is not an independent review. I reopened the node and checked its full statement
against the theorem. The table above accounts for every hypothesis and clause.
In particular, neither chart surjectivity nor finite type is silently added, the
source finite-type condition is retained through the recorded predicate, the two
canonical identifications retain their projections, and the refinement's B-map
is the actual induced map, not an arbitrary morphism. The scheme-test isomorphism
also records its projection to h_U. `Over S` records all base compatibility without
additional hypotheses. No statement mismatch was found. On the import check, the
fibre-product dependency was changed to a public import because it is a statement
dependency, and Scheme and Etale are also imported publicly. No new nodes or
dependency modules are introduced. Maintainer independent review remains pending.
