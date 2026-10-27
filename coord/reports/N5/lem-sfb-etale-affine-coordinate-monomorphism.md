## Worker report

The module `Sheaf.AlgebraicGeometry.Sites.EtaleAffineCoordinateMonomorphism`
states `AlgebraicGeometry.exists_etaleAffineCoordinateMonomorphism`. Its sole proof
is `sorry`. No construction or auxiliary theorem is postponed and no definition
is introduced. The statement is unchanged. The additional landed statement
dependency `def-sc-etale-additive-structure-restriction` records the existing
additive structure sheaf used to express its underlying set sheaf (per brief §5,
STMT_DEPS MAY GAIN LANDED NODES).

Clause-by-clause translation:

- The size convention is explicit `universe u`, `Scheme.{u}`, and sheaf values in
  `Type (u + 1)`. The small étale site has object universe `u+1` and morphism
  universe `u`. ULift raises the sections and relative Hom sets without changing
  them. No equation between the site's two universes is imposed.
- Any scheme S is `(S : Scheme.{u})`. An étale morphism V→S is `(V : S.Etale)`;
  its structure morphism is `V.hom`. Affineness is exactly `[IsAffine V.left]`.
- O_S is the underlying set sheaf
  `(sheafForget (D := AddCommGrpCat.{u+1}) S.smallEtaleTopology).obj
  S.etaleAdditiveSheaf`. Its sections are `ULift Γ(T.left, ⊤)` and its restriction
  is pullback of functions. This uses an existing definition, not a second copy
  of the structure sheaf. The same convention gives O_X.
- `∃ (n : ℕ) (c : Fin n → Γ(V.left, ⊤))` gives the finite tuple, including n=0,
  before the quantifier `∀ (X : Scheme.{u}) (a : X ⟶ S)`. Thus the coordinates
  are uniform for every base change, not chosen depending on a.
- h_V is `S.smallEtaleTopology.uliftYoneda.{u+1}.obj V`. The small-site
  representable sheaf theorem and subcanonical instance justify this bundled
  sheaf. Its sections are ULift of relative morphisms.
- `a.Etale.obj V` is V×_S X, with structure map the second projection to X.
  It is canonically X×_S V by factor exchange. Consequently `pullback.fst
  V.hom a` is pr_V; using this orientation changes no morphism or formula.
- Each `X.smallEtaleTopology.uliftYonedaEquiv.{u+1} (X := a.Etale.obj V)`
  inverse applied to `⟨(pullback.fst V.hom a).appTop (c j)⟩` is exactly the map
  sending u to `(u.left ≫ pr_V).appTop (c j)`. This is the defining evaluation
  formula for the Yoneda inverse, together with functoriality of appTop.
  `Pi.lift` assembles the j coordinates into O_X^n. The first `Mono` conjunct
  is monicity of precisely this map e_a, not an arbitrary injection.
- Direct image is explicitly `a.Etale.sheafPushforwardContinuous ...`, whose
  value at T is evaluation at T×_S X. Inverse image is the recorded
  `Scheme.etaleSetPullback a`. `sheafAdjunctionContinuous` is its specified
  adjunction, not a free left adjoint or a chosen equivalence.
- The first conjunct specifies β on every T and s as
  `(β.hom.app (op T) ⟨s⟩).down = (pullback.fst T.hom a).appTop s`.
  Hence β is uniquely the pullback-of-functions map in the node. Its inverse
  image adjunct is `(sheafAdjunctionContinuous ...).homEquiv _ _ |>.symm β`
  (written with parentheses in the module), exactly a^♯ on underlying sets.
  Compatibility of the ring and set adjunctions is the recorded algebraic
  structures dependency. Nothing replaces a^♯ by an unconstrained scalar map.
- The existential `ι` is an isomorphism from inverse-image h_V to the sheaf
  represented by `a.Etale.obj V`. Its second conjunct quantifies over every
  `T : S.Etale` and `z : T ⟶ V`, prescribing its adjunct to be `a.Etale.map z`.
  This is id_X×_S z in the chosen fibre-product orientation. Yoneda and
  adjunction determine ι uniquely, excluding any twist by an automorphism.
- The displayed equality is `ι.hom ≫ e_a = L.map e ≫ piComparison L ... ≫
  Limits.Pi.map (fun _ : Fin n ↦ a^♯)`. Here e is the Yoneda tuple of the
  original c_j on S. At a=id it is the node's e under the canonical identity
  base-change identification. `piComparison` is the projection-defined
  identification L(O_S^n)→(L O_S)^n; it is an isomorphism by the dependency's
  finite-limit preservation. The last `Mono` conjunct states the final
  monomorphism assertion for exactly that composite.
- There are no quasi-compactness, quasi-separatedness or separation binders on
  S or X, and no affineness or étaleness assumption on a.

Dependency declarations read and used:

- `def-weil-size-convention`: its convention-only record, implemented by universes.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and
  `Scheme.Etale` (defined in `Morphisms.Etale`).
- `WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`:
  `smallEtaleRepresentablePresheaf_isSheaf`, on Hom over the base.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the library's base-change functor packages these.
- `WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable`:
  `nonempty_inverseImage_representable_iso`. Its interface allows any specified
  adjunction; this item further specifies the adjunct normalization explicitly.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`:
  `etaleInverseImageAlgebraicStructures`, finite limits and the ring/set adjunct
  agreement; its public `EtaleSheaves` interface gives `Scheme.etaleSetPullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- Added existing dependency
  `WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf`:
  `Scheme.etaleAdditiveSheaf`, its coefficient composite, and
  `Scheme.etaleAdditiveSheafToLowerStar`. This is the existing structure function
  sheaf, with the exact Γ and ULift convention needed here.

All stated proof dependency modules are imported without `public`:
QuasiAffine (`instIsQuasiAffineOfIsAffine`), UnramifiedMorphism
(`IsUnramified`), FiniteType (`LocallyOfFiniteType`), upstream AffineSpace
(`exists_immersion_affineSpace_of_quasiAffine`), Mathlib AffineSpace
(`AffineSpace`), GammaSpecAdjunction (`ΓSpec.adjunction`), ClosedImmersion
(`IsClosedImmersion`), ZariskisMainTheorem
(`IsClosedImmersion.iff_isProper_and_mono`), OpenImmersion
(`IsOpenImmersion.mono`), and Yoneda (`yonedaEquiv`, `Coyoneda.fullyFaithful`).
Statement dependency imports already cover the other proof dependencies.

Edge cases checked: n=0 is an actual Fin 0 product, so Pi.lift and piComparison
have their empty-product meanings; no positivity premise occurs. Empty V admits
a monomorphism to the terminal sheaf. Empty T has its unique relative map and
unique functions. Empty S forces V and every X→S empty, without invalid binders.
For a=id_S the comparison is normalized to the identity base change, not an
arbitrary automorphism. S and X may be non-quasi-compact and non-quasi-separated.
A concrete sanity check is an open affine V→S, where n=0 can distinguish all
relative maps since h_V is subterminal. No connectedness or field hypothesis is
used. There is no statement dispute or source correction.

Sources read: Stacks `morphisms.tex`, lemma-quasi-affine-finite-type-over-S
(Tag 04II), and `etale-cohomology.tex`, lemma-2-morphism (Tag 04IJ), especially
the coordinate injection and displayed inverse-image composite. The five-step
DAG proof is carried in the theorem docstring, with its dependencies.

Searches made through the prescribed msearch.py wrapper:

1. LeanFinder: “An affine etale scheme has finitely many global functions defining
   a monomorphism of representable etale sheaves after arbitrary base change”.
   Eight hits: IsEtale/formally-unramified APIs, Scheme.Etale and category
   instances, Algebra.Etale.finitePresentation; no coordinate sheaf theorem.
2. Loogle: `"Mono", "smallEtaleTopology"`: OK, zero hits.
3. Mathlib grep in AlgebraicGeometry:
   `coordinate.*[Mm]ono|[Mm]ono.*coordinate`: OK, zero hits.
4. LeanSearch: “Finite global coordinate functions of an affine etale scheme give
   a monomorphism of representable sheaves into a finite power of the structure
   sheaf compatible with arbitrary base change”. Eight hits: AffineSpace.coord,
   map_appTop_coord, homOverEquiv, homOverEquiv_apply, isoOfIsAffine;
   IsFinite.recOn, IsFinite.toIsAffineHom, AffineScheme.Γ. None contains the
   theorem or its normalized sheaf compatibility.
5. `rg -n 'coordinate.*[Mm]ono|[Mm]ono.*coordinate|lem-sfb-etale-affine-coordinate-monomorphism'`
   in both `lean/WeilConjectures` and `lean/Sheaf`: unrelated coordinate,
   polynomial, stalk and support results, no same statement. Searching the node
   id alone in upstream Lean finds no declaration.
6. Targeted searches for `structureSheaf`, `etaleSetPullback`, `gaSheaf`,
   `etaleAdditiveSheaf` found the already defined structure functions. Reading
   its DAG record led to using `etaleAdditiveSheaf` rather than defining a sheaf.
   No new node or dependency repair is needed.

Validation: scompile.py compiled the module independently in sandbox and library
modes in about 3 seconds each, with no errors or warnings. No global or local
library build was run.

## Second reading by N5

I reread the node and module after compilation (the dispatcher explicitly forbids
starting another agent). The maintainer's independent delivery review remains
separate. I checked every binder and conjunct against the node: étale plus affine
V; fixed n and c before arbitrary a; h_V and h_base-change as site representables;
Γ sections with only a universe lift; actual coordinate map, its Mono instance;
β's projection pullback formula; ι's adjunct on every relative map; the product
comparison and a^♯ adjunct in both the equality and final Mono. All match.

Two elaboration issues found in the first read were repaired: named arguments
belong to `uliftYonedaEquiv` before taking `.symm`, and categorical product maps
are `Limits.Pi.map` rather than the unrelated function `Pi.map`. Explicit
representing objects and ULift universe parameters also remove inference
ambiguity without adding mathematical hypotheses. A subsequent reread replaced
the equivalent upstream `gaSheaf` spelling with the landed node's recorded
`etaleAdditiveSheaf`, and added that node to stmt_deps. No statement correction,
private definition, hidden let/show binder, unbound universe, or missing
normalization remains. The factor exchange is documented and all projection
formulas consistently use V×_S X. The only sorry is the assigned theorem.
