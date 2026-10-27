## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout` states the node in three
named theorems, each with proof `sorry` and a source-based natural-language proof docstring.
There are no new definitions and no statement correction. The accepted thirteen-step
stage-1 split, sources and proof dependencies are preserved.

Hypotheses and clauses, in order:

- Work over a scheme B, in the prescribed universes: `universe u`, `{B : Scheme.{u}}`,
  and `AlgebraicSpace B`. All maps are in the category of spaces over B. The scheme
  clause uses `Over B`; it does not forget the structure maps.
- A thickening T into T+ is rendered by `i : T ⟶ T'`,
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom` and
  `IsHomeomorph (mapPoint i.hom.hom)`. The existing point topology is the final topology
  of etale scheme charts, equivalently the quotient topology of a surjective atlas.
  No finite nilpotence exponent is imposed.
- The affine map T into S is `a : T ⟶ S` with
  `IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom`.
  Mathlib's `IsAffineHom` says that inverse images of affine opens are affine.
- `exists_affineThickeningPushout` gives `∃ P j b, IsPushout a i j b ∧ ...`.
  `IsPushout` is the universal property in the category of algebraic spaces over B:
  maps to every algebraic space Q are exactly compatible pairs, uniquely. The other
  two conjuncts give representable closed immersion and homeomorphism for S into P.
- For schemes, `scheme_affineThickeningPushout` takes T, T+, S in `Over B`, with
  `[IsClosedImmersion i.left]`, `IsHomeomorph i.left.base`, and `[IsAffineHom a.left]`.
  It asserts existence of P, j and b in `Over B`, with both the scheme-level
  `IsPushout a.left i.left j.left b.left` and `IsPushout` of their actual Yoneda
  algebraic-space maps. Thus a scheme pushout is also the space pushout, and uniqueness
  of pushouts identifies any P from the first theorem with this scheme representative.
- Recovery is stated for any supplied base pushout `hp : IsPushout a i j b` and arbitrary
  spaces X and Y with maps `x : X ⟶ S` and `y : Y ⟶ T'`. There is no flatness or local
  finite presentation hypothesis.
- The specified overlap isomorphism is
  `φ : enlargedFibreProduct x a ≅ enlargedFibreProduct y i`.
  `hφ` says its composite with the second sheaf projection is the second projection
  to T. This is precisely an isomorphism over T, rather than an arbitrary isomorphism
  of the underlying spaces.
- The overlap U is the actual sheaf fibre product `enlargedFibreProduct x a`.
  Its map to X is `enlargedFibreProductFst x a`; its map to Y is
  `φ.hom ≫ enlargedFibreProductFst y i`. The existential Z, u, v and p has the
  pushout condition for exactly these maps.
- `IsPullback u x p j` and `IsPullback v y p b` mean the canonical maps
  X into Z times_P S and Y into Z times_P T+ are isomorphisms. Their square equations
  also say that p extends the given maps into P. The pushout equation uses the specified
  φ, so their restrictions over T agree by this φ itself. No arbitrary replacement
  equivalence, arbitrary comparison map, or unspecified choice is substituted.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith` (fppf sheaves and scheme-test
  representability). The full signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
  Their full signatures and docstrings were read; the first supplies the property
  used by the already existing bundled sheaf pullback.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `def-weil-size-convention` is a convention, not a Lean object: the explicit universe
  u and the existing big-site interfaces implement it.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`; their existing definition owners
  `def-trf-scheme-algebraic-space` and `def-sfb-space-sheaf-fibre-product` are added to
  stmt_deps. These definitions retain the actual Yoneda sheaf and sheaf pullback.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `PointRepresentative.map`; its owner `def-a1-space-point-topology` is added.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: the existing `mapPoint`, whose owner
  `def-sfb-proper-curve-moduli` is added. Only the induced point map is used here;
  no curve-family assumption is imposed on the theorem's spaces.

The already stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`,
`Sheaf.AlgebraicGeometry.EtaleRelationQuotient`, and
`Sheaf.AlgebraicGeometry.EtaleAtlasPresentation`. The original algebraic-space and
fibre-product statement dependencies are public imports. The remaining seven proof
nodes currently have no Lean record, Mathlib match or upstream audit declaration:
affine-charts, scheme-colimit-upgrade, scheme-affine-thickening-pushout,
scheme-infinitesimal-etale-patching, space-thickening-etale-scheme-equivalence,
unramified-geometric-equivalence-relation and space-closed-immersion-atlas-locality.
Their arguments are retained in the proof docstrings; there is no missing notion needed
for typing the present statements and no import cycle is introduced.

Edge cases checked: the identity thickening; empty spaces (including empty T and T+);
non-affine S and T+; arbitrary locally nil defining ideals without a global exponent;
nonflat and non-finitely-presented X and Y; an arbitrary, nonidentity gluing isomorphism
over T; and arbitrary base schemes, without separation or finiteness hypotheses.
All are admitted by the signatures. In the identity-thickening case the pushout is S;
in the empty-overlap case it is the disjoint union. No binders use auto-bound implicits:
`set_option autoImplicit false` is enabled.

Source checked: `literature/stacks-project/spaces-pushouts.tex`,
lemma-pushout-along-thickening-schemes (07SY), lemma-pushout-along-thickening (07VX),
and lemma-equivalence-categories-spaces-over-pushout (07W0), including its two atlas
cubes and final canonical comparison assertion. The additional structure-sheaf formula
in 07VX is not a clause of this DAG node and is not silently added.

Searches for an existing statement:

- msearch LeanSearch: "Pushouts of algebraic spaces along thickenings and affine morphisms
  and canonical recovery by base change". Eight hits about ring pushouts and affine
  base change; no algebraic-space pushout statement.
- msearch LeanFinder: "Pushouts of algebraic spaces along thickenings and affine morphisms
  and recovery by base change". Eight hits, mainly Spec of ring pushouts (scheme
  pullbacks), ideal-sheaf gluing and affine-space pullbacks; none is this statement.
- msearch Loogle: `CategoryTheory.IsPushout, AlgebraicGeometry.IsAffineHom`. Zero hits.
- msearch grep: `thickening|Thickening|AlgebraicSpace` in Mathlib/AlgebraicGeometry.
  One documentation hit in Morphisms/FormallyUnramified, not the desired theorem.
- rg of `thickening.*[Pp]ushout|[Pp]ushout.*[Tt]hickening|affineThickeningPushout`
  in project WeilConjectures and Sheaf: only a proof comment in CurveInfinitesimalPushout.
  Search of the exact node id in WeilConjectures and the proposed names in
  dag/lean_names_upstream.json found no existing declaration. The retained sandbox
  draft is not a published duplicate. Existing helper declarations were read and reused.

The initial draft and revised module compile cleanly through scompile.py against the
published live library. No theorem was proved. There is no STATEMENT-DISPUTED issue.
The inherited BLOCKED report was a stage-1 live-wins refusal: brief-stage2 section 0
explicitly permits this handoff, and the live queue lists this item at stage 2 with
no Lean record. This delivery changes no accepted stage-1 proof step.

## Second reading by Q63

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
