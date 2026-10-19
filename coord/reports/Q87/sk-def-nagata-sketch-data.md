## Worker report

Existing declaration binding; no new Lean module, theorem, or definition is needed.
The already landed module `Sheaf.Compactification.BoundaryRefinement` defines precisely
this sketch's three notions. The primary declaration is
`AlgebraicGeometry.Compactification.BoundaryCompactification`; the record also lists
`QuasiCompactObjects`, `boundaryRefinementProperty`, and `DenseBoundaryCompactification`
in the same namespace and module. I read the complete module and its dependency
signatures and docstrings, and the current main-20261015 blueprint unit. The node
copy changes only `lean`; the recorded signature is verbatim from the existing file.

Clause-by-clause correspondence:

- The arbitrary morphism `f : X ⟶ S` is bound with `{X S : Scheme.{u}}` in every
  recorded definition. There are no finiteness, separatedness, Noetherianity,
  nonemptiness, or density assumptions on `f`. The universe `u` is explicitly bound
  by the owning module; objects lie in `Type (u + 1)` as schemes do.
- The factorization is the existing `Compactification f`, with ambient scheme `Z`,
  maps `i : X ⟶ Z`, `g : Z ⟶ S`, and `comm : f = i ≫ g`.
  These are exactly the displayed ambient scheme, `j`, `p`, and factorization equality.
- The open immersion and properness clauses are its fields
  `isOpenImmersion : IsOpenImmersion i` and `isProper : IsProper g`.
- Quasi-compactness is retained by
  `QuasiCompactObjects f = ObjectProperty.FullSubcategory
  (fun c : Compactification f ↦ QuasiCompact c.i)`.
  A `BoundaryCompactification` object wraps exactly such an object via `.obj`;
  wide subcategories add no further object condition. Thus the general upstream
  compactification notion, which omits quasi-compactness, is not incorrectly used
  alone to represent this sketch.
- Density is the predicate `IsSchemeTheoreticallyDominant c.obj.obj.i` defining
  `DenseBoundaryCompactification`. The recorded Mathlib definition says the kernel
  ideal sheaf is zero. For quasi-compact `j` this is exactly injectivity of
  `O_Z → j_* O_X`: Mathlib's `Scheme.Hom.app_injective` proves sectionwise
  injectivity, while `Scheme.Hom.ker_apply` identifies the kernel on each affine
  open with the ring-map kernel, so sectionwise injectivity gives the converse.
  Quasi-compactness is already present, and no reducedness hypothesis is needed.
- For source compactification `c'` and target `c`, a morphism in the wide
  subcategory has underlying upstream refinement `r.hom.hom`. Its ambient map
  `h := r.hom.hom.hom` satisfies `hom_g : h ≫ c.obj.obj.g = c'.obj.obj.g`:
  this is exactly being an `S`-morphism. The same upstream refinement's
  `i_hom : c'.obj.obj.i ≫ h = c.obj.obj.i` is `h j' = j`.
- Its remaining morphism property is `boundaryRefinementProperty f`, namely
  `h ⁻¹ᵁ c.obj.obj.i.opensRange = c'.obj.obj.i.opensRange`.
  This is the full inverse-image condition, not just compatibility on `X`.
  Equality is in `Scheme.Opens`, so both sides denote the open subschemes with
  restricted structure sheaf. The triangle equality gives the specified
  identification of their copies of `X`. These are all the refinement conditions;
  no density is imposed on general objects or morphisms.

Dependency declarations read and used:

- `def-nagata-compactification`: `AlgebraicGeometry.Compactification` in
  `WeilConjectures.Compactification.Defs`, including all six fields. Its
  `blueprint_update` gives the general open-immersion notion; the item's additional
  quasi-compactness is supplied by the already recorded refinement module.
- `def-nagata-dense-compactification`:
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant` in
  `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (kernel zero),
  read together with `Scheme.Hom.app_injective` there and `Scheme.Hom.ker_apply`
  in `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`.
- `det-nagata-definition-refinement`: all four declarations named in this binding,
  from `Sheaf.Compactification.BoundaryRefinement`. Its imports use the upstream
  `AlgebraicGeometry.Compactification.Refinement` (fields `hom`, `i_hom`, `hom_g`)
  in `WeilConjectures.Compactification.Refinement`. I also read Mathlib's
  `ObjectProperty.FullSubcategory` and `WideSubcategory` object and morphism
  structures to check that the wrappers impose exactly the stated properties.

Edge cases checked mathematically: if `f` is proper, the identity open immersion
with proper map `f` is allowed and dense. If `X` is empty, nonempty proper ambient
schemes are allowed as compactifications but fail density; the empty ambient is
allowed and dense. For nonempty proper `X/S`, the fold `X ⊔ X → X`, with the first
component as the source's distinguished open and identity as the target's open,
satisfies both triangles but fails the inverse-image condition; the recorded
boundary predicate correctly excludes it. No assumption of dense compactifications
is silently added. The dense subcategory retains exactly the same refinements.

Searches for reuse (all run for Q87 / sk-def-nagata-sketch-data, with wrapper logs
in `searches.jsonl`):

- LeanFinder: "A compactification of a scheme morphism is a quasi compact open
  immersion followed by a proper morphism; refinements preserve the inverse image
  of the open and dense means injective on the structure sheaf". Eight results,
  including `Scheme.Hom.liftCoborder`, `Scheme.Hom.toImage_app_injective`, and
  `IsImmersion.isPullback_toImage_liftCoborder`; no combined definition.
- Loogle: `AlgebraicGeometry.Compactification, AlgebraicGeometry.IsSchemeTheoreticallyDominant`.
  Zero hits; the service reports unknown identifier `AlgebraicGeometry.Compactification`.
  This is a limitation of its Mathlib index; the upstream declaration was read directly.
- LeanSearch: "Compactification of a morphism of schemes with quasi-compact open
  immersion, proper map and refinements preserving the distinguished open".
  Eight constituent-property hits (including `QuasiCompact` and proper restriction),
  none defines the combined data.
- Wrapper grep: `Compactification|compactification|boundaryRefinementProperty`,
  Mathlib subdirectory `AlgebraicGeometry`: zero hits.
- Direct `rg` in upstream `WeilConjectures/Compactification` for compactification,
  density and refinements found `Defs.lean`, `Refinement.lean`, and `Dense.lean`.
  General upstream refinements omit the inverse-image condition.
- Direct `rg` in upstream `WeilConjectures` for `boundaryRefinementProperty`,
  `BoundaryCompactification`, `DenseBoundaryCompactification`, and the item id:
  no hits. The required `grep -rn` for the item id also returned no hits.
- Direct `rg` in project `lean/Sheaf` for the same boundary declarations found
  `Sheaf.Compactification.BoundaryRefinement`, exactly the dependency module
  already recorded in the DAG. Its declarations match all three clauses, so this
  delivery uses `existing: true`, branch `newtargets-dag`, and writes no module.
  `dag/lean_names_upstream.json` confirms general upstream compactification names.

No node fault, statement correction, new node, dependency repair, or
STATEMENT-DISPUTED finding. No repair handoff exists for this item.

Validation: `deliver2.py --no-push` checks every recorded existing declaration by
an import and `#check @...` probe through `scompile.py`, then runs server preflight.
The second reading is reserved for the independently started second reader.

## Second reading by Q87

I read the item node, its blueprint source place, the three dependency nodes, and
`Sheaf.Compactification.BoundaryRefinement.lean` independently. The source section
introduces the following data and clauses, with the corresponding Lean rendering.

1. An arbitrary morphism `f : X ⟶ S` of schemes is represented by the explicit
   binders `{X S : Scheme.{u}}` and `(f : X ⟶ S)` in
   `AlgebraicGeometry.Compactification.QuasiCompactObjects`,
   `boundaryRefinementProperty`, `BoundaryCompactification`, and
   `DenseBoundaryCompactification`. Verdict: exact; no separatedness, Noetherianity,
   finiteness, nonemptiness, density, or characteristic hypothesis is added.
2. A compactification introduces an ambient scheme `Z`, an open immersion
   `j : X ⟶ Z`, a proper map `p : Z ⟶ S`, and the factorization equality. These are
   the fields `Z`, `i`, `g`, and `comm` of the recorded
   `AlgebraicGeometry.Compactification` dependency. Verdict: exact up to the
   harmless names `i = j` and `g = p`; the equality has the same orientation
   `f = i ≫ g`.
3. The requirement that `j` be a quasi-compact open immersion is rendered by
   `QuasiCompactObjects f := ObjectProperty.FullSubcategory
   (fun c : Compactification f ↦ QuasiCompact c.i)`, while the upstream structure
   supplies `IsOpenImmersion c.i`. Verdict: exact; the ambient module does not
   accidentally use the weaker upstream compactification category by itself.
4. Properness of `p` is the upstream field `Compactification.isProper g`, registered
   as an instance. Verdict: exact, with no stronger properness condition.
5. Scheme-theoretic density is rendered by the object predicate
   `IsSchemeTheoreticallyDominant c.obj.obj.i` in
   `DenseBoundaryCompactification`. The Mathlib dependency defines this as zero
   kernel ideal sheaf; for the already quasi-compact open immersion its
   `Scheme.Hom.app_injective` characterization is precisely injectivity of
   `\mathcal O_Z → j_* \mathcal O_X`. Verdict: exact; no reducedness assumption is
   introduced.
6. A refinement introduces two compactifications `c'` and `c` and an ambient map
   `h : c'.obj.Z ⟶ c.obj.Z`. The upstream `Refinement` morphism fields `hom`,
   `i_hom`, and `hom_g` render respectively `h`, `h ≫ p = p'`, and
   `j' ≫ h = j`. Verdict: exact, including the order of source and target.
7. The additional inverse-image clause is rendered by
   `boundaryRefinementProperty f`, namely
   `r.hom.hom ⁻¹ᵁ c.obj.i.opensRange = c'.obj.i.opensRange` in `Scheme.Opens`.
   `BoundaryCompactification` is the corresponding `WideSubcategory`, and
   `DenseBoundaryCompactification` is its full subcategory on dense objects.
   Verdict: exact; equality is of open subschemes with restricted structure sheaves,
   and no extra density condition is imposed on arbitrary refinements.

The source place is the sketch node itself (order 2), and its refinement details
are supplied by `det-nagata-definition-refinement`; I checked that dependency's
three numbered conditions and its identity/composition paragraph against the
module. The empty-index issue is irrelevant because no index type or limit is
introduced. The zero and empty-scheme cases remain admitted: the identity
compactification of a proper map is allowed, and for empty `X` an empty ambient
scheme is dense while a nonempty ambient scheme is not. A fold ambient map
`X ⊔ X ⟶ X` can satisfy the two triangles but fails the inverse-image equality,
confirming that the third refinement clause is substantive. Universes are
polymorphic in `u`, with schemes in `Scheme.{u}` and resulting categories in
`Type (u + 1)`; no case is excluded.

For the one-definition-per-notion check I reran semantic LeanFinder and LeanSearch
queries, a Loogle query, and `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`.
The searches found only constituent morphism predicates and the upstream general
`Compactification`/`Refinement`; they found no combined boundary-preserving
definition. The project search found the already landed
`Sheaf.Compactification.BoundaryRefinement` module, and the dependency declarations
were opened and matched clause by clause. No repair note exists, no new node or
dependency module is needed, and no citer audit or statement correction is
triggered.

No mismatch was found, so no file or statement was changed. The sandbox node's
`lean` record binds the existing declaration
`AlgebraicGeometry.Compactification.BoundaryCompactification` (and the companion
declarations in the same module) with `existing: true`, branch `newtargets-dag`,
and a signature verbatim from the source module.
