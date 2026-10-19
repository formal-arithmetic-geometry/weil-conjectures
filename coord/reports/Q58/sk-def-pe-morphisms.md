## Worker report

This delivery binds `sk-def-pe-morphisms` to existing declarations, with primary declaration
`AlgebraicGeometry.proAffineEtale` in
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`. No module, new definition,
new theorem, dependency repair, statement correction, or proof is supplied. Only the item's
`lean` record changes. The existing upstream module publicly exposes all the declarations
listed in the record. Its current source was also read through `scompile.py --source`.
There is no repair note for this item.

Source checked: the current main-20261015 blueprint's
`sec-proetale-coefficients/sk-def-pe-morphisms/_section.md`, the node's reviewed
stage-1 statement, and the complete signatures and docstrings of the recorded dependencies.
The blueprint's comparison assertions are already separated into
`det-pe-morphisms-etale-comparison`; this definition binding introduces none of them anew.

Clause-by-clause correspondence:

1. Commutative rings and a ring map are the binders `{R S : Type u} [CommRing R]
   `[CommRing S] (f : R →+* S)` of `RingHom.IndEtale`. Its real defining data use
   `f.toAlgebra` and `Algebra.IndEtale R S`, precisely the convention of dependency
   `def-weil-pbc-ind-etale-algebra`. The latter's `exists_colimitPresentation` quantifies
   over `(ι : Type u)`, `SmallCategory ι`, `IsFiltered ι`, and
   `P : ColimitPresentation ι (CommAlgCat.of R S)`, and requires
   `∀ i, Algebra.Etale R (P.diag.obj i)`. `Algebra.Etale.finitePresentation` supplies
   finite presentation, so it is already part of the existing stage condition.
   `ColimitPresentation` contains the diagram, natural coprojections `P.ι`, and
   `P.isColimit`, not merely an isomorphism to an unspecified algebra.
2. The affine spectrum and the induced map are dependency `AlgebraicGeometry.Spec`
   and `Spec.map (CommRingCat.ofHom f)`. The already recorded comparison
   `AlgebraicGeometry.proAffineEtale_Spec_iff` has full signature
   `{R S : CommRingCat.{u}} {f : R ⟶ S} :
   proAffineEtale (Spec.map f) ↔ f.hom.IndEtale`.
   Thus the existing pro-affine-etale predicate specializes exactly to the ring
   definition for an affine base. Its existing proof sends a filtered presentation
   `(D,t,s,hs)` to `D.op ⋙ Scheme.Spec`, with structure maps `Spec.map (t.app _)`
   and projections `Spec.map (s.app _)`; preservation by `Scheme.Spec` gives its
   limit cone. These are the specified canonical maps from the chosen presentation,
   not arbitrary morphisms or chosen nonempty data.
3. For arbitrary `X : Scheme.{u}` and `u : U ⟶ X`, the primary declaration is
   `MorphismProperty.pro.{u} (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)`.
   Expanding the existing `MorphismProperty.pro` gives a small category
   `(J : Type u)`, `[SmallCategory J]`, `[IsCofiltered J]`, a diagram `D : J ⥤ Scheme`,
   natural structure maps `t : D ⟶ (Functor.const J).obj X`, natural projections
   `s : (Functor.const J).obj U ⟶ D`, `IsLimit (Cone.mk _ s)`, and for each `j`
   both the stage property and `s.app j ≫ t.app j = u`.
   The stage property says exactly `Etale (t.app j)` and `IsAffine (D.obj j)`:
   `ofObjectProperty` tests the source and the right-hand `⊤` imposes no condition
   on `X`. Naturality of `t` makes all transitions `X`-morphisms; naturality of `s`
   is projection compatibility. `IsLimit.lift`, `.fac`, and `.uniq` are existence,
   factorization, and uniqueness for every compatible family. An ambient-scheme
   limit here is equivalent to the stated limit over `X`: cofilteredness implies
   nonemptiness and connectedness, and `Over.forget` preserves connected limits.
   Directly, the ambient lift is over `X` by factoring through any stage; conversely
   a cone of schemes acquires its unique map to `X` from the common stage composites.
   Thus no extra universal-property condition has been imposed.
4. Nonempty filtered and cofiltered indexing is already in Mathlib's `IsFiltered`
   and `IsCofiltered`, whose structures both include `Nonempty`. In particular this
   is not `IsFilteredOrEmpty` or `IsCofilteredOrEmpty`. `SmallCategory J` matches the
   small-index convention of dependency `def-weil-pbc-category-colimit`.
5. For a scheme morphism, the dependency's exact Mathlib declaration
   `AlgebraicGeometry.WeaklyEtale` has fields `flat : Flat f` and
   `flat_diagonal : Flat (pullback.diagonal f)`. The diagonal has the specified
   fibre-product target. No finite-presentation or affineness hypothesis is added.
6. For rings, the dependency's exact `Algebra.WeaklyEtale R S` has fields
   `flat : Module.Flat R S` and
   `flat_lmul' : (Algebra.TensorProduct.lmul' R (S := S)).Flat`.
   This is the specified multiplication `S ⊗[R] S → S`. The existing
   `RingHom.WeaklyEtale f` uses exactly the algebra structure `f.toAlgebra`.
   `weaklyEtale_SpecMap_algebraMap_iff` is the already recorded spectrum comparison
   in the dependency's separately imported weakly-etale comparison module; the
   definition clauses here require only the two predicates, already exposed by the
   primary module.

Dependency declarations read and reused:

- `def-weil-pbc-ind-etale-algebra`:
  `Sheaf.RingTheory.IndPrincipalZariski` publicly imports the existing
  `Algebra.IndEtale` from `WeilConjectures.RingTheory.ProEtale.IndEtale`,
  `proAffineEtale_Spec_iff` from the primary module, and
  `Algebra.WeaklyEtale` / `weaklyEtale_SpecMap_algebraMap_iff` through
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`.
  The dependency's primary `Algebra.IsIndPrincipalZariski` concerns its additional
  ind-Zariski clause; that notion is not required by this item.
- `def-weil-pbc-category-colimit`:
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, `colimit.desc`, and `CategoryTheory.IsFiltered`.
  The actual presentation interface is Mathlib's `ColimitPresentation`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`, with exactly its affine-locally-etale signature.
- `def-weil-weakly-etale-morphism`: its `mathlib_match` is
  `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`,
  `AlgebraicGeometry.WeaklyEtale`; the absence of a separate `lean` record is permitted.

Edge cases checked before binding: empty indexing categories are excluded by both
filteredness structures. Singleton presentations include every absolutely affine etale
scheme over any base; the base need not be affine, quasi-compact, or nonempty. Empty
schemes and the zero ring are permitted (there is no `Nontrivial` or scheme-nonemptiness
binder). Affineness is on each scheme, not on its structural morphism: an identity on a
nonaffine scheme does not qualify merely because identity morphisms are affine. The
ring and scheme universe convention is the same as the recorded ind-etale dependency:
small index objects and morphisms are in the carrier universe `u`, rather than an
independent smaller universe. No characteristic, finiteness of the index, surjectivity,
or separatedness is imposed. No statement dispute was found.

Searches performed (outputs also retained in `searches.jsonl`):

- `msearch.py ... leanfinder`, query
  "An affine pro-etale scheme over X is a cofiltered inverse limit of affine schemes
  etale over X": eight results, mostly `Scheme.Etale`, its site, and affine-limit
  lemmas; no exact new definition in Mathlib.
- `msearch.py ... loogle`, query
  `Algebra.IndEtale, AlgebraicGeometry.proAffineEtale, Algebra.WeaklyEtale`:
  zero results, unknown identifier `Algebra.IndEtale` (a project declaration).
- `msearch.py ... grep`, query `IndEtale|proAffineEtale|WeaklyEtale`:
  fifteen results; exact weakly-etale definitions in Mathlib, no Mathlib ind-etale or
  pro-affine-etale definition.
- `msearch.py ... leansearch`, query
  "pro etale affine morphism inverse limit affine etale schemes": eight results
  including `Scheme.isAffine_of_isLimit`, affine-scheme limits, and `Scheme.Etale`;
  no exact whole bundle.
- `rg` across the read-only upstream source, the side `lean/WeilConjectures`, and
  `lean/Sheaf` for the named definitions and comparisons found the exact existing
  declarations above. Searching for the blueprint id in upstream gave no hit;
  the upstream-name table includes `AlgebraicGeometry.WeaklyEtale`, but did not
  identify the ind-etale/pro-affine-etale definitions. Incomplete metadata does
  not override the actual source matches. No private copy is needed.

Validation: an initial scratch probe found that the optional spectrum comparison
`weaklyEtale_SpecMap_algebraMap_iff` is not re-exported by the primary module. It was
removed from this item's auxiliary declaration list (the actual scheme and ring
weakly-etale definitions are both exposed). No definition clause was changed.
The corrected seven-declaration scratch probe passed `scompile.py` cleanly in both
the sandbox and library contexts (2.5 s and 3.4 s); it introduced no declaration.
The prescribed delivery dry run checks every listed existing declaration
with an imported `#check` probe through `scompile.py`, and checks the node/report shape.
The independent second reader will append their reading and perform delivery.

## Second reading by Q58

Step 1 list and verdicts, matching the node statement clause by clause:

1. For commutative rings `R`, `B` and a ring map `R →+* B`, the ind-étale
   notion is rendered by `RingHom.IndEtale`, whose definition installs
   `f.toAlgebra` and uses `Algebra.IndEtale`. Its `exists_colimitPresentation`
   field gives a small `ι : Type u`, `SmallCategory ι`, `IsFiltered ι` (hence
   nonempty), a `ColimitPresentation`, and étale stages. `Algebra.Etale`
   supplies finite presentation. Verdict: exact, with no extra ring or
   finiteness hypothesis.
2. For an affine base, `AlgebraicGeometry.proAffineEtale_Spec_iff` identifies
   `proAffineEtale (Spec.map f)` with `f.hom.IndEtale`; the canonical maps are
   the `ColimitPresentation.ι` maps and the induced `Spec.map` maps. Verdict:
   exact affine ind-étale/pro-affine correspondence.
3. For arbitrary `X` and `u : U ⟶ X`, `AlgebraicGeometry.proAffineEtale` is
   `MorphismProperty.pro (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)`. Its
   `D`, natural `t` and `s`, `IsLimit (Cone.mk _ s)`, and factorization clauses
   give precisely a small nonempty cofiltered inverse-limit presentation by
   absolutely affine schemes étale over `X`. Naturality makes transition maps
   `X`-morphisms; cofilteredness makes the ambient cone universal property
   equivalent to the stated over-`X` one. Verdict: exact; the `⊤` factor adds
   no condition on `X`.
4. `SmallCategory` and `IsCofiltered` are the required small, nonempty
   indexing conventions; no empty indexing category is admitted. Verdict:
   exact.
5. `AlgebraicGeometry.WeaklyEtale` has exactly the fields `Flat u` and
   `Flat (pullback.diagonal u)`, with the diagonal landing in the fibre
   product. Verdict: exact.
6. `Algebra.WeaklyEtale` has `Module.Flat R B` and flatness of
   `Algebra.TensorProduct.lmul' R`, the multiplication map
   `B ⊗[R] B → B`; `RingHom.WeaklyEtale` installs the ring-map algebra
   structure. Verdict: exact.

Edge cases: filtered/cofiltered indexing excludes the empty category but allows
singletons; zero rings, zero/empty schemes, and empty affine stages remain allowed;
there is no `Nontrivial`, characteristic, separatedness, surjectivity, finite-index,
or quasi-compactness assumption. The scheme and ring universes are consistently `u`
with no hidden equality restriction, and `n = 0` is irrelevant to this definition.

Searches were rechecked with `msearch.py` (LeanFinder, Loogle and grep queries for
ind-étale/pro-affine/weakly-étale), `rg` over Mathlib and both project source trees,
and direct reading of `ProAffineEtale.lean`, `IndEtale.lean`, Mathlib's
`WeaklyEtale.lean`, and the Stacks source for Tags 092B, 094P and 097Z. Mathlib
provides the weakly-étale declarations but no combined ind-étale/pro-affine
definition; the project declarations are therefore the exact existing match.

No mismatch was found. No file or statement was changed; the node's `lean` record
already names the exact existing declarations. The scratch `#check` probe was
compiled with `scompile.py`; no warnings other than permitted existing declarations
occurred, and no variable or universe was left implicit.
