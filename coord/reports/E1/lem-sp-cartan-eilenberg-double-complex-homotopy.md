## Worker report

Item: `lem-sp-cartan-eilenberg-double-complex-homotopy`.
Module: `Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy`.
Declaration: `CategoryTheory.cartanEilenberg_doubleComplex_homotopy`.
The single theorem has proof `by sorry`; there are no new definitions, auxiliary
lemmas, or changes to the mathematical node. The module compiled cleanly on the
server (1.5 seconds, no warnings).

Sources read: [Stacks Tag 015I](https://stacks.math.columbia.edu/tag/015I), especially
the alternating short exact sequences and their compatible resolutions, and
[Stacks Tag 015K](https://stacks.math.columbia.edu/tag/015K), functoriality of the
associated spectral sequences. These were opened online because the remote
read-only checkout does not contain `literature/stacks-project/derived.tex`.
The node's finer homotopy construction and four proof steps are reproduced in
the declaration docstring, including the references to the horizontal-lift and
vertical-nullhomotopy children. The theorem states the imported node, without
claiming that Stacks explicitly states this finer decomposition.

Every hypothesis and conclusion clause is rendered as follows:

- Abelian category: `(C : Type u) [Category.{v} C] [Abelian C]`, with both
  universes explicitly bound. There is no added enough-injectives assumption:
  the target resolutions are supplied rather than constructed.
- Cochain complexes: `(K L : CochainComplex C ℤ)`.
- Double complexes: `(I J : HomologicalComplex₂ C (ComplexShape.up ℤ)
  (ComplexShape.up ℕ))`. This is precisely the project's landed Cartan–Eilenberg
  convention. `hI` and `hJ` give `IsZero (I.X p)` / `IsZero (J.X p)` for `p < 0`.
  The natural vertical index is the nonnegative restriction; `E` is Mathlib's
  extension-by-zero functor applied horizontally, and `I'`, `J'` are its
  integer/integer bicomplexes. Negative vertical degrees are consequently zero.
- Augmentations: `eI`, `eJ` are ONE bicomplex morphism each from
  `((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K`
  and its counterpart for `L`. Their component at vertical degree zero is the
  augmentation in the node. Being bicomplex maps enforces all compatibility.
- Horizontal cycles, boundaries, cohomology: `I.cycles p`,
  `image (I.d (p - 1) p)`, `I.homology p`, and the counterparts for `J`,
  all formed in the abelian category of vertical complexes. Evaluation at
  `q` gives the node's horizontal cycle/boundary/cohomology objects.
- Exact augmented source B/Z/H resolutions: `hIres` is the conjunction of
  `QuasiIso (HomologicalComplex.cyclesMap eI p)`,
  `QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p)
  (eI.comm (p - 1) p)))`, and
  `QuasiIso (HomologicalComplex.homologyMap eI p)` for EVERY integer `p`.
  These are the actual augmentation-induced maps, not independently chosen
  quasi-isomorphisms. The exact single₀ functor identifies their domains with
  the single-degree complexes of Z/B/H of K. The natural vertical indexing
  and quasi-isomorphisms express exact augmented resolutions.
- The exact sequences involving those resolutions are the canonical short
  exact sequences `0 → Z^p → I^p → B^(p+1) → 0` and
  `0 → B^p → Z^p → H^p → 0`, automatic for a cochain complex in an abelian
  category. Here that category is the category of vertical complexes, which
  is abelian and computes these sequences degreewise. Their augmentation
  compatibility is automatic from `eI`, `eJ`. Thus this clause requires no
  additional independent hypothesis or private sequence definition. Column
  exactness also follows from the cycle/boundary resolution conditions and
  these sequences; it has not been postulated as extra input.
- Injective augmented target B/Z/H resolutions: `hJres` uses the same three
  quasi-isomorphism maps of `eJ`; `hJinj` supplies injectivity of EVERY term
  of the cycle, boundary and cohomology complexes. These are precisely the
  quasi-isomorphism and term-injectivity fields of `InjectiveResolution`,
  also used by the landed existence theorem. Target column injectivity
  follows by splitting the cycle/boundary short exact sequence, rather than
  requiring an additional hypothesis.
- Double-complex morphism: `(δ : I ⟶ J)`.
- Base complex map and homotopy components: `(w : K ⟶ L)` and
  `(s : ∀ p : ℤ, K.X p ⟶ L.X (p - 1))`.
- Equation `w = d_L s + s d_K`: `hs` is
  `w.f p = s p ≫ L.d (p - 1) p + K.d p (p + 1) ≫ s (p + 1) ≫
  eqToHom (congrArg L.X (Int.add_sub_cancel p 1))`.
  The final equality transport merely identifies `(p+1)-1` with `p`.
  Category-theoretic composition is written in traversal order, so the first
  summand is the node's `d_L s`, and the second is `s d_K`.
- Compatibility `δ ε_I = ε_J w`: `hδ` equates
  `(eI.f p).f 0 ≫ (δ.f p).f 0` with `w.f p ≫ (eJ.f p).f 0`.
- Existence of components: `s1` has source `(I'.X p).X q` and target
  `(J'.X (p-1)).X q`; `s2` has that source and target `(J'.X p).X (q-1)`.
  Both are quantified over ALL integer `p,q`, using the canonical extension.
- Zero outside the first quadrant: `s1 p q = 0` if `p ≤ 0 ∨ q < 0`,
  and `s2 p q = 0` if `p < 0 ∨ q ≤ 0`. These include the cases where either
  source or target is outside the quadrant; in particular the vertical
  component in degree zero vanishes. The apparently stronger `p = 0` clause
  for s1 is automatic since its target column is zero.
- Prescribed degree-zero lift: the next conjunct states the node's
  `s1 ε_I = ε_J s`, using `(I.X p).extendXIso ... rfl` and the counterpart
  for `J.X (p-1)` to identify vertical degree zero before and after extension.
- Total homotopy identity: `H : Homotopy
  (HomologicalComplex₂.total.map (E.map δ) (ComplexShape.up ℤ)) 0`.
  Mathlib's `Homotopy.comm` is EXACTLY `d H + H d = δ`, while its `zero`
  field makes `H` degree minus one.
- The same H is the signed sum of the components: for every `p+q=n`, the
  explicit inclusion equation states `ιTotal(p,q,n) ≫ H.hom n (n-1)` equals
  `s1 p q ≫ ιTotalOrZero(p-1,q,n-1)` plus `p.negOnePow` times
  `s2 p q ≫ ιTotalOrZero(p,q-1,n-1)`. `Int.negOnePow` is the unit `(-1)^p`
  used by Mathlib's integer total-shape signs; the horizontal sign is +1.
  This equation identifies the components with the actual total homotopy,
  rather than merely asserting an unrelated total null-homotopy.
- Filtration shift: for EVERY integer `q,n`, the final existential gives a
  map from `(I'.secondFiltration n).step q` to
  `(J'.secondFiltration (n-1)).step (q-1)`, whose composite with the latter
  subobject arrow equals the former subobject arrow followed by
  `H.hom n (n-1)`. This is precisely the stated inclusion in an abelian
  category, using the dependency's actual decreasing vertical filtration.
- Existence of the total complexes is included as existential witnesses
  `tI`, `tJ` to `HasTotal`, inside the conclusion. Thus no diagonal coproduct
  or arbitrary-coproduct assumption is added: first-quadrant finiteness in an
  abelian category supplies them. `letI` merely exposes those witnesses to
  Mathlib's total-complex operations.

Dependency declarations read and used:

- `def-sp-abelian`: `Mathlib.CategoryTheory.Abelian.Basic`,
  `CategoryTheory.Abelian` (its full class and docstring read).
- `def-sp-double-complex-total`:
  `Sheaf.CategoryTheory.DoubleComplexTotal`,
  `HomologicalComplex₂.secondFiltration`, alongside recorded Mathlib
  `HomologicalComplex₂`, `total`, `ιTotal`, `ιTotalOrZero` and the total signs.
- `def-sp-filtration`: `Sheaf.CategoryTheory.Filtration`,
  `CategoryTheory.DecreasingFiltration`, `step` and the subobject-factorization
  convention of `FilteredObject.Hom`.
- `def-sp-injective-resolutions`:
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`,
  `CategoryTheory.InjectiveResolution`, with its exact defining fields read;
  `CategoryTheory.Injective` from its Basic module, factors field read.
- `lem-sp-cartan-eilenberg-exists`:
  `Sheaf.CategoryTheory.CartanEilenbergExists`,
  `CategoryTheory.exists_cartanEilenberg_resolution`. Its full signature and
  docstring were read, and its bicomplex, augmentation and induced-map
  conventions are reused. Its existence conclusion is not required as a new
  hypothesis since this theorem is about supplied resolutions.
- Technical Mathlib operations read:
  `ComplexShape.embeddingUpNat`, `ComplexShape.Embedding.extendFunctor`,
  `HomologicalComplex.extendXIso`, `HomologicalComplex₂.total.map`,
  `Homotopy`, `HomologicalComplex.cyclesMap`, `homologyMap`.

Edge cases checked before writing:

- Zero complexes / zero category: all morphisms and components vanish, the
  total homotopy identity and every filtration factorization hold.
- Horizontal degree zero: s1 lands in zero column -1; the augmented equation
  is consistent. The given exact augmented B/Z/H rows force the negative
  base terms to vanish (cycle and boundary exact sequences), although this
  is not imposed as a separate assumption on K or L.
- Vertical degree zero: s2 lands in the extension's zero degree -1; its
  required vanishing is explicit. No natural truncated subtraction is used.
- Negative total degree: every diagonal summand is zero. The empty finite
  sums are zero, and the homotopy/filtration assertions still quantify here.
- Arbitrary negative filtration index: the second-filtration formula includes
  the entire nonnegative diagonal, while its negative-index contributions
  vanish; no positive-index-only filtration assertion is substituted.
- Universes and category: general abelian categories, arbitrary object and
  morphism universes, no modules-over-a-ring specialization, no additional
  global enough-injectives or infinite-coproduct assumptions.

Searches (actual outputs also in sandbox `searches.jsonl`):

- LeanFinder via msearch: `Cartan Eilenberg comparison maps horizontal vertical
  homotopy total complex` returned eight bifunctor homotopy declarations,
  including `HomologicalComplex.mapBifunctorMapHomotopy.comm₁_aux` and
  `mapBifunctorMapHomotopy₂`. None is a Cartan–Eilenberg comparison theorem.
- Loogle via msearch: `Homotopy, HomologicalComplex₂` returned one bifunctor
  homotopy auxiliary declaration; no matching statement.
- LeanSearch via msearch: `Cartan Eilenberg homotopy components` was unavailable
  (`Internal Server Error`); the other services and source searches were used.
- Mathlib grep via msearch: `cartan|Cartan|Homotopy` in `Algebra/Homology`
  returned ordinary homotopy-category declarations; narrower
  `Cartan.Eilenberg|cartanEilenberg|doubleComplex.*homotopy` returned zero hits.
- `rg 'cartan|Cartan'` in source `WeilConjectures` found an unrelated Cartan
  Lie-algebra criterion and the Grothendieck spectral-sequence description,
  not this statement. `rg` for the exact item id there returned zero hits.
- `rg 'cartan|Cartan'` in project `lean/Sheaf` found the existing resolution
  existence/properties and left-exact cohomology modules, not this homotopy.
- The proposed declaration name was searched in `dag/lean_names_upstream.json`;
  no name clash found. Extension and homotopy operations were found in Mathlib
  and reused; no duplicate notion was defined.

No node fault, statement correction, or STATEMENT-DISPUTED issue was found.

## Second reading by E1

I independently compared the node with `CategoryTheory.cartanEilenberg_doubleComplex_homotopy`.
The objects and hypotheses match item by item: the abelian category and universes are
`(C : Type u) [Category.{v} C] [Abelian C]`; `K,L` are cochain complexes; `I,J` are
the stated integer-by-natural Cartan--Eilenberg bicomplexes with negative-horizontal
vanishing (`hI`, `hJ`); `eI,eJ` are bicomplex augmentations from `single₀`; `hIres` and
`hJres` are the three augmentation-induced cycle, image-boundary, and homology
`QuasiIso` conditions; and `hJinj` gives injectivity termwise for the three target rows.
The map data `δ,w,s`, the null-homotopy equation `hs`, and augmentation compatibility
`hδ` occur in the same order and with the same quantifiers as the node.

The conclusion introduces the extension-by-zero integer bicomplexes and existential
`HasTotal` instances, then `s1 : I'^{p,q} ⟶ J'^{p-1,q}` and
`s2 : I'^{p,q} ⟶ J'^{p,q-1}`. Their stated vanishing regions, the degree-zero
augmentation lift, the total `Homotopy` witness, its explicit signed summand equation,
and the decreasing second-filtration factorization all render the corresponding
clauses of the node. The `p ≤ 0` and `q ≤ 0` boundary clauses are forced by the
negative target columns and correctly include the boundary of the first quadrant.

Edge cases checked: zero complexes and zero categories; horizontal or vertical degree
zero; negative horizontal, vertical, and total degrees; empty diagonal sums; arbitrary
filtration indices; and the unrestricted category and universes. No extra enough-
injectives, Noetherian, characteristic, ring, or finiteness assumptions occur.

Searches were repeated with `rg` over `lean/Sheaf`, the slopmaster2 source and Mathlib,
plus LeanFinder/Loogle queries for Cartan--Eilenberg homotopies and total complexes.
Only generic `Homotopy` and bicomplex operations were found; no existing declaration
states this theorem. The module compiled cleanly with `scompile.py`. I found no
mismatch and made no source or node changes.
