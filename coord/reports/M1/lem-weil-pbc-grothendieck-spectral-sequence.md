## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` states the relative
Leray spectral sequence with no restriction on the source sheaf. All three named theorem
proofs are `sorry`; no definition is introduced, no statement correction is needed, and
there are no new nodes or dependency modules.

Declarations:
- `AlgebraicGeometry.Etale.exists_module_grothendieck_spectralSequence` is the commutative
  coefficient-ring version.
- `AlgebraicGeometry.Etale.exists_abelian_grothendieck_spectralSequence` is the abelian-sheaf
  version explicitly mentioned by the node.
- `AlgebraicGeometry.Etale.abelian_rightDerived_iso_higherDirectImage` supplies the final
  identification of injective-resolution right derived functors with cohomology of the
  bounded-below derived direct image; instantiate `g` with `f`, `h`, or `f ≫ h`.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Schemes X, Y, Z and morphisms X → Y → Z | `{X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)` |
| Commutative coefficient ring Λ | `(Λ : Type (u + 1)) [CommRing Λ]`; no finiteness, nonzero-ring, characteristic, torsion or Noetherian assumptions |
| Small etale site of T | `T.smallEtaleTopology` on `T.Etale` |
| Modules over the constant ring sheaf Λ_T | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` |
| Direct images f_*, h_*, (hf)_* | `lowerStar (ModuleCat Λ) f`, `lowerStar (ModuleCat Λ) h`, `lowerStar (ModuleCat Λ) (f ≫ h)` |
| R^q computed by injective resolutions | `Functor.rightDerived q` on each direct image |
| A spectral sequence for every F, functorial in F | `∃ E : E₂CohomologicalSpectralSequence (A ⥤ C)`; evaluation at F gives the individual spectral sequence |
| Pages for r ≥ 2 | `E.page r hr`, where `r : ℤ` and `hr : 2 ≤ r` |
| d_r : E_r^(p,q) → E_r^(p+r,q-r+1) | The shape of `E₂CohomologicalSpectralSequence` is `ComplexShape.up' (r, 1-r)` on `ℤ × ℤ` |
| d_r composed with d_r is zero | `HomologicalComplex.d_comp_d`, a field law of every `E.page r` |
| E_(r+1) is ker d_r / im d_r | `SpectralSequence.iso`: homology of `E.page r` is isomorphic to the next page |
| E_2^(p,q) = R^p h_*(R^q f_* F) for p,q ≥ 0 | `∀ p q : ℕ, Nonempty ((E.page 2).X (p,q) ≅ fStar.rightDerived q ⋙ hStar.rightDerived p)` |
| E_2^(p,q) = 0 otherwise | `∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2).X (p,q))` |
| First-quadrant spectral sequence | This support condition propagates to every page by the homology-to-next-page isomorphisms |
| Stabilization for r > max(p,q+1) | The third conjunct quantifies `r`, its page bound `hr`, and natural p,q, and gives the natural next-page/current-page isomorphism under precisely that strict bound |
| Abutment H^n = R^n(hf)_* F | `hfStar.rightDerived n`; filtration is on this functor itself |
| Finite decreasing filtration | `∃ filtration : ∀ n : ℕ, DecreasingFiltration (hfStar.rightDerived n)` |
| F^0 H^n = H^n | `(filtration n).step 0 = ⊤` |
| F^(n+1) H^n = 0 | `IsZero ((filtration n).step ((n : ℤ) + 1) : A ⥤ C)`; a subobject is bottom exactly when its representing object is zero |
| gr^p H^n ≅ E_infty^(p,n-p) | Final conjunct: for `p ≤ n` and every page above `max(p,n-p+1)`, `Nonempty ((filtration n).gradedPiece p ≅ (E.page r hr).X (p,n-p))` |
| Functorial pages, filtration and all comparisons | Everything lives in `A ⥤ C`: differentials and isomorphisms are natural transformations; filtration steps are subfunctors of the specified abutment, and quotient isomorphisms are natural isomorphisms |
| No hypothesis on F | The functor domain is all sheaves, rather than an acyclic/torsion/constructible subcategory |
| Λ = ℤ gives every abelian sheaf | The second theorem has `AddCommGrpCat.{u + 1}` in every coefficient position and the same pages, stabilization and filtration clauses |
| R^q u_* = H^q(Ru_* F) for abelian sheaves | The third theorem gives a natural isomorphism from `(lowerStar AddCommGrpCat g).rightDerived q` to `DerivedCategory.Plus.singleFunctor _ 0 ⋙ rightDerivedLowerStarPlus AddCommGrpCat g ⋙ DerivedCategory.Plus.homologyFunctor _ (q : ℤ)` |

The equalities between categorical objects are expressed as isomorphisms, as is customary
for chosen resolutions, kernels and quotients. An isomorphism in the functor category is
a natural isomorphism, not a family of unrelated objectwise witnesses. Once incoming and
outgoing differentials vanish, the spectral sequence's homology identification gives
its canonical stable-page identification. The final graded-piece clause applies to every
stable page, so no separate privately defined E_infty object is needed. Natural-number
indices cover precisely the nonnegative derived degrees. For p > n the graded piece
is zero, since the decreasing filtration is already zero at n+1; this accounts for the
negative second-coordinate cases. Evaluation preserves kernels, cokernels and homology,
so functor-category pages and graded pieces evaluate to the node's pages and quotients.

The constant-ring module encoding is the same used by landed
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
`Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible`, and the source's SixFunctors
library. Constant scalar actions extend uniquely to locally constant scalars by gluing:
a local presentation of a section of Λ_T as constants defines its action; compatibility
on overlaps and independence of presentation follow from the sheaf condition. Conversely
restricting a Λ_T-action to constants gives a presheaf of Λ-modules. Linear natural maps
extend in the same way. This identifies the categories, including direct images. For ℤ,
every abelian sheaf has the unique usual integer action, and every additive map is linear.
Thus this encoding drops none of the Λ_T-module objects or morphisms.

Dependency declarations read and used:
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms in
  `Mathlib.AlgebraicGeometry.Scheme` (the locally ringed space with local affine charts).
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.smallEtaleTopology` in
  `Mathlib.AlgebraicGeometry.Sites.Etale` (topology on schemes etale over the base).
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf` in
  `Mathlib.CategoryTheory.Sites.ConstantSheaf` (sheafification of the constant presheaf),
  used through the constant-ring module interpretation above; no second constant sheaf.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf` and its abelian instance, interpreted for
  constant coefficients via the module-valued sheaf encoding, not redefined.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  The recorded latter declaration is actually in the Derived module, not the recorded
  Defs module; the correct source module is imported. Its definition is precisely
  `(lowerStar A g).rightDerivedFunctorPlus`.
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.rightDerived` in
  `Mathlib.CategoryTheory.Abelian.RightDerived`; its full signature requires an additive
  functor and injective resolutions. These instances are inferred for the actual sheaf
  categories; they are not extra hypotheses in the theorem.
- `def-sp-filtration`: `CategoryTheory.DecreasingFiltration` and
  `CategoryTheory.DecreasingFiltration.gradedPiece` in `Sheaf.CategoryTheory.Filtration`;
  these are used literally, including integer indexing and cokernel of adjacent-step
  inclusion.
- `def-weil-pbc-abelian-etale-sheaves`: `CategoryTheory.Sheaf` in
  `Mathlib.CategoryTheory.Sites.Sheaf`, instantiated with the small etale topology and
  `AddCommGrpCat` exactly as the record says.
- Abstract page structure: `CategoryTheory.SpectralSequence` and
  `CategoryTheory.E₂CohomologicalSpectralSequence` in
  `Mathlib.Algebra.Homology.SpectralSequence.Basic`; full page, differential and homology
  signatures read. `CategoryTheory.Abelian.functorCategoryAbelian` provides pointwise
  abelian structure, and the imported source instances give enough injectives for the
  etale sheaf categories.

Sources checked: [Stacks 0734](https://stacks.math.columbia.edu/tag/0734) states relative
Leray for module sheaves and functoriality in the source sheaf; its proof invokes
[Stacks 015N](https://stacks.math.columbia.edu/tag/015N), whose statement supplies the
bidegree, second page, convergence and finite filtrations. Local literature copies are
absent on this machine, so these two source places were opened online. The natural-language
proof in each declaration includes every step of the node's proof (Grothendieck abelian
categories, composition, injective preservation and acyclicity, spectral sequence,
first-quadrant convergence, and the integer/abelian comparison).

Edge cases checked before writing:
- n = 0 gives F^0 = H^0 and F^1 = 0, with gr^0 identified with E_2^(0,0) already for r=2.
- p=0 and q=0 use the strict bound r > max(p,q+1), including the lower-page bound r≥2.
- Negative p or q are explicitly zero on E_2; no truncated integer subtraction in the
  differential shape. The only natural subtraction n-p occurs under p≤n.
- Arbitrarily large n and p, and the boundary p=n, retain the stated bounds.
- Empty schemes, identity maps, zero sheaves and the zero coefficient ring are allowed;
  there is no nonemptiness, nontriviality, finite-type or acyclicity assumption.
- Schemes use universe u, coefficient objects and modules u+1, the source library's
  convention. Any given schemes and coefficient ring fit by raising u as needed;
  no quantification over test objects in a smaller, possibly vacuous universe occurs.

Searches on 2026-10-11:
- `msearch.py ... leanfinder "Grothendieck spectral sequence for composite direct images
  of etale module sheaves"`: 8 hits, consisting of ring-etale composition/Kaehler
  differential lemmas and scheme-module pushforward coherence; none is this statement.
- `msearch.py ... loogle "CategoryTheory.SpectralSequence"`: 12 hits for the abstract
  structure, pages, isomorphisms and morphisms; no Grothendieck/relative Leray theorem.
- `msearch.py ... grep "grothendieck.*spectral|spectral.*grothendieck|Leray"`: 0 hits.
- `msearch.py ... leansearch "Grothendieck spectral sequence for composition of left
  exact functors"`: UNAVAILABLE, HTTP service Internal Server Error; no verdict inferred
  from the unavailable search.
- `rg` on source `WeilConjectures` for the item id: 0 hits. Searches for Grothendieck
  spectral sequences found derived-composition machinery, not a spectral sequence.
- `rg` on `lean/Sheaf` and source category-theory files for Grothendieck machinery and
  constant/module direct images: existing filtration and module-coefficient encoding
  found; no statement giving these pages, stabilization, filtrations and functoriality.
- Full proposed declaration names searched in Mathlib, `WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json`: no collisions.

Validation: server single-file compile passed in 2.0 seconds with no warnings or errors
before final import cleanup. The final file is checked again by the delivery dry run.
The first compile encountered expensive bottom-subobject instance search in the functor
category; the zero last step is now expressed equivalently using `IsZero` of its
representing functor, avoiding that search without increasing compiler limits.

## Second reading by M1

I independently read the node statement and the module declaration. The introduced objects
are schemes `X Y Z : Scheme.{u}`, composable morphisms `f : X ⟶ Y` and `h : Y ⟶ Z`, and a
commutative coefficient ring `Λ : Type (u + 1)` with `[CommRing Λ]`. The module renders these
exactly in `exists_module_grothendieck_spectralSequence`; it adds no finiteness,
Noetherianity, characteristic, nonzero, or acyclicity hypothesis. It also has the separate
integer-coefficient theorem `exists_abelian_grothendieck_spectralSequence`.

The node's small-etale sites and coefficient categories are rendered as
`Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` (and as
`Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}` in the abelian case), using the recorded
Mathlib/site declarations. The direct images are the recorded `lowerStar` functors for `f`,
`h`, and `f ≫ h`; their right derived functors are `Functor.rightDerived`, as required by
the dependency. The spectral sequence is an
`E₂CohomologicalSpectralSequence (A ⥤ C)`, which packages functoriality in every source
sheaf. Its page-2 clause gives `R^p h_*(R^q f_*)` for natural `p,q`; the integer clause
makes all negative bidegrees zero. The page type supplies the differential bidegree and
`d ∘ d = 0`, and its homology/page structure supplies `E_{r+1} ≅ ker d_r / im d_r`.
The explicit third conjunct gives the node's stable-page bound
`r > max(p,q+1)`. The filtration is on `hfStar.rightDerived n`, with step zero equal to
`⊤`, step `n+1` zero, and graded pieces identified with every page above the exact stable
bound; this is the node's finite decreasing filtration and `E_∞` clause, in functorial form.
The abelian theorem uses `AddCommGrpCat` and the final comparison theorem identifies its
right-derived functors with the higher cohomology of `rightDerivedLowerStarPlus`, matching
the node's final sentence.

I checked edge cases `n = 0`, `p = q = 0`, `p = n`, negative indices, empty schemes,
identity maps, zero sheaves, and the zero coefficient ring. None is excluded; natural-number
indices and the integer page indices retain the stated boundary behavior. Universes are
bound explicitly by `u`, with coefficient categories at `u + 1`.

Searches were rechecked in Mathlib, `WeilConjectures`, and `lean/Sheaf` for Grothendieck or
Leray spectral-sequence declarations and for the full proposed names; only abstract
spectral-sequence and underived pushforward APIs were found. LeanFinder/Loogle searches
similarly found no relative Leray theorem. The module compiles cleanly with
`scompile.py`; no mismatch with the node was found, so no source or node change was needed.
