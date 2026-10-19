## Worker report

The module `Sheaf.Paper.TraceFormulaStrictWeilComplex` defines the finite-coefficient
strict Weil category and its forgetful functor using the recorded coefficient conventions.
It specializes the existing `CategoryTheory.Endofunctor.IsoAlgebra` construction; it does
not define another algebra, commuting-morphism structure, or category instance.
There are five definitions, no theorem declarations, and no `sorry` terms.

The node and the main-20261015 source were read in full. The node already records the
stage-1 correction of the rational-category comparison and the geometric-point qualification
of the Jordan-block illustration. This delivery changes only its `lean` field.

Hypotheses and clauses, in order:

- Global finite-field datum: the argument `T : TraceFormulaCoefficientConventions.{u}`
  contains `T.datum : FiniteFieldDatum`. Its fields specify the prime p, positive exponent a,
  q = p^a, a field k₀ of cardinality q, and a fixed algebraic closure k.
- Coefficients A = A_{E,n}: `T.coefficients` specifies the prime l distinct from p and
  the algebraic closure of the l-adic field; `T.extension` specifies the finite extension
  inside it. `T.coefficientField` is its recorded small model, and `T.coefficientRing`
  is the recorded quotient of its valuation ring by the chosen uniformizer to `T.level`.
  Positivity is exactly `T.level_pos : 1 ≤ T.level`.
- X₀ separated of finite type over k₀: `T.X₀` is an object over `Spec T.datum.k₀`;
  the structure's `finite_type`, `quasi_compact`, and `separated` instance fields impose
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure morphism.
- X = X₀ ×_{k₀} k: `T.geometricBaseChange` is precisely `(T.datum.geometricFiber T.X₀).left`.
- Small pro-etale site and its coefficient derived category:
  `proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing` is the recorded
  derived category of `SheafOfModules` over the constant ring sheaf on `Scheme.ProEt.topology`.
  In particular, this retains the existing site object and morphism universes u+1 and u.
- Derived geometric-Frobenius pullback: `strictWeilFrobeniusPullback T` is
  `T.derivedPullback (T.datum.geometricGaloisFrobenius T.X₀)`. The first is the coefficient
  dependency's finite derived inverse image, including its positive-level indexing
  transport. The second is the scheme-Frobenius dependency's geometric Galois map,
  definitionally `(T.datum.geometricFrobenius T.X₀).hom`, not the q-power scheme Frobenius
  or the arithmetic Galois Frobenius.
- Pair (K,φ) with K in Dᵇ_ctf and φ : Lg* K ≅ K:
  `IsoAlgebra T.strictWeilFrobeniusPullback` already supplies the carrier and invertible
  structure map in the ambient derived category. `strictWeilCarrierProperty T` is the
  inverse image of `T.boundedConstructibleFiniteTor` under `IsoAlgebra.forget`.
  `strictWeilComplex T` is its full subcategory. The finite-Tor predicate is the existing
  conjunction of intrinsic bounded constructibility and finite pro-etale Tor amplitude.
  The definition imposes this condition only on the carrier and leaves the structure
  isomorphism in the ambient category, just as the node requires.
- Morphisms commute with φ: the inherited morphism, before the two full-subcategory
  wrappers, is `Endofunctor.Algebra.Hom` with field
  `h : F.map f ≫ target.str = source.str ≫ f`.
  Symmetry of equality gives precisely φ_K followed by f equals F(f) followed by φ_L.
  Neither wrapper adds a condition on arrows. Identities and composition are inherited
  from the existing algebra category and are computed on the underlying arrows.
- Category Dᵇ_ctf,W: `strictWeilComplex T` inherits the `FullSubcategory.category` instance;
  thus every commuting arrow is present, with no Ext enrichment or derived localization
  applied to this category of pairs.
- Forgetful functor For: `strictWeilForget T` lifts the composite of the carrier-property
  inclusion and `IsoAlgebra.forget` into `T.boundedConstructibleFiniteTor.FullSubcategory`.
  Its object is the same carrier with the membership proof already stored in the pair;
  its arrow is the same underlying arrow. Faithfulness is inherited from the existing
  faithful inclusion, fixed-pair forgetful functor, and full-subcategory lift.
- Structure isomorphism: `strictWeilFrobenius T K` is `K.obj.str`, with its displayed
  source and target expressed using the actual forgetful object.
- The comparison with rational Weil complexes is categorical, not an identification
  with derived Weil sheaves: the recorded `sfWeilComplex` also uses `IsoAlgebra` on its
  rational coefficient category. This module supplies no triangulated structure.
- The point/Jordan-block sentence explains the distinction rather than defining extra
  data. Here a morphism of pairs is necessarily an ambient morphism K → L. On Spec k,
  Hom(A,A[1]) = H¹(Spec k,A) = 0, so there can be no nonzero pair morphism of that type.
  Conversely the Jordan operator (x,y) ↦ (x+y,y) on A² has no equivariant splitting of
  its extension of A by A: such a splitting would require 1 = 0 in A. This is a nonzero
  finite coefficient ring because the level is positive. No derived-of-pairs construction
  is used to turn that extension into a morphism. No additional theorem node is stated.

Dependency declarations read and used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `coefficientField`, `coefficientRing`,
  `geometricBaseChange`, `boundedConstructibleFiniteTor`, and `derivedPullback`.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `WeilConjectures.FiniteFieldDatum.geometricGaloisFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`,
  used through `T.derivedPullback`, not reconstructed in this delivery.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and `geometricFiber`,
  used through the coefficient conventions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and topology,
  used by the existing `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` encoding.
- `Sheaf.Paper.SfWeilSheafComplex`: `WeilConjectures.sfWeilComplex` and `sfWeilForget`
  were read to check the rational comparison; they are not used as finite categories.
- The scheme-morphism-properties node explicitly introduces no declaration: the
  corresponding Mathlib properties are exactly the instance fields of T above.
- `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`: `IsoAlgebra`, its
  `forget` and `str`. `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory` supplies
  the full-subcategory instance, inclusion and lift. These are the same fixed-pair
  construction already used by the rational dependency, not private copies.

Edge cases checked before writing: the zero complex and empty geometric scheme are
not excluded; an invertible structure is required even for these cases, with no
nonzero-carrier assumption. Level n = 1 is included. Higher positive levels are retained
without imposing field coefficients or freeness on the complex. Arbitrary cohomological
bounds and finite Tor intervals remain existential in the dependency predicate.
No connectedness, smoothness, reducedness, or pullback-preservation hypothesis is added.
The isomorphism direction is Lg* K → K throughout.

Searches for an existing declaration (2026-10-18):

- `msearch.py leansearch`, query `category of pairs of constructible complexes and
  Frobenius isomorphism`: eight unrelated Mathlib hits, including categorical Frobenius
  morphisms, pair diagrams and bicomplex isomorphisms; no matching notion.
- `msearch.py leanfinder`, query `strict Weil complexes finite coefficients pairs
  constructible derived category geometric Frobenius isomorphism`: eight hits on period
  rings, isocrystals and bounded derived representatives; no matching declaration.
- `msearch.py loogle`, query `WeilComplex, IsoAlgebra`: no hits, unknown identifier
  `WeilComplex` in Mathlib.
- `msearch.py grep`, query `WeilComplex|IsoAlgebra|strict Weil`, subdirectory CategoryTheory:
  zero Mathlib hits. Direct reading located Mathlib's general `Endofunctor.Algebra`,
  and the upstream `IsoAlgebra` extension, which this module reuses.
- `rg` over the upstream source and `lean/Sheaf`, by those names and the blueprint id:
  found the upstream Etale `WeilComplex`, upstream ProEtale `StrictWeilComplex` and
  `GeometricFiberStrictWeilComplex`, and the project's rational `sfWeilComplex`.
  All were read, including the upstream pro-etale underlying `DerivedCategoryFiniteTor`.
  The etale and rational forms have different sites or coefficients. The pro-etale
  form is a general construction over `DerivedCategory (Sheaf ... A)` and its own
  `DerivedCategory.constructibleFiniteTor` predicate, with an arbitrary coefficient category
  and scheme automorphism. It is not an interface on the recorded intrinsic
  `SheafOfModules` category, finite-Tor predicate, chosen finite-field datum and derived
  constant-ring pullback. Recording it alone would not render the node using its
  dependency declarations. This delivery therefore specializes the already available
  generic fixed-pair construction on the exact recorded category instead.
- Exact proposed-name search in upstream sources, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no existing `strictWeilComplex` or `trfStrictWeilComplex` declaration.

No statement dispute, statement correction, new node, or dependency-record repair is needed.

Validation: `scompile.py Q10 def-trf-strict-weil-complex` accepted the delivered module
without errors or warnings (14.1 seconds for the library-file check). The delivery dry run
also passed compilation and the server's stage-2 preflight. The node diff contains only
`lean`; the Lean file has no line over 100 characters and no `sorry` term.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
