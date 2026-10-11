## Worker report

The module `Sheaf.Paper.AffinePerfectKoszulPrincipalUnit` states the node exactly, with
`sorry` as its proof. The statement is unchanged. A new definition module supplies the
shifted Koszul complex and its concrete canonical augmentation; no arbitrary object or
map is substituted for either.

Hypothesis and clause correspondence:

- A commutative ring: `(A : Type a) [CommRing A]`, with no domain, Noetherian,
  nontriviality, characteristic, or regular-sequence assumption.
- A finite sequence of arbitrary length: `(r : ℕ) (f : Fin r → A)`, allowing `r = 0`.
- `X = Spec A`: every occurrence is the Mathlib scheme `Spec (.of A)`.
- The union `U = ⋃ D(f_i)`: `⨆ i : Fin r, (Spec (.of A)).basicOpen
  ((Scheme.ΓSpecIso (.of A)).inv (f i))`. The inverse global-section isomorphism
  views the element as a structure-sheaf section, so this is the principal open.
- A positive exponent: `(e : ℕ) (he : 1 ≤ e)`. The theorem quantifies over any such
  exponent, and uses `fun i ↦ f i ^ e` throughout its Koszul objects and augmentation.
- `K^bullet` is the cochain reindexing of the recorded Koszul chain complex.
  `shiftedKoszulChain` has term `K_(n+1)` in degree `n` and differential
  `-koszulBoundary ... (n+1)`; extension via `embeddingDownNat` gives the term
  `K_(1-i) = K^(i-1)` in degree `i ≤ 0`, zero for `i > 0`.
- `I_e` is `DerivedCategory.Q.obj ((affineAssociatedComplex A).obj
  (shiftedKoszulComplex A r (fun i ↦ f i ^ e)))`. Associated sheaves are the
  existing Mathlib `tilde.functor`, with the shared `SheafOfModules` category.
- The canonical `u_e` is `affineKoszulAugmentation A r (fun i ↦ f i ^ e)`.
  Its module-level component in degree zero is `koszulBoundary ... 0` followed by
  Mathlib `exteriorPower.zeroEquiv`; this sends each standard basis vector to
  `f_i^e`. All other components are zero, via `ChainComplex.toSingle₀Equiv`.
  `extendMap`, termwise tilde, and `DerivedCategory.Q.map` carry this actual map
  to the derived category. Its target is the sheafified `A[0]`, canonically
  `O_X[0]` by Mathlib `tildeSelf`, not a separately chosen derived object.
- Perfectness: the first conjunct is the dependency's `Scheme.IsPerfect` applied
  to precisely this `I_e`.
- Restriction isomorphism: the second conjunct is `IsIso` of the image of this
  actual augmentation under `(SheafOfModules.overFunctor ... U).mapDerivedCategory`.
  It states that the restricted augmentation is invertible, not merely that its
  endpoints happen to be isomorphic.
- The `HasDerivedCategory` binders are the project's shared localization choices
  for `D(O_X)` and the open module categories, in unrestricted morphism universe `b`.

Dependency declarations read and used: `AlgebraicGeometry.Scheme` and
`Scheme.Hom` (Mathlib.AlgebraicGeometry.Scheme); `Scheme.IsPerfect`
(Sheaf.AlgebraicGeometry.PerfectComplex), including its pointwise open-cover
and strictly-perfect definitions; `ExteriorAlgebra.koszulComplex` and
`koszulBoundary` (Sheaf.Paper.KoszulComplex), including the exterior-power terms,
contraction differential, and square-zero theorem. The new node additionally
uses `AlgebraicGeometry.schemeDerivedCategory` and the module category from
Sheaf.AlgebraicGeometry.DerivedCategory. The latter module imports the common
restriction exactness instances, which the theorem reuses.

Edge cases checked mathematically before the final statement: `r = 0` gives
zero `I` and empty `U`, and every map in the empty-open derived category is an
isomorphism; `r = 1` gives `I^0 = A` and augmentation multiplication by `f^e`;
`f = 0` gives empty `U` without restricting `A`; a unit among the `f_i` gives
`U = X` and the usual contraction. The zero ring yields the empty affine scheme.
The negative differential and positive degree-zero augmentation agree with
Stacks 08CX, including characteristic two where minus equals plus.

Searches: msearch leanfinder, query "Koszul complex shifted augmentation perfect
restricts isomorphism on principal open": eight general complex-embedding,
augmentation and derived single-object results, no matching theorem. msearch
loogle "ExteriorAlgebra, CochainComplex": zero hits. msearch grep
"koszul|Koszul" in AlgebraicGeometry: zero hits. msearch leansearch "truncated
Koszul complex with negative differential and canonical augmentation": service
unavailable (Internal Server Error). msearch leanfinder "Koszul complex delete
degree zero negative differential augmentation to ring": eight general augmentation
results, no matching Koszul definition. msearch grep
"shiftedKoszul|koszulAugmentation|KoszulComplex": zero hits. Direct rg in the
source and Sheaf for the node id and proposed declarations: no existing match.
DAG rg and blueprint_refs searches for shifted Koszul/Koszul found only downstream
statement mentions and unrelated intrinsic-completion nodes, no definition of `I`.
Read Mathlib Modules/Tilde, Homology/Single, Homology/Embedding/Extend,
ExteriorPower/Basic to use the existing associated sheaves, degree-zero exterior
identification, and complex embeddings instead of duplicating them.

Source checked directly at https://stacks.math.columbia.edu/tag/08CX because the
referenced local perfect.tex is absent. Its displayed definition of I, the
positive degree-zero augmentation, and the paragraph after Lemma 36.9.4 match
this statement. No statement dispute or correction is needed.

Validation: both modules compiled together on the server with no errors or warnings.
All data definitions are explicit; only named proof obligations have `sorry`.

## New nodes

`def-pc-shifted-koszul-augmentation` defines the complex I with the exact truncation
and sign convention of Stacks 08CX and its canonical augmentation, then its
associated sheaf and derived augmentation on Spec A. Existing definition nodes
provide K, schemes, and D(O_X); none provides this I or map. Searches above are
recorded on the node. The general Mathlib `tilde.functor` is reused via an explicit
category-instance adapter (Scheme.Modules uses its own Category instance whereas
D(O_X) uses the common SheafOfModules instance). The adapter changes neither the
sheaves nor maps. The named square-zero, augmentation-chain-map, and zero-map
proof obligations have source and complete proofs in their docstrings, all under
this definition node, and all data are given without `sorry`.

## Second reading by M1

I reread the node, its Stacks source (Tag 08CX, Section 36.9), both delivery
modules, and every statement dependency. The correspondence is as follows.

- The commutative ring is `(A : Type a) [CommRing A]`; no domain, Noetherian,
  characteristic, or regular-sequence assumption is added.
- The finite sequence is `(r : ℕ) (f : Fin r → A)`, so the empty sequence and
  arbitrary zero entries are included. `Spec (.of A)` is the node's affine
  scheme, and the open is exactly the supremum of its basic opens using
  `Scheme.ΓSpecIso.inv`.
- The exponent is `(e : ℕ) (he : 1 ≤ e)`, and every Koszul occurrence uses
  `fun i ↦ f i ^ e`; `he` is the source's positivity hypothesis.
- `shiftedKoszulComplex` is the cochain complex with terms `K_(n+1)` in the
  nonpositive degrees and negative Koszul differential, implemented by
  `shiftedKoszulChain.extend ComplexShape.embeddingDownNat`.
- `affineAssociatedComplex` applies Mathlib's `tilde.functor` degreewise, and
  `DerivedCategory.Q.obj` gives the object `I_e` in the shared derived
  category. `affineKoszulAugmentation` is the actual degree-zero Koszul
  augmentation (the `exteriorPower.zeroEquiv` composite), extended and then
  localized; it is not an arbitrary map.
- The first conclusion is exactly `Scheme.IsPerfect` for that object. The
  second is `IsIso` of its image under the derived open restriction functor on
  the stated union, which is the node's restriction-isomorphism clause. The
  target is the sheafified `A[0]`, canonically the structure sheaf by
  Mathlib's `tildeSelf` identification.

The dependency declarations match their nodes: `Scheme`/`Scheme.Hom` are the
Mathlib scheme notions; `Scheme.IsPerfect` is the project's scheme-level
perfectness predicate; `ExteriorAlgebra.koszulComplex` and `koszulBoundary`
are the project's Koszul chain complex and differential; and
`schemeDerivedCategory` supplies the derived-category carrier. No private
replacement notion is used. The new definition node is necessary because no
Mathlib, source, or existing DAG declaration supplies this shifted complex and
canonical augmentation.

Edge cases were checked: `r = 0` gives the empty union and the zero shifted
complex; `r = 1` gives the usual two-term unit contraction after restriction;
zero entries give empty basic opens; a unit entry gives the whole affine
scheme; the zero ring and characteristic two are allowed; and `e = 1` is
included while `e = 0` is excluded by `he`. The universe binders use the ring
universe for modules and an independent derived-category universe exactly as
 the dependency declarations require.

Searches were independently repeated with `rg` over Mathlib, the source
`WeilConjectures`, and `lean/Sheaf`, plus msearch LeanFinder/Loogle queries for
shifted or truncated Koszul complexes and canonical augmentations. They found
only generic homological-complex APIs and the unrelated projective-space
Koszul sequence; no existing declaration states this notion or theorem.

No mismatch was found. The node copy and Lean signatures remain unchanged; the
only delivery addition is this independent reading record.
