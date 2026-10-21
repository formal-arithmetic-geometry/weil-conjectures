## Worker report

The module `Sheaf.CategoryTheory.CompletedTensorRationalNaturality` states
`CategoryTheory.CompletedTensorComparison.naturality_and_rationalization`, with
exactly one postponed theorem proof (`sorry`). The three accompanying definitions
are the restriction P, completed bifunctor B, and specified component d appearing
in this node's own statement. They are real constructions using Mathlib's lift,
functor composition, and full-subcategory isomorphism constructor. No new notion,
new node, dependency repair, or statement correction is needed. The node copy
changes only `lean`.

Source read: the current main-20261015 blueprint's
`sec-six-functors/sk-rem-sf-pf-done/def-wf-tensor-product.md`, second sentence,
and the existing specialized implementation in `Sheaf.Paper.WeilTensorProduct`,
including `wfIntegralTensorPullback_naturality` and
`wfRationalTensorPullback_exists`. The latter is an application to complete
pro-etale complexes, rather than the abstract assertion of this node. The six
steps in this node's proof are reproduced in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring and p in A are `(A : Type r) [CommRing A] (p : A)`.
  `D : Type u`, `[Category.{v} D] [Preadditive D] [Linear A D]` are the
  A-linear category, without assuming biproducts or an additive category.
  The ring, object, and morphism universes are independently bound.
- The full A-linear subcategory is `C : ObjectProperty D`, interpreted as
  `C.FullSubcategory`. Its inherited preadditive and linear structures are
  Mathlib's instances. Its inclusion is the recorded standard `C.ι`.
- The A-linear reflector functor is `L : D ⥤ C.FullSubcategory`, with
  `[L.Additive] [L.Linear A]`. The natural unit is the natural transformation
  `η : 𝟭 D ⟶ L ⋙ C.ι`. Hypothesis `hη` says for every `X : D` and
  `Y : C.FullSubcategory` that `f ↦ η.app X ≫ f` is bijective. It is exactly
  the Hom bijection in the node, and does not assume that η is an epimorphism
  against arbitrary objects of D.
- `H : D ≌ D` with `[H.functor.Additive] [H.functor.Linear A]` is the
  A-linear equivalence. `hH` says it preserves the subcategory's objects.
  `restriction C H hH` is literally `C.lift (C.ι ⋙ H.functor) hH`, so both
  its object and morphism maps are H's maps. Its `IsEquivalence` hypothesis
  expresses exactly that this restriction P is an equivalence of C. No
  arbitrary comparison between P and H, or strict inverse to H, is assumed.
- `c` is an object-indexed family of isomorphisms `H(LX) ≅ L(HX)` in D.
  `hc` is precisely `H.map (η.app X) ≫ (c X).hom = η.app (H.obj X)`.
  No naturality hypothesis is made on c.
- `T : D × D ⥤ D` is the bifunctor. `hT` gives for each four objects a
  bilinear map whose value at `(f,g)` is `T.map (Prod.mkHom f g)`. Existence
  of this nested linear map is exactly separate A-bilinearity of the
  morphism action, including additivity; it introduces no unspecified
  tensor object or assumed comparison map.
- `τ : T ⋙ H.functor ≅ (H.functor.prod H.functor) ⋙ T` is the given natural
  isomorphism, with components `H(T(X,Y)) ≅ T(HX,HY)`.
- `tensor C L T` defines B as `(C.ι.prod C.ι) ⋙ T ⋙ L`. Thus its object
  formula is `L(T(M,N))` and its morphism formula is `L(T(f,g))`.
  `comparison C L H hH T c τ M N` defines d by
  `ObjectProperty.isoMk C (c (T.obj (M.obj,N.obj)) ≪≫
  C.ι.mapIso (L.mapIso (τ.app (M.obj,N.obj))))`. Fullness supplies the
  C-valued isomorphism, including its actual inverse, from this exact
  composite; d is not an arbitrary given family.
- `Pbar` and `Bbar` are supplied functors on the raw
  `ScalarLocalization A C.FullSubcategory p`. Hypotheses `hPobj` and
  `hBobj` give their specified object maps on all integral objects. Every
  raw localized object is a wrapper around an integral object.
- `hPmap` and `hBmap` express precisely the two fraction formulas. With
  `s = IsLocalization.Away.invSelf (S := Localization.Away p) p`, the
  project's scalar-first order represents `f/p^n` by `(s^n) ⊗ₜ[A] f`.
  The formulas preserve the exponent n for P and add n+m for B. `HEq`
  accommodates functors whose object maps are specified by equality,
  rather than definitionally identical to these expressions. Under the
  object equalities it is ordinary equality of those morphisms.
- The first conclusion is naturality of c for every arrow `f : X ⟶ X'`
  in D, with precisely `H(Lf);c_X' = c_X;L(Hf)`.
- The second conclusion is simultaneous naturality of d for every pair
  `(f,g)` in C: `P(B(f,g));d_M'N' = d_MN;B(Pf,Pg)`.
- The third conclusion is `∃! μ : Bbar ⋙ Pbar ≅
  (Pbar.prod Pbar) ⋙ Bbar`, with forward component `Q.map d.hom` and
  inverse component `Q.map d.inv` for every integral pair. This is the
  requested natural isomorphism, both component formulas, and uniqueness.
  Uniqueness with both formulas is equivalent to the node's uniqueness
  with the forward formula, since an isomorphism's inverse is determined
  by its forward map.
- There is no torsion-freeness, nonzero-p, injectivity-of-Q, or faithfulness
  hypothesis. No assumptions beyond the listed categorical and fraction
  hypotheses have been introduced.

Dependency declarations read and used:

- `def-weil-linear-category` has a Mathlib match, not a Lean record:
  `Mathlib.CategoryTheory.Linear.Basic`, `CategoryTheory.Linear` (its full
  signature and docstring), together with `Preadditive` and the inherited
  `Linear.fullSubcategory` instance. `Functor.Linear` and `Functor.Additive`
  come through the scalar-localization module's imports.
- `def-weil-linear-scalar-localization`:
  `Sheaf.CategoryTheory.ScalarLocalization`, `CategoryTheory.ScalarLocalization`
  and `ScalarLocalization.localization`. The whole recorded source was
  read, including the category's tensor Hom modules, composition, identities,
  scalar structures, and the localization and endofunctor maps. This is the
  recorded raw localization, with the same objects up to its one-field
  wrapper, rather than a Karoubi completion or categorical quotient.
- The proof-only dependencies are imported without `public`:
  `Mathlib.RingTheory.Localization.BaseChange`,
  `IsLocalizedModule.isBaseChange` (the tensor-localization Mathlib match);
  and `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule.Away`, `LocalizedModule.mkLinearMap` and
  `IsLocalizedModule.lift`. Their source signatures and docstrings were
  read. They supply the fraction-representation step of the proof plan.

Edge cases checked before writing and during the final reading:

- p=1: the formulas reduce to the integral naturality statement.
- p=0 or any nilpotent p: localization is the zero ring and every localized
  Hom module is zero. There is still a unique natural comparison, and its
  forward and inverse components have the required identities.
- Torsion Hom modules, for example Z/2 with p=2: Q need not be injective.
  Neither the hypotheses nor the conclusion ever cancels a power of p in
  the integral Hom module.
- Empty categories are not excluded by a Nonempty hypothesis. If C is empty
  while D is not, no L into C exists, just as in the informal statement.
- Zero Hom modules and identity L or H need no special assumptions.
- Ring universe r need not be bounded by v: raw Hom localization has
  universe `max r v`; no site/ring/object universe is identified.

Searches (all through the prescribed tools or read-only `rg`):

- msearch LeanFinder: "A reflector unit comparison H L X isomorphic to L H X
  is natural and extends to scalar localized bilinear functors". Eight hits,
  including `unitCompPartialBijective_symm_natural`,
  `unitCompPartialBijective_natural`, `unit_obj_eq_map_unit`, and
  `Localization.functor_linear_iff`. These give ingredients but not this
  reflector comparison and bilinear rationalization statement.
- msearch Loogle: `CategoryTheory.unitCompPartialBijective_natural,
  CategoryTheory.Localization.lift₂NatTrans`. Zero hits.
- msearch grep in Mathlib/CategoryTheory:
  `unitCompPartialBijective|lift₂NatTrans|completedTensorRational`. Fifteen
  hits, in Reflective, Bifunctor, and Closed/Ideal; no completed tensor
  rationalization statement with the given family c.
- msearch LeanSearch: "Naturality of reflector unit comparison and unique
  rationalization of completed tensor bifunctor". Eight hits, mostly the
  same generic reflector unit results. No exact match.
- Read-only project rg for
  `completed.*[Tt]ensor|[Tt]ensor.*[Rr]ational|wfRationalTensorPullback|lem-sf-completed-tensor-rational-naturality`
  in both `lean/WeilConjectures` and `lean/Sheaf`: found the specialized
  `wfRationalTensorPullback_exists` described above and unrelated completed
  tensor constructions; none states the general node.
- Read-only rg for `completedTensorRational|unitCompPartialBijective|lem-sf-completed-tensor-rational-naturality`
  in both project trees and `dag/lean_names_upstream.json`: no existing
  declaration of the node. The new namespace was also checked against the
  project category-theory sources.

Validation: the prescribed `scompile.py` compiled this file separately as
sandbox and library module against the live published build, with no errors
or warnings (6.0 s and 4.4 s). The final module contains no `#check`, private
helper, file-local notation, local instance, or proved theorem. All variables
and all three universes are explicitly bound. No STATEMENT-DISPUTED flag.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
