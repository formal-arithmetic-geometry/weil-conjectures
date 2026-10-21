## Worker report

The module `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatConstantScalarMono` states
`SheafOfModules.constantScalar_injective_of_flat`, with its sole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. No new nodes,
dependency repairs, statement corrections or disputed statements are needed.

Hypothesis and conclusion correspondence:

- The small site is `{C : Type uC} [Category.{vC} C]` with
  `J : GrothendieckTopology C`. The object and morphism universes are independent.
  A category with these set-sized collections is small in their maximum universe;
  no topology, terminal object, or enough-points condition is added.
- The coefficient ring is `(A : Type r) [CommRing A]`. No domain, nontriviality or
  nonzero-scalar assumption is imposed.
- The constant commutative ring sheaf is exactly
  `(constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A)`. The recorded
  `CategoryTheory.constantSheaf` is the constant presheaf followed by sheafification.
  Forgetting commutativity uses the canonical `sheafCompose` functor.
- The module sheaf `M` has type `ringedSiteModules` over that forgotten ring sheaf.
  This is the recorded transparent abbreviation for Mathlib's `SheafOfModules`,
  rather than a copy or the fixed-scalar `Sheaf J (ModuleCat A)` encoding.
- Flatness is exactly `(hM : IsFlatOnSite M)`, the recorded predicate asserting
  exactness of the sheafified tensor functor `siteSheafTensorRight M`.
  In particular there is no assumption that the modules of sections are flat.
- The scalar and regularity hypothesis are `(a : A)` and
  `(ha : Function.Injective (fun x : A ↦ a * x))`, verbatim the node's injectivity
  condition on the original ring.
- `∀ U : C` covers every object. Its first conjunct is injectivity of
  `s ↦ ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)) a * s`.
  The source type `(sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).obj (op U)`
  is definitionally the sections of the above constant ring sheaf. Writing that
  unfolding avoids a heterogeneous-multiplication instance elaboration failure.
- The second conjunct is injectivity of the same constant section acting by `•`
  on `M.val.obj (op U)`. The action is the existing module-sheaf action and the
  scalar section is the canonical sheafification unit, not a separately chosen map.
- These two sectionwise injectivity assertions are also exactly the monomorphism
  assertions: module-sheaf kernels are sectionwise, and cancellation of morphisms
  can be checked on every component. Multiplication on the ring is understood as
  a module/additive-sheaf endomorphism, not incorrectly as a ring homomorphism.

The explicit `HasSheafify J CommRingCat`, `HasSheafify J AddCommGrpCat`,
`J.HasSheafCompose (forget₂ CommRingCat RingCat)` and
`J.WEqualsLocallyBijective AddCommGrpCat` instance parameters expose the
sheafification and forgetful infrastructure already needed by the recorded constant
sheaf and flatness interfaces. They are standard for small sites in an adequate
ambient universe; they add no geometric or algebraic restriction. Ring universe `r`
and extra module universe `m` are independent of both site universes. Modules use
`max r m`, so the regular coefficient module can serve as a tensor test object.
Any given small site and coefficient/module data can be placed in a common adequate
universe; the statement does not force the object and morphism universes equal.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`; the scalar section additionally uses
  `CategoryTheory.toSheafify` from `Mathlib.CategoryTheory.Sites.Sheafification`.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, definitionally `SheafOfModules` with its
  sectionwise module structures and semilinear restrictions.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, defined using the existing
  `SheafOfModules.siteSheafTensorRight` and `CategoryTheory.exactFunctor`.

The stated proof plan is included in the declaration docstring in all four steps.
The recorded proof-dependency tensor module
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is imported without
`public`, as are the Mathlib module-sheafification interface and exact-functor
homology API. The sheafification-preserves-finite-limits interface is already
publicly imported by `ConstantSheaf`. Sources were read in
`literature/stacks-project/sites-modules.tex`: `lemma-sheafification-exact`
(Tag 03EI), `definition-flat`, clause (3) (03ER), and `section-tensor-product`
(03EK). The statement matches these and the supplied four-step node proof.

Edge cases checked before finalizing the signature:

- Empty site: the objectwise conclusion is vacuous; no nonempty or terminal-object
  hypothesis is present.
- An object with an empty cover: the relevant sheaf sections are forced trivial,
  which is compatible with injectivity.
- Zero module: the second scalar map is injective, without requiring `M ≠ 0`.
- Zero ring and `a = 0`: regularity permits this precisely when the original ring
  is subsingleton; the constant ring and its modules then have trivial sections.
- Rings with zero divisors: `A = ℤ/6`, `a = 5`, and `A = ℤ × ℤ`, `a = (2,3)`
  satisfy the regularity premise. The latter shows regular nonunits are retained.
- Flatness is essential: on the one-object trivial site `A = ℤ`, `a = 2`,
  `M = ℤ/2` would violate the second conclusion without `hM`.
- No stalks or points occur, and the proof only tensors a sheaf monomorphism;
  it does not infer sectionwise flatness or treat all tensor sections as pure tensors.

Searches for an existing statement (no exact match):

- `msearch.py ... leanfinder` with query
  `A regular scalar acts injectively on a flat sheaf of modules over the constant sheaf of rings on any small site`:
  eight results, including `Module.Flat.isSMulRegular_of_isRegular`,
  `Module.Flat.isSMulRegular_of_nonZeroDivisors` and `IsSMulRegular.of_flat`.
  These concern ordinary modules, not flat sheaf tensor on arbitrary sites.
- `msearch.py ... loogle '"SheafOfModules", "Mono"'`: twelve results,
  principally presheaf mono criteria and tensor constructions; no such theorem
  about flat module sheaves over a constant ring sheaf.
- `msearch.py ... grep 'isSMulRegular|constantSheaf.*[Mm]ono|[Mm]ono.*constantSheaf' Algebra/Category/ModuleCat`:
  two hits in `ModuleCat/Ext/Basic.lean`, neither an exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `IsFlatOnSite|constant.*[Ss]calar|scalar.*[Mm]ono`, and the narrower
  `constantScalar_injective_of_flat|constant.*scalar.*injectiv|regular.*scalar`,
  found existing flatness uses, scalar constructions and unrelated regular-module
  calculations, but no theorem with this arbitrary-site assertion.
- The literal node-id search in `lean/WeilConjectures` found no declaration.
  The chosen declaration name was also absent from `dag/lean_names_upstream.json`.

## Second reading by O4

This is the author's second pass with the node and final Lean signature open;
the independent maintainer review is separate. The ring, site, module and scalar
are the same objects as in the node. The only mathematical hypotheses are the
commutative-ring structure, flatness of the sheaf tensor functor, and injectivity
on A. The four instance parameters supply the existing sheaf interfaces. Both
sectionwise injectivity clauses are present, hence both module-sheaf monomorphism
claims. The ring-section type is an unfolding of the recorded constant sheaf,
not the constant presheaf A. The scalar is the image of a under its canonical
unit, not a globally chosen lift or an arbitrary ring section. No domain,
nontriviality, enough-points, sectionwise-flatness or nonempty-site condition was
introduced. The elaboration adjustment changed only the definitional spelling
of the ring sections. No mathematical mismatch or source correction was found.
