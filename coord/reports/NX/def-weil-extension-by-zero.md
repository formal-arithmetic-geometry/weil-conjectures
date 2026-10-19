## Worker report

The new module `Sheaf.AlgebraicGeometry.ProEtaleExtensionByZero` defines
`AlgebraicGeometry.Scheme.proEtaleExtensionByZero` as the existing extension-by-zero
module-presheaf functor followed by the existing module-sheafification functor.
It introduces no theorem, proof, auxiliary notion, or sorry. The node is unchanged
except for its `lean` record.

Hypotheses and clauses, matched individually:

- A finite commutative ring is `(A : CommRingCat.{u + 1}) [Finite A]`.
  `RingCat.of A` forgets commutativity for the module-sheaf API, without changing
  the ring operations. No nontriviality, characteristic, or invertibility is assumed.
- The ambient scheme is `(X : Scheme.{u})`; `(U : X.ProEt)` packages the second
  scheme `U.left` and its morphism `U.hom : U.left ⟶ X`.
  `[IsOpenImmersion U.hom]` is precisely the open-immersion hypothesis.
  Every open immersion is weakly etale, so can be packaged by `Scheme.ProEt.mk`;
  the packaging adds no mathematical restriction.
- The small pro-etale site is `X.ProEt`, with `ProEt.topology X`.
  Its values and module sections live in universe `u + 1`, large enough for
  its morphism-indexed direct sums and sheafification. There are no independent
  smaller test universes or extra smallness assumptions.
- The constant coefficient ring sheaf is exactly
  `(constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of A)`.
  This uses the ring-valued presentation of the localization dependency; it is
  the sheafification of the constant presheaf, with no altered scalar structure.
- The statement expressly says to regard M as an `A_X|_U`-module on `X_proet/U`.
  Accordingly the input category is `ringedSiteModules (A_X.over U)`.
  This is the localized-site presentation in the statement, not a replacement
  coefficient category. The already recorded `ProEt.weaklyEtale_localization`
  identifies its objects and ring actions with `A_U`-modules on `U.left.ProEt`
  (the `q` equivalence in that theorem). The module imports that dependency and
  documents this presentation. No unspecified equivalence is selected to
  manufacture data from an existence theorem containing sorry.
- The output category is `ringedSiteModules A_X` on the ambient pro-etale site.
- The entire piecewise formula for P_M is supplied by
  `SheafOfModules.extensionByZeroPresheaf A_X U`: its section module is
  `DirectSum (V ⟶ U) (fun φ => M.val.obj (op (Over.mk φ)))`.
  The localization theorem's final clause says the indexing type is subsingleton
  for an open immersion and is inhabited exactly on factorizations through U.
  Thus the direct sum is M at that factorization, or zero when there is none.
  The existing presheaf module even states its empty-index and unique-index
  identifications (`extensionByZeroPresheafSection_isEmpty` and `_unique`).
- Scalar multiplication is the existing direct-sum module action: its summand
  ring is definitionally `A_X(V) = (A_X.over U)(V ⟶ U)`, and localization
  identifies that action with the A_U action.
- Restrictions use `extensionByZeroPresheafRestrictAdd`: the summand indexed by
  φ is mapped via M's restriction to the summand indexed by `a ≫ φ`.
  If the original value is zero this is the zero map. If the original object
  factors through U, every object mapping to it factors through U as well.
- On module morphisms the first functor uses
  `extensionByZeroPresheafHomApp`, the direct sum of the components of α.
  The second functor maps this presheaf morphism by sheafification.
- Sheafification is `PresheafOfModules.sheafification (𝟙 A_X.obj)`.
  Its composite with the first functor specifies both object and morphism parts
  and all functor laws through the existing functor structures.
- The rings A_{E,n} are examples of the finite rings already covered; the
  coefficient construction is a pointer, not an extra hypothesis.
- No assumption about ordinary geometric stalks or their conservativity occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`: open immersion of locally ringed spaces.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`: read its full definition
  and docstring for the same underlying small pro-etale site and constant-ring
  module-sheaf setup. This item needs the underlying site and module category,
  not its derived-category wrapper; that wrapper is not applied here.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`: constant presheaf followed by sheafification.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: transparent abbreviation of Mathlib's
  `SheafOfModules`, with exactly its sectionwise-linear morphisms.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
  `AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`: full signature and
  docstring read, including canonical site equivalence, coverings, coefficient
  comparison, module equivalence, and unique-factorization clauses.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`,
  `SheafOfModules.extensionByZeroPresheaf`: full construction read, including
  the section, restriction and morphism definitions and zero/singleton cases.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
  `PresheafOfModules.sheafification`: full signature, required locally bijective
  ring map and sheafification assumptions, and its object/morphism construction
  read. They synthesize for the identity of A_X in the chosen universe.

Sources read: the node's blueprint file at order 1471;
`literature/stacks-project/sites-modules.tex`, Lemma 03DI and its construction;
`literature/stacks-project/proetale.tex`, Definition 09AE. The latter's module
clause and 03DI give exactly the localized module-sheaf construction here.
Also read `coord/pefw-upstream-framework.md` and the exact finite-coefficient
open-lower-shriek side-overlay source.

Edge cases checked by inspection before writing:

- No factorization: the empty direct sum is the zero module.
- Unique factorization: the one summand gives the specified value of M.
- Empty U: nonempty test schemes do not factor through U; empty test schemes
  still have their unique factorization, as required by the piecewise formula.
  No false claim that every presheaf value is zero is imposed.
- U = X with identity immersion: every object has its unique structure map,
  so the formula recovers M before sheafification up to the standard isomorphism.
- Empty X, zero M, and the one-element coefficient ring are included.
- Restriction out of an object factoring through U cannot land at an object
  that fails to factor through U; the remaining zero-source case is well-defined.

Searches made (no matching module-sheaf extension-by-zero functor found):

- `msearch.py ... leanfinder "extension by zero sheaves of modules on pro etale
  site along open immersion"`: eight hits, including ordinary scheme-module
  restriction, generic module sheafification, and condensed-module constructions;
  no matching definition.
- `msearch.py ... loogle "SheafOfModules, PresheafOfModules.sheafification"`:
  twelve hits, all generic sheafification and related adjunction/compatibility
  declarations; no extension-by-zero definition.
- `msearch.py ... grep "extensionByZero|extension by zero|lowerShriek"
  Algebra/Category/ModuleCat`: zero Mathlib hits.
- `msearch.py ... leansearch "extension by zero sheaves of modules"`:
  unavailable (Internal Server Error); no verdict inferred from the failure.
- `rg` of `extensionByZero|extension.by.zero|lowerShriek|jShriek` in
  `lean/Sheaf` and the upstream pro-etale subtree found the generic
  extension-by-zero presheaf, localized adjunction statements using its inline
  sheafification composite, and generic coefficient-category lower shriek.
  `grep -rn "def-weil-extension-by-zero"` upstream found no matching node tag.
  Searches of upstream Mathlib/AlgebraicGeometry project extensions found no
  module-sheaf definition with this name or signature.
- Read `ProEtale.localizationLowerShriek`, `localizationLowerShriekPresheaf`,
  and `openImmersionLowerShriek` in the upstream open-immersion definitions,
  and the exact copied `FiniteCoefficient/LowerShriek/Open/Defs.lean`.
  These act on `Sheaf J D` for a fixed coefficient category D, not on
  `SheafOfModules` for the specified sheaf of rings; they do not directly supply
  the node's presheaf-of-modules construction. None is duplicated here.
- Searched `dag/lean_names_upstream.json` for extensionByZero: the hits concern
  Weil-sheaf trace results, not the present definition. Searched the proposed
  declaration name; it is fresh.

Validation: server-only `scompile.py NX def-weil-extension-by-zero` compiled
all required side dependencies and this delivered module cleanly; the module
itself took 1.9 seconds, nice 19, two threads, 60-second per-file limit.
No local Lean invocation or global build. No node fault or statement dispute.


## Second reading by NX

I independently read the node copy, its blueprint source (order 1471), Stacks
`sites-modules.tex`, Lemma 03DI and its construction, and `proetale.tex`,
Definition 09AE, including the surrounding extension-by-zero context. Lemma
03DI assumes an arbitrary ringed site and its localized ringed site; 09AE
assumes a weakly etale morphism and, for modules, a ring. The node specializes
to an open immersion and finite commutative coefficients. There is no hidden
Noetherian, quasi-compactness, characteristic or nontriviality assumption.

Object/hypothesis/clause checklist, made against the node:

1. Finite commutative ring A: `(A : CommRingCat.{u + 1}) [Finite A]`.
   `RingCat.of A` retains exactly its ring structure. Verdict: exact; no field,
   invertibility or nonzero hypothesis.
2. Schemes U and X and open immersion j: `(X : Scheme.{u}) (U : X.ProEt)`
   and `[IsOpenImmersion U.hom]`, with domain scheme `U.left` and j = `U.hom`.
   I read Mathlib's `Scheme.ProEt`, `ProEt.mk` and `IsOpenImmersion` declarations.
   All open immersions are weakly etale and thus give such objects; there is no
   extra condition on j. Verdict: exact bundled presentation.
3. The small pro-etale sites: `ProEt.topology X` on `X.ProEt`, and its over-site
   at U. I read `proEtaleDerivedCategory` and the full signature and docstring of
   `ProEt.weaklyEtale_localization`. The latter identifies `Over U` with
   `U.left.ProEt`, preserving the actual underlying schemes, arrows and covers.
   Verdict: the precise sites in the node, with the permitted localization.
4. Constant ring coefficients A_X and A_U: the term
   `((constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of A))`
   is A_X, and `.over U` is its restriction. I read `constantSheaf` as constant
   presheaf followed by sheafification. The localization theorem's ring clause
   identifies this restricted ring with A_U, fixing constant sections.
   Verdict: correct coefficients, not a different structure sheaf.
5. Input M and output j_! M: the functor domain is
   `ringedSiteModules (A_X.over U)` and its codomain `ringedSiteModules A_X`.
   I read `ringedSiteModules`, a transparent abbreviation of `SheafOfModules`,
   and the localization theorem's q equivalence, including its equation on
   underlying module presheaves. The node expressly regards M as a localized
   module. Using that presentation requires no choice of data from its sorry
   theorem. Verdict: exact presentation expressly allowed by the node.
6. Values of P_M: the first factor `SheafOfModules.extensionByZeroPresheaf A_X U`
   uses `extensionByZeroPresheafSection`, the direct sum over `V ⟶ U` of
   `M.val.obj (op (Over.mk φ))`. I read this construction and its empty/unique
   index identifications. The localization theorem's final clause supplies
   at most one arrow and existence exactly for factorizations through j.
   Verdict: precisely the node's piecewise values, up to the canonical
   singleton-direct-sum identification; no new arbitrary zero/nonzero data.
7. Module action: each summand has scalars `A_X.obj.obj V`; localization of the
   ring makes this definitionally the ring at `Over.mk φ`. The direct-sum
   action therefore is exactly the stipulated action. Verdict: exact.
8. Restrictions: `extensionByZeroPresheafRestrictAdd` sends the φ summand along
   M's restriction for `Over.homMk a.unop` into the `a.unop ≫ φ` summand.
   With no φ its source is zero. Verdict: exactly both cases in the node;
   restriction from a factoring V has a factoring source V' as required.
9. Morphisms: `extensionByZeroPresheafHomApp` is `DirectSum.lmap` of
   `(α.val.app (op (Over.mk φ))).hom`. The composite's second map is the
   sheafification of this map. Verdict: every morphism clause is present.
10. Sheafification and the functor: the second factor is
    `PresheafOfModules.sheafification (𝟙 A_X.obj)`. I read its signature,
    obj/map definitions and the required sheafification and local bijectivity
    instances. These synthesize without extra binders on this site. Composition
    supplies object/map parts and functor laws. Verdict: concrete construction,
    with no hollow definition and no newly proved theorem.
11. The examples A_{E,n} introduce no further quantified object or hypothesis;
    all finite rings are covered. No stalk hypothesis occurs. Verdict: exact.

Edge cases: the empty factorization index gives the zero module; one
factorization gives M's section module. The empty open is included, and the
empty test scheme still factors through it, so the formula does not falsely
force all presheaf sections to vanish. Identity immersion has one factorization
for every test object. Empty X, zero M and the zero ring are included. There is
no n binder and no characteristic restriction; in particular n = 0 examples
are covered whenever they give a finite coefficient ring. Schemes use one
universe u, as in the site dependency; coefficients and module sections live
in u+1, which contains finite rings and the morphism-indexed sums. No independent
smaller test universe or smallness binder excludes an edge case. All variables
and universes in the delivered signature are explicitly bound.

Independent searches, using different descriptions from the worker:

- `msearch.py NX def-weil-extension-by-zero leanfinder "sheaf modules localized
  site left adjoint restriction extension zero"`: eight hits, generic module
  sheafification adjunctions and their comparison maps; no matching functor.
- `msearch.py NX def-weil-extension-by-zero loogle "SheafOfModules.overFunctor"`:
  three hits, module restriction, its compatibility map and the scheme-module
  restriction equivalence; no matching extension-by-zero definition.
- `rg` for extensionByZero, jShriek, lowerShriek and extension-by-zero prose in
  Mathlib's module-category sources, upstream WeilConjectures and project
  Sheaf, followed by declaration-focused searches, found the generic module
  presheaf used here, abelian site extension, ringed-space/scheme-module
  results, and the coefficient-category pro-etale lower shriek. I opened the
  actual declaration `ProEtale.localizationLowerShriek` in the exact side
  framework's `FiniteCoefficient/LowerShriek/Open/Defs.lean`: its categories
  are `Sheaf J D` for fixed D, not the node's localized ring-module categories.
  I also read the side framework's
  `ModuleObject/LowerShriek/Defs.lean`, including
  `CondensedRing.linearOpenImmersionLowerShriek` and
  `CondensedRing.openImmersionLowerShriek`: these use internal modules over
  `condensedRingObj Λ X`, with condensed coefficients and scalar transport,
  not this module-presheaf formula over the constant RingCat sheaf.
  The project's `siteExtensionByZeroSheaf` is for AddCommGrpCat on a small
  precoverage site. None supplies the present definition verbatim. I read
  `coord/pefw-upstream-framework.md`; no substitute framework object is added.

No statement correction, new definition node or dependency module is needed.
The sandbox contains only this item's node and its one module. No mathematical
or convention mismatch was found, so I left the Lean and node unchanged and
added this independent reading. The recorded `lean.statement` was compared
verbatim against the source signature, and every source line is at most 100
characters. Source tags and blueprint docstrings are present.

Validation: `scompile.py` from the sandbox compiled the delivered module cleanly
on the server (1.8 s), also compiling its two side dependencies (1.0 s and
2.7 s), with nice 19, two threads and 60 seconds per file. There were no errors
or warnings. No local compiler, global build or modification of upstream/live
Lean was used. My first invocation from the read-only project directory could
not locate the sandbox-relative filename; rerunning from the sandbox resolved
that path error without changing any code.
