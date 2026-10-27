## Worker report

Item: `lem-sf-reindexed-sheaf-bidual-equivariance`. The delivery states
`SheafOfModules.reindexed_bidual_equivariance` in
`Sheaf.CategoryTheory.ReindexedSheafBidualEquivariance`. Its only proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The node is unchanged outside `lean`.

Sources read: the entire item and every statement-dependency record; the source
signatures/docstrings recorded below; Stacks `sites-modules.tex`, section 04TT,
including the localized-Hom formula, restrictions, evaluation, and lemma 03EM;
`WeilConjectures/WeilSheaf/Dual.lean`, `dualStr` and `dual`. The latter uses the
inverse source structure and the forward target structure, exactly the convention
used here. The five-step proof in the item is rendered in the theorem docstring.
There is no repair note for this item.

Hypotheses and clauses, individually:

- The site is `{C : Type u} [Category.{u} C] (J : GrothendieckTopology C)`.
  Rings and modules also have universe `u`. This is the stipulated smallness in
  the coefficient universe, not an extra equality on a general large site.
  The size-convention dependency is metatheoretic and has no Lean declaration.
- The invertible functor with chosen inverse is `(τ : C ≌ C)`. The two assumptions
  `[τ.functor.IsContinuous J J] [τ.inverse.IsContinuous J J]` express preservation
  of covering sieves in both directions. For equivalences this is equivalent to
  cover preservation: Mathlib `CoverPreserving.of_isContinuous` gives one direction,
  and `Functor.isContinuous_iff_coverPreserving` applies to the representably flat
  equivalence for the other. No pullbacks or terminal object of C are assumed.
- The commutative ring sheaf is `(R : Sheaf J CommRingCat.{u})`. The repeated
  `sheafCompose ... (forget₂ CommRingCat RingCat)` only forgets commutativity for
  Mathlib's module interface. The binder `s` is a ring-sheaf isomorphism from its
  reindexing along `τ.functor` to itself. A ring isomorphism between commutative
  rings is the same isomorphism in CommRingCat; no coefficient automorphism is fixed.
- `M : ringedSiteModules.{u} ...` is the recorded general-site module category.
  `(pushforward (F := τ.functor) s.inv)` is the actual reindexing endofunctor T:
  the sections at U are M(τ U), restrictions are along τ(f), morphisms are
  reindexed componentwise, and R(U) acts through the component of s inverse.
  This is Mathlib's existing construction, not an arbitrary endofunctor variable.
- `(a : T.obj M ≅ M)` is exactly the required R-linear structure isomorphism.
  The old TR-action is s-semilinear because T restricts scalars by s inverse.
- `homObj (R := R) M (unit _)` is D(M). The repeated `homObj` gives D²(M).
  These are the recorded localized-Hom objects; `unit` is R as its own module.
- The first conjunct gives the canonical comparison, in coefficient-identified
  coordinates: `q : T(D(M)) ≅ Hom_R(TM,R)`. The quantified formula over EVERY
  U, V, f : V -> U, local map μ, and section x states that its component is
  `s_V (μ_(τ f)(x))`. Undoing the specified coefficient identification s gives
  exactly the node's TR-linear comparison `TD(M) ≅ Hom_TR(TM,TR)`, whose formula
  is μ_(τ f)(x). Thus this is the same comparison written with all objects in
  Mod(R), not a different inverse-image comparison. The isomorphism is determined
  by the formula: local Hom maps are determined by their components and arguments.
- The existential `b : T(D(M)) ≅ D(M)` comes with the equality at every slice
  `b_U(μ)_f(x) = s_V(μ_(τ f)(a_V^{-1}(x)))`. This is precisely
  `b(μ)=s ∘ μ ∘ a^{-1}` in localized coordinates.
- The existential `c : T(D²(M)) ≅ D²(M)` comes with the equality at every slice
  `c_U(ζ)_f(lam) = s_V(ζ_(τ f)(b_V^{-1}(lam)))`. This is precisely the
  twice-induced structure `c(ζ)=s ∘ ζ ∘ b^{-1}`.
- These are existentially stated canonical isomorphisms, not unconstrained maps
  or objects chosen from a sorried mere existence theorem. Each is forced by its
  all-slices formula. Existence and all the asserted properties form the ONE node
  theorem; no definition takes data from its postponed proof.
- `bidual M` is the existing evaluation δ, defined from actual tensor-Hom data.
  Its source `PresheafOfModules.bidual_app_app_apply` is the node's formula
  `δ_U(x)_f(lam)=lam_id(x|V)`. Mapping `bidual M` by the actual pushforward
  reindexes this identical formula at τ U, τ V, τ f. This accounts for the
  reindexing/evaluation clause without assuming its compatibility as a hypothesis.
- The equation `T.map (bidual M) ≫ c.hom = a.hom ≫ bidual M` is exactly
  `c ∘ Tδ = δ ∘ a`, since Lean composition is written from left to right.
- The next existential supplies an ACTUAL morphism of the recorded fixed-pair
  category, from `IsoAlgebra.mk M a` to `IsoAlgebra.mk D²(M) c`, whose forgetful
  image is δ. The fixed-pair category is not replaced by an equation-only alias.
- The final `∀ [IsIso (bidual M)]` makes invertibility conditional, leaving
  arbitrary M allowed in the preceding clauses. Its equation
  `T.map (inv δ) ≫ a.hom = c.hom ≫ inv δ` is the required `a ∘ T(h)=h ∘ c`.
  The subsequent `e` is an actual fixed-pair isomorphism, with forward forgetful
  image δ and inverse forgetful image `inv δ`, so its inverse is specifically h.
- No finite generation, local freeness, reflexivity, trivializing cover, or
  invariant-cover hypothesis appears anywhere.

Dependency declarations used:

- `def-weil-size-convention`: explicit `universe u`; no declaration is prescribed.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`; its entire general-site abbreviation
  and docstring were read.
- `def-pur-sheaf-hom`:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`; read its complete general signature and docstring,
  the underlying `PresheafOfModules.homObj` and `restrictOver`, and its functoriality.
  Importing the existing `...Sheaf.Bidual` exposes it and the canonical
  `SheafOfModules.bidual`. Read that declaration and its presheaf evaluation formula.
- `def-weil-endofunctor-fixed-pair-category`:
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`,
  `CategoryTheory.Endofunctor.IsoAlgebra`, `.mk`, `.forget`; also read the exact
  underlying Mathlib `Endofunctor.Algebra.Hom` compatibility field.
- Proof dependency `def-pur-localized-ringed-site`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `.over`, `.Hom.over`, `.overMap`, `.overFunctorMap`;
  read their definitions and docstrings. This module is a public import because
  its `pushforward` is itself used in the statement. No separate private proof
  import is necessary: all the node's proof dependencies are already exposed.

Edge cases checked mathematically before writing and on the second pass:
empty C; zero coefficient ring; zero M; identity τ and s; nontrivial coefficient
automorphism on a one-object site; non-free and non-reflexive M; an invertible
underlying δ; a site with no selected invariant trivialization. In the one-object
semilinear case the scalar action is through s inverse, so a inverse is correctly
used in b. The inverse equation is the reverse intertwining equation, with the
composition direction checked against `Endofunctor.Algebra.Hom.h`.
The zero/non-reflexive cases require no unconditional IsIso δ.

Searches actually run through the prescribed msearch.py wrapper:

- LeanFinder: "Bidual evaluation of sheaves of modules is equivariant under site
  reindexing and semilinear contragredient automorphisms". Eight results include
  `SheafOfModules.unitHomEquiv_symm_comp`, `unitHomEquiv_comp_apply`,
  `freeHomEquiv_symm_comp`, `map_ιFree_mapFree_hom`, and related free-module maps;
  none states this lemma.
- Loogle: `SheafOfModules.homObj, SheafOfModules.pushforward,
  CategoryTheory.Endofunctor.IsoAlgebra`. Zero results; reports unknown identifier
  `SheafOfModules.homObj` (that declaration is upstream, not in Mathlib's index).
- LeanSearch: "Sheaf of modules bidual evaluation compatible with reindexing by
  a site automorphism". Eight results include ordinary `Module.Dual.eval`,
  `Module.evalEquiv`, `SheafOfModules.pushforwardSections`, `evaluation`,
  and `Equivalence.sheafCongr.functor_map_val_app`. No full statement match.
- Mathlib grep: `bidual|doubleDual|contragredient` in `Algebra/Category/ModuleCat`.
  Zero results.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `reindex|bidual|doubleDual|double_dual|contragredient`: found existing ordinary
  biduality, special Weil duality, and `TwistedActionRingedSite` comparisons.
  Read the latter's data and comparison statement: it requires a larger action-site
  presentation and pullbacks, and does not state arbitrary ringed-site bidual
  equivariance. No duplicate was used. The ordinary bidual and reindexing
  constructions WERE reused, as above.
- Direct rg for this node id under `lean/WeilConjectures`: no existing statement.
  Direct rg for `reindexed_bidual_equivariance` in both source libraries and
  `dag/lean_names_upstream.json`: no declaration-name collision.

Validation: prescribed scompile.py compiled both the sandbox module and its library
module name cleanly, in 2.3 and 2.1 seconds respectively. Explicit `(R := R)`
arguments remove ambiguity in nested internal Hom; all universes and variables
are explicit and autoImplicit is disabled. There are no diagnostic commands and
no definitions or proved auxiliary theorems. No statement fault or disputed claim
was found.

## Second reading by NE

This is the delivering worker's second reading, not an independent agent review;
the maintainer supplies the independent review. I reopened the node, complete
module, and `Endofunctor.Algebra.Hom` signature. I checked each binder and every
conjunct as mapped above, especially s inverse in scalar restriction, a inverse
in b, b inverse in c, quantification over EVERY slice arrow rather than only global
sections, and the forward/inverse underlying maps of the fixed-pair isomorphism.
The comparison is written after coefficient transport; reversing that transport
recovers exactly the TR comparison stated in the node. The existential b and c
are uniquely forced by their component formulas. The final IsIso binder scopes
only the inverse conclusion. No local freeness or invariant cover was introduced.
The implementation corrections were the reserved lambda identifier and explicit
ring parameters for nested internal Hom; neither changed the mathematical statement.
