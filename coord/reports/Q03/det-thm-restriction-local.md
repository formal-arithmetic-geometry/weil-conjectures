## Worker report

The delivery states the local factorization theorem in
`lean/Sheaf/Paper/RestrictionLocal.lean`, declaration
`AlgebraicGeometry.ProEtale.restrictionLocal`.  The proof is intentionally `sorry`,
and the module contains no new data definition.  The theorem uses the existing
localizing closure, derived pullback, compactification, lower-shriek and affine-space
constructions.

The coefficient hypothesis is rendered by `hΛ`: either there is a finite intermediate
extension `E : PadicAlgCl.FiniteIntermediateField ℓ` whose condensed ring object is
isomorphic to `Λ`, or `Λ` is isomorphic to
`Profinite.padicAlgClRingObj ℓ`.  The prime, field-characteristic and non-equality
hypotheses are the explicit binders `[Fact ℓ.Prime]`, `[Field k]`,
`[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]`.  The separated finite-type
setting for `X`, `Y`, and `f` is rendered by the explicit `Over`,
`LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsOver` and morphism-property
instances in the theorem header.

For the local chart clause, the binders `v : V ⟶ Y` and `u : U ⟶ X`, together with
`hV`, `hU`, `hv`, and `hu`, render affine open subschemes.  The natural number `d`,
the morphism `i : U ⟶ AffineSpace (ULift (Fin d)) V`, `hi`, and `q : U ⟶ V` render
the affine-space presentation and its closed immersion.  The equations
`i ≫ (AffineSpace.over ... V).hom = q` and `q ≫ v = u ≫ f` render the two equations
`p i = q` and `f u = v p i`, including the `d = 0` case.

The existential `cf`, `hf`, and `Ff` packages a compactification of `f`, its
localizing-closure preservation proof, and the exceptional right-adjoint functor.
For every chart, `huStar` and `hvStar` are the canonical derived pullback lifts into
the localizing closures.  The witnesses `cp`, `hp`, `Fp` and `ci`, `hi'`, `Fi` give
the corresponding compactification-defined right adjoints for the affine-space
projection and the closed immersion.  The `Nonempty` natural isomorphism

`Ff ⋙ u^* ≅ v^* ⋙ Fp ⋙ Fi`

is the Lean rendering of `u^* f^! ≃ i^! p^! v^*` on the localizing categories; the
composition order is chosen so both sides have domain the localizing closure over
`Y` and codomain the one over `U`.  The following universal clause takes every
ambient `K` with `constantModelBoundedConstructible Λ Y K`, chooses its localizing
witness `hK`, and states bounded constructibility of the resulting pulled-back
object over `U`; this renders `u^* f^! K ∈ Dbc(U, Λ)`.  The final existential gives a
finite `Fin n` family of affine open `U a`, proves their pointwise coverage of `X`,
and supplies for each member an affine open `V`, the factorization data, and the two
morphism equations.  Empty families are excluded when `X` has points by the
coverage clause, while the empty scheme and empty charts are still typable.

Dependency declarations used:

* `sk-def-sfb-dc-setting`: `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the recorded `BoundedConstructible` declarations in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
* `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`, especially `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and `ConstantModelBoundedConstructible`.
* `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`, `AlgebraicGeometry.ProEtale.localizingClosureProEtale` and its recorded admissible-coefficient interface.
* `sk-prop-sf-existence`: `Sheaf.Paper.LocalizingExceptionalAdjoint`, `AlgebraicGeometry.ProEtale.CondensedRing.localizingLowerShriek` and `exists_localizingExceptionalAdjoint`.
* `sk-def-sfb-module-derived-pushpull`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`, using `CondensedRing.upperStar`, `Functor.leftDerivedFunctor`, and `derivedUpperStarLowerStarAdjunction`.
* `def-sbc-affine-space`: Mathlib `AlgebraicGeometry.AffineSpace` and `AffineSpace.over`.
* `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.IsOpenImmersion`.
* `def-weil-closed-immersion`: Mathlib `AlgebraicGeometry.IsClosedImmersion`.
* `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
* `def-weil-proper-morphism`: Mathlib `AlgebraicGeometry.IsProper` and its separated/finite-type fields.
* `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
* `sk-def-sfb-qlbar-condensed`: the existing `Profinite.padicAlgClRingObj` construction imported from the condensed ell-adic coefficient module; no duplicate definition is introduced.

Edge cases checked were `d = 0` (the `ULift (Fin 0)` affine-space projection is
accepted by Mathlib), empty `U` and empty complements, the empty scheme `X`, a point
scheme, zero derived objects, and rank/characteristic hypotheses with `ℓ` distinct
from `ringChar k`.  The finite-family coverage clause remains meaningful in all of
these cases.

Searches made:

* `msearch.py ... leanfinder "local factorization exceptional inverse image f star affine chart bounded constructible"`: eight Mathlib hits, all affine-open or constructibility utilities; no matching theorem.
* `msearch.py ... loogle "CategoryTheory.Adjunction.comp, AlgebraicGeometry.AffineSpace, Compactification.BoundaryCompactification"`: zero hits (the qualified compactification name is not a Loogle identifier).
* `msearch.py ... grep "restrictionLocal|exceptional.*inverse|localizingLowerShriek" Mathlib/CategoryTheory`: zero hits.
* `rg -n "restrictionLocal|localizingLowerShriek|BoundaryCompactification"` over the named Weil source and shared `lean/Sheaf`: related compactification and exceptional-adjoint declarations were found, but no declaration of this theorem.
* The repository-wide node search found no existing `det-thm-restriction-local` Lean declaration.  Therefore `existing` is false and no new definition node is required.

The module was compiled with `python3 /home/ubuntu/weil-launcher-nt/scompile.py
Q03 det-thm-restriction-local lean/Sheaf/Paper/RestrictionLocal.lean`; both the sandbox
and library checks completed with exit code 0 and no warnings.

## Second reading by Q03

I reread the source statement and checked that each coefficient, scheme, morphism,
chart, factorization equation, functor-isomorphism, constructibility, and finite-cover
clause has a corresponding explicit Lean binder or conjunct.  The only elaboration
repair was orienting the functor composition as `Ff ⋙ u^*`, which is forced by the
source and target categories.  No source hypothesis was dropped, and no additional
mathematical assumption was introduced beyond the standing typeclass presentation
needed to render the stated separated finite-type setting.

## Maintainer reviewer fix (2026-10-18)

The delivered statement packaged the exceptional inverse images existentially
(`∃ cf hf Ff, Nonempty (… ⊣ Ff) ∧ …` and, per chart, `∃ … cp hp Fp ci hi' Fi`).  That
only asserts the factorization for *some* compactification of `f` (and of `p`, `i`),
which is weaker than the node: `f^!`, `p^!`, `i^!` are the right adjoints of
sk-prop-sf-existence for the chosen compactification, and the consumers
(det-thm-restriction-glue step 4, sk-thm-restriction) apply the item to an arbitrary
given compactification and right adjoint.  Without a compactification-independence
statement they could not use the existential form.  The fix takes `cf`, `hf`, `Ff`,
`_adjf` as theorem arguments (the convention of `rationalRestrictionGlue` and
`rationalExceptional_preserves_constructibleFiniteTor`) and universally quantifies
`cp`, `hp`, `Fp`, `adjp`, `ci`, `hi'`, `Fi`, `adji` in the chart clause.  The pullback
membership proofs `huStar`, `hvStar` stay existential (propositions).  Everything else is
unchanged; the docstring now lists the eleven proof steps of the node.  Compiled clean
with nt_compile.py.
