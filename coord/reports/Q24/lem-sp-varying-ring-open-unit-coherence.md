## Worker report

The module `Sheaf.AlgebraicGeometry.VaryingRingOpenUnitCoherence` states
`AlgebraicGeometry.ProEtale.VaryingRing.open_unit_coherence`. Its sole theorem has
`by sorry` as its entire proof. No definition, instance, auxiliary theorem, or new
DAG node is introduced. The original node is changed only in `lean`.

The source was read at `literature/stacks-project/sites-modules.tex`,
`lemma-extension-by-zero` (Tag 03DI), beginning at line 2058. It constructs the
ordinary left adjoint and its sheafified direct-sum model. As the node itself
explains, the derived identity normalization and unit calculation are additional
categorical assertions, not claims made by that tag. The docstring contains all
five steps of the node's proof, including both unit equations, the ordinary
compositor calculation, and exact localization.

Hypothesis and clause correspondence:

- Arbitrary commutative rings `R_n` are `(R : ℕ → CommRingCat.{u + 1})`;
  all transition homomorphisms are `(φ : ∀ n : ℕ, R (n + 1) ⟶ R n)`.
  There is no flatness, finiteness, invertibility, or constant-ring assumption.
- An arbitrary scheme is `(X : Scheme.{u})`. The universe convention is exactly
  that of the dependency: the small pro-etale site has object universe `u + 1`
  and Hom universe `u`; coefficient rings and modules have universe `u + 1`.
  No site object/Hom universe equality is imposed.
- The ordinary category is the dependency's `Modules R φ X`, and the unbounded
  derived category is `Derived R φ X`. These are the actual semilinear
  sequence-site system categories, without a cartesianness restriction.
- `L` is `pull R φ (𝟙 X)` and `B` is `extension R φ (𝟙 X)`. The ordinary
  inverse-image identity `e_X` is the inner
  `Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X)`.
  This is exactly the ordinary comparison used in the definition of `gId`.
- The outer `Adjunction.leftAdjointIdIso (moduleJAdj R φ (𝟙 X)) (...)`
  is the node's `b_X`, characterized by preservation of the ordinary unit.
  It is written as the existing Mathlib construction directly, without a new
  definition or an arbitrary isomorphism parameter.
- `J_{1_X}` is the dependency's `J R φ (𝟙 X)`, definitionally the exact derived
  functor of `extension R φ (𝟙 X)`. The node's specified `j_X` is `jId R φ X`;
  its definition is the left-adjoint identity comparison for the specified
  `jAdj` and `gId`, not a newly selected derived adjunction.
- The first conjunct equates `(jId R φ X).hom` with the hom of
  `Functor.mapDerivedCategoryNatIso b_X ≪≫
  Functor.mapDerivedCategoryIdIso (Modules R φ X)`. This is precisely localization
  of `b_X` followed by the exact-derived identity comparison. Equality of hom
  natural transformations also determines equality of the corresponding isos.
- The second conjunct uses `(jComp R φ (𝟙 X) (𝟙 X)).hom` followed by
  `eqToHom` from `J R φ ((𝟙 X) ≫ (𝟙 X))` to `J R φ (𝟙 X)`.
  Its equality proof is only `by simp only [Category.id_comp]`, so it is the
  stipulated equality transport. Simplification handles the dependent
  `IsOpenImmersion` proof argument as well as the morphism equality.
- The right side is `Functor.whiskerLeft (J R φ (𝟙 X)) (jId R φ X).hom`,
  namely `J_{1_X}(j_X)`. Both conjuncts are equalities of natural transformations
  themselves, hence cover every object and morphism of the entire unbounded
  derived category. There is no boundedness or coefficient-evaluation binder.

Dependency declarations read and used, all in
`Sheaf.AlgebraicGeometry.VaryingRingOperations`, namespace
`AlgebraicGeometry.ProEtale.VaryingRing`: `Modules`, `Derived`, `pull`,
`extension`, `moduleAdj`, `modulePId`, `moduleJAdj`, `G`, `J`, `jAdj`, `gId`,
`moduleJComp`, `jComp`, `jId`. I read the dependency node's statement and complete
`lean` record, then the signatures and docstrings of the relevant declarations.
In particular `jComp` is the inverse exact-composition comparison followed by
localization of `moduleJComp`; `jId` is defined through `jAdj`, while `gId`
localizes the displayed ordinary identity.

Mathlib constructions are `CategoryTheory.Adjunction.leftAdjointIdIso` in
`Mathlib.CategoryTheory.Adjunction.CompositionIso`, and
`CategoryTheory.Functor.mapDerivedCategoryNatIso` and
`CategoryTheory.Functor.mapDerivedCategoryIdIso`, supplied by the dependency.
The proof imports additionally retain the stated proof dependencies:
`Sheaf.SixFunctors.OpenTensorNormalizationData`
(`SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`, whose complete
signature and definition were read), `Mathlib.CategoryTheory.Adjunction.Mates`
(`unit_conjugateEquiv_symm`, `conjugateIsoEquiv`), and
`Mathlib.CategoryTheory.Adjunction.Basic` (`Adjunction.comp`, its unit and
hom-equivalence formulas, and `Adjunction.id`). The two proof-only DAG nodes
`lem-sp-exact-derived-transformation-pasting` and
`lem-sp-varying-ring-pullback-unit-coherence` have no recorded Lean declaration
in the read snapshot; they are not needed to type this statement, so no module
for them is invented or imported.

Edge cases checked: the empty scheme, the zero coefficient ring at any or all
indices, arbitrary nonflat transition homomorphisms, and complexes unbounded in
both directions are all retained. The identity is always an open immersion, so
no geometric property binder is required. In an abstract adjunction with a
nonidentity unit, both identity isomorphisms remain the unit-preserving
comparisons; the formula does not replace either one by the identity map.
The natural-transformation equation uses outer whiskering, in the same order
as the ordinary calculation in steps 3 and 4. Equality transport includes the
open-immersion instance; no equality of open-extension functors is asserted by
reflexivity.

Searches executed through `msearch.py Q24 lem-sp-varying-ring-open-unit-coherence`:

- `leanfinder`: “Exact localization of the identity comparison for an open
  extension left adjoint and its identity compositor coherence”. Eight hits,
  including `Adjunction.Localization.ε_app`, `localization_unit_app`, and
  `leftAdjointCompIso_id_comp`; these are generic ingredients, not this result.
- `loogle`: `CategoryTheory.Adjunction.leftAdjointIdIso`. Six hits, including
  its hom/inv formulas and the two ordinary compositor unit lemmas. These
  provide the canonical ordinary construction but do not assert its agreement
  with the specified derived identity.
- `grep`: `leftAdjointIdIso|mapDerivedCategoryNatIso_fach`, subdirectory
  `CategoryTheory`. Five hits in `Adjunction/CompositionIso.lean`, all concerning
  the ordinary construction and unit law; no exact statement match.
- `leansearch`: “Exact derived identity comparison for extension by zero agrees
  with localization of the ordinary adjoint identity”. Eight hits, including
  generic derived/localized adjunctions; none states both required equalities
  for the specified varying-ring operations.
- Local `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `open_unit_coherence` found no existing
  declaration. The prescribed node-ID grep of `lean/WeilConjectures` also found
  none. Broader `rg` for `moduleJComp`, `jId`, and the node ID found the actual
  operations and private implementation lemmas `jId_eq` and `jComp_id` in
  `VaryingRingProperOpenPasting.lean` (lines 1206 and 1257). I read their full
  signatures and proofs. They cover the two constituent calculations separately,
  through private helper definitions; neither is a public declaration of this
  node's combined statement. This delivery adds a single public theorem and
  reuses the canonical constructors directly, without copying those helpers or
  importing the downstream proper/open-pasting module.

Validation: `scompile.py` compiled the delivered file both under its sandbox name
and its actual library module name, cleanly, in 3.0 and 3.1 seconds. The initial
subtype/congruence expression for transport exhausted elaboration heartbeats;
it was replaced by the equivalent explicit `eqToHom` with a dependent-safe
identity simplification. The final file has no compiler warnings. No statement
correction, unusable dependency interface, or disputed statement was found.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
