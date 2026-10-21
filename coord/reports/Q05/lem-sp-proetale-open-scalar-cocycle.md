## Worker report

The module `Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle` states
`AlgebraicGeometry.ProEtale.proEtaleOpenScalarCocycle`, with `sorry` as its entire
proof. It introduces no definitions and changes only the item's `lean` record.
The declaration docstring gives all five proof steps of the node, including
restriction/pullback coherence, the unit normalization of the scalar associator,
mate pasting, and cancellation of the prescribed open coordinate changes.

Hypothesis and clause correspondence:

- A fixed prime ell is `(ℓ : ℕ) (hℓ : ℓ.Prime)`.
- The finite commutative unital coefficient rings are `{A B C : Type u}`,
  `[CommRing A] [CommRing B] [CommRing C]` and `[Finite A] [Finite B] [Finite C]`.
  `CommRing` supplies the unit; no `Nontrivial` assumption excludes the zero ring.
- Annihilation by powers of ell is `hA : ∃ n : ℕ, (ℓ : A) ^ n = 0`, and likewise
  `hB` and `hC`. For a unital ring this is equivalent to ell^n killing the entire
  ring: evaluate at one in one direction, and multiply by any element in the other.
  Allowing exponent zero includes only the zero ring, already killed at exponent one.
- The specified unital maps are `(φ : A →+* B) (ψ : B →+* C)`. Direct scalar
  extension uses their actual composite `ψ.comp φ`.
- Arbitrary schemes and the open immersion are `{U Z : Scheme.{u}}`,
  `(j : U ⟶ Z) [IsOpenImmersion j]`. There is no quasi-compactness hypothesis.
- The arbitrary input is `(M : proEtaleDerivedCategory U A)`, the full ordinary,
  uncompleted intrinsic constant-ring module derived category used by the recorded
  scalar and open comparison declarations. It has no cohomological restriction.
- `T_T^{A,B}` is exactly `scalarExtensionFunctor φ T`; the specified alpha is
  `(scalarExtensionFunctor_composition φ ψ T).hom.app E`, not an arbitrary iso.
- `j_!^A` is `(sfIntrinsicExtensionByZero j A).mapDerivedCategory`:
  the recorded sectionwise sheafified open extension, applied termwise and descended.
- Every `e` in the equation is exactly `(reductionOpenScalarIso ... j).hom.app ...`.
  Its definition transports the normalized `openScalarIso` through the specified
  `reductionOpenModel` coordinate isomorphisms. No new comparison is selected.
- The left side is alpha at `j_!^A M`, followed by `e^{A,C}` at M, written
  `alpha_Z.hom.app (jA.obj M) ≫ eAC.hom.app M` in Lean's diagrammatic order.
- The right side is `T_Z^{B,C}(e^{A,B}_M)`, then `e^{B,C}` at `T_U^{A,B} M`,
  then `j_!^C(alpha_U at M)`, expressed by the two `.map` calls and middle `.hom.app`.
  Both sides go from `T_Z^{B,C}(T_Z^{A,B}(j_!^A M))` to `j_!^C(T_U^{A,C} M)`.
- No boundedness, constructibility, coefficient flatness, finite projective dimension,
  invertibility of ell on a scheme, or quasi-compactness of j is imposed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, and `finiteCoefficientRingSheaf` describe the
  finite coefficient framework; the operations below use its published intrinsic
  constant-ring coordinates `Scheme.proEtaleDerivedCategory` from
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingComparison`, `proEtaleConstantRingPullback`,
  `proEtaleConstantRingAdjunction`, and `proEtaleConstantRingDerivedPullback`
  fix the geometric operations used inside the recorded open comparison.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor` and
  `scalarExtensionFunctor_composition`, whose unique K-flat balancing
  characterization is `scalarExtensionFunctor_composition_existsUnique`.
- `Sheaf.SecSmoothPurity.ReductionDirectImageComparison`:
  `reductionOpenScalarIso` and its defining coordinate change `reductionOpenModel`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero` and `sfIntrinsicModuleEquivalence`.

The proof-only imports include every recorded proof dependency: the normalized
`SheafOfModules.sheafRingDerivedCoefficientAdjunction`; the canonical
`Scheme.proEtaleRingRestrictionDerivedPullback` and
`Scheme.proEtaleRingSheafChangeAdjunction`; the unit-normalized
`SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`;
Mathlib `Adjunction.comp`, `SheafOfModules.restrictScalars`, `Localization.lift`,
`Localization.liftNatTrans` and `Localization.natTrans_ext`,
`unit_conjugateEquiv_symm`, `mateEquiv_vcomp`, `mateEquiv_hcomp`, and
`conjugateEquiv` from the recorded Mathlib modules.

Edge cases checked mathematically before writing: U empty (all maps are in the
zero source category), Z empty, j the identity, either coefficient map the identity,
zero coefficient rings, M zero, arbitrarily unbounded M, and nonflat coefficient
maps such as Z/ell^2 -> F_ell. None is excluded by the binders, and the normalization
and cancellation proof applies in each case. The sole universe u is the published
scheme/coefficient convention: the site has objects in u+1 and morphisms in u;
coefficients are lifted internally to u+1. No equality of site universes is imposed.

Searches for an existing statement:

- `msearch.py ... leanfinder "Derived extension of scalars commutes coherently with
  extension by zero for a tower of coefficient rings"`: eight hits, including
  `ModuleCat.extendScalarsComp` and `ModuleCat.extendScalars_assoc`; these are ordinary
  module scalar associators, with no pro-etale normalized open comparison.
- `msearch.py ... loogle '"extendScalars", "comp"'`: nine hits, including
  `ModuleCat.extendScalarsComp` and `ModuleCat.homEquiv_extendScalarsComp`;
  again no matching open cocycle.
- `msearch.py ... leansearch "Derived open extension by zero scalar extension
  comparison satisfies the coefficient cocycle"`: eight unrelated hits on Lie algebra
  extensions and hom-complex cocycles; no match.
- `msearch.py ... grep
  'openScalar.*(comp|assoc|cocycle)|extensionByZero.*scalar|shriek.*scalar'`:
  zero Mathlib hits.
- `rg -n 'openScalar.*(comp|assoc|cocycle)|reductionOpenScalarIso|
  lem-sp-proetale-open-scalar-cocycle' lean/WeilConjectures lean/Sheaf`:
  the reduction comparison definition and its direct-image use, plus etale open scalar
  coherence declarations. The latter concern etale sheaf complexes, not these ordinary
  pro-etale derived categories or the recorded normalized maps.
- `grep -rn 'lem-sp-proetale-open-scalar-cocycle' lean/WeilConjectures`: no hits.
- `rg` of `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`
  for the final declaration name found no existing declaration.

Read the actual source proof at blueprint main-20261015,
`sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.proof.md`,
Steps 1 and 4, the item's five expanded proof steps, all five statement-dependency
records and their relevant signatures/docstrings, and `coord/pefw-upstream-framework.md`.
No repair note exists for this item. No statement fault or dispute was found.

Validation: `scompile.py Q05 lem-sp-proetale-open-scalar-cocycle <module>` passed
both the sandbox and library-path checks in 3.1 seconds each, without warnings or
errors. No global build or direct git operation was performed.

## Second reading by Q05

The dispatcher explicitly forbids starting another agent, so this is the writing
worker's second pass; the maintainer's independent review remains external.
Reopened the completed theorem and original node. Matched every coefficient,
prime and annihilation hypothesis, the two actual ring maps, arbitrary open j,
and arbitrary M to the binders above. Recomputed the common source and target
of the two sides, checking that Lean's `≫` reverses the paper's displayed
composition notation. Verified that alpha is the K-flat normalized comparison,
that every e is `reductionOpenScalarIso`, and that the open functor is the
sectionwise sheafified one rather than merely the adjoint presentation.
No mismatch was found, and no statement correction or dependency module is needed.
