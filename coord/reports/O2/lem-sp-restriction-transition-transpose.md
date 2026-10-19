## Worker report

The module `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` states
`AlgebraicGeometry.ProEtale.restrictionTransitionTranspose`, with `sorry` proof.
Three real helper definitions give the scalar transpose, the mixed compact-support
transpose, and the identity-coefficient input in canonical adjunction coordinates.
No statement correction or new DAG node is needed.

Hypothesis-by-hypothesis correspondence:

- The field and characteristic are `k`, `[Field k]`, `[CharP k pchar]`, `hp : 0 < pchar`;
  the different prime is `ℓ`, `[Fact ℓ.Prime]`, `hℓ : pchar ≠ ℓ`.
- The three schemes are `X Z Y : Scheme.{u}`. Their `Over (Spec (.of k))` structures,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structure maps express precisely
  separated finite type over k. The morphisms f, j and h have the corresponding `IsOver`
  instances. `[IsOpenImmersion j]`, `[IsProper h]`, and `hf : j ≫ h = f` give the supplied
  compactification, rather than selecting another one.
- `A B : Type u`, `CommRing`, `Finite`, `hA`, `hB` and `φ : A →+* B` give finite
  commutative rings killed by powers of ℓ and an arbitrary unital coefficient map.
  There is no flatness, surjectivity or finite-projective-dimension hypothesis.
- `K : proEtaleDerivedCategory X A` and `L : proEtaleDerivedCategory X B` are objects
  of the ordinary uncompleted intrinsic constant-ring module derived categories.
  `hKb` and `hLb` assert finite cohomological support, equivalently boundedness over ℤ.
  `hKc` and `hLc` use the recorded intrinsic constructible-sheaf predicate in every degree.
  `hKt` and `hLt` are the recorded finite Tor-amplitude predicates. Thus both inputs
  have exactly the node's Dctf membership, without imposing etale origin.
- `t : K ⟶ (scalarRestriction φ X).obj L` is any derived morphism.

Clause-by-clause correspondence (composition in Lean is left to right):

1. `reductionCompactSupport R j h` is exactly `j_!` followed by `Rh_*`; its open
   factor is the recorded `sfIntrinsicExtensionByZero` descended termwise. T is
   `scalarExtensionFunctor φ W`, Res is `scalarRestriction φ W`, and epsilon is
   the counit of `proEtaleRingDerivedExtensionAdjunction` at the actual constant-ring map.
2. `restrictionTransitionScalarTranspose φ W t` is the inverse of that canonical
   adjunction's Hom equivalence, so is precisely t-sharp, with its specified tensor
   normalization. `restrictionTransitionMixedTranspose` first maps t by F_A, then
   applies the specified d_f, then takes that same scalar transpose over Y.
3. The first conjunct is exactly `(d_f(L) F_A(t))^sharp = F_B(t^sharp) b_f(K)`.
   The map b_f is the published `reductionDirectImageComparison`, never a newly
   chosen map or an assumed mate. Its definition retains both the proper-counit
   and open-tensor normalizations from det-sp-reduction-direct-image.
4. The second conjunct quantifies over every ambient B-object H and states exactly
   `T_Y(d_f(H)) ≫ epsilon_Y(F_B H) = b_f(Res_X H) ≫ F_B(epsilon_X H)`.
   In particular it makes no boundedness or Tor-amplitude assertion about Res_X H.
   The final conjunct states invertibility of b_f only on the supplied Dctf K.
5. The third conjunct gives naturality in both inputs: precompose t by u and
   postcompose by Res(v); the resulting transpose is T_Y(F_A(u)), the original
   mixed transpose, then F_B(v). The arbitrary t binder gives the asserted scope
   in the third variable as well; no special representative of t is selected.
6. The fourth conjunct quantifies over a further finite commutative ℓ-primary C
   and arbitrary ψ : B →+* C. Its first equality gives successive scalar transposes
   versus the composite transpose after `scalarExtensionFunctor_composition` on X.
   Its second gives successive mixed compact-support transposes versus the direct
   one after that very tensor associator on Y. The input restriction identification
   is the published termwise `sfDerivedCoefficientRestrictionComp`. Its third equality
   writes the full b cocycle with alpha on both K and F_A K. All scalar-counit
   assertions remain ambient, including H and its scalar restrictions.
7. The fifth conjunct says identity coefficients give F_A(s), for every s : M → N.
   `restrictionTransitionIdentityInput` uses the scalar unit followed by restriction
   of the multiplication unitor and s. This is exactly s under identity restriction,
   not an arbitrary lifted map. Precomposition with the inverse of the normalized
   scalar identity unitor identifies the output source with F_A M. The sixth conjunct
   specializes to the identity morphism and says the output is identity on F_A M.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` records the setting;
  this statement uses the given compactification and writes the setting binders explicitly.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules` and the
  constant-ring realization vocabulary; the intrinsic ordinary derived category is the
  same shared `Scheme.proEtaleDerivedCategory` used by the scalar and compact-support nodes.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`: `Scheme.IsConstructibleProEtaleModuleSheaf`;
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`: `Scheme.HasFiniteProEtaleTorAmplitude`.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `ProEtale.scalarExtensionFunctor`,
  `scalarExtensionFunctor_composition`, `scalarExtensionFunctor_identity`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used by the published scalarRestriction.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction` gives the normalized Hom equivalence;
  the concrete canonical scalar adjunction reused here is
  `Scheme.proEtaleRingDerivedExtensionAdjunction` from `Sheaf.Paper.FourCorners`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingComparison`, `proEtaleConstantRingDerivedPullback`;
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero` (the exact open factor).
- `Sheaf.SecSmoothPurity.ReductionDirectImage`: `ProEtale.reductionDirectImage_isIso`,
  `reductionDirectImage_cocycle`; its comparison module supplies
  `reductionCompactSupport`, `reductionDirectImageComparison`, `reductionOpenScalarIso`.
- The repaired restriction node below supplies `intrinsicCompactSupportRestriction`.
  It reuses `Scheme.sfOpenRestriction` and `sfDerivedCoefficientRestrictionComp` from
  `Sheaf.Paper.SfCompactSupportRestrictionOfScalars`, and
  `Scheme.proEtaleRingRestrictionDerivedDirectImage` from
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.
- The remaining recorded proof modules are imported without `public`:
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`,
  `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`,
  `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`,
  `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
  Their normalized adjunction-composition, constant-section, open and K-injective
  interfaces are the seven-step proof plan; every step is included in the theorem docstring.

Edge cases checked before writing:

- Zero complexes, zero morphisms, zero coefficient rings and empty schemes are allowed.
  No nonzero, nonempty or positive-degree assumption was introduced.
- Identity coefficient homomorphisms and identity t have explicit normalized equations.
- Nonflat finite maps, for example Z/ℓ² → Z/ℓ, are allowed. A restricted B-object may
  have infinite A-Tor amplitude; the ambient counit binder deliberately has no Tor bound.
- All cohomological degrees are integers; finite support permits the empty support and
  arbitrary bounded intervals. The common Tor bound is the recorded predicate, not
  independent bounds for separate test sheaves.
- The pro-etale site retains object universe u+1 and morphism universe u; coefficients
  are lifted internally to u+1. No site-universe equality or arbitrary coefficient
  transport is imposed. The intrinsic dependency module and the final consumer compile
  together, verifying the repaired interface at precisely those universes.

Searches for an existing statement:

- msearch leanfinder, `Adjunction transpose compact support mixed coefficients restriction
  scalar extension`: 8 generic ModuleCat scalar-adjunction hits, no geometric derived match.
- msearch loogle, `"homEquiv", "naturality"`: 12 generic adjunction naturality lemmas;
  none identifies these specified proper/open comparisons or their coefficient cocycles.
- msearch leansearch, `Adjunction transpose of a natural transformation mate commutes with
  arbitrary mixed coefficient morphisms`: 8 generic counit/mate results, no exact match.
- msearch grep, `(compactSupport|reductionDirectImage).*(transpose|Adjunction)`: no hits.
- rg in upstream WeilConjectures for `(compactSupport|shriek).*(transpose|scalar)` and
  `restrictionTransitionTranspose`, and grep for the node id: no matching statement.
- rg in project Sheaf found the existing scalar, reduction and fixed/intrinsic restriction
  constructions used above, but no statement of this node. The intrinsic module is an
  interface repair rather than a second definition of compact support or scalar extension.

Source read directly: sites-cohomology.tex, lemma-adjoint and
lemma-derived-pushforward-composition (Tags 07A6 and 0D6E); the current blueprint's
sk-lem-sp-reduction-direct-image.md, including its nonflat coefficient cocycle.
No STATEMENT-DISPUTED issue was found.

## Dependency modules

`lem-sf-compact-support-restriction-of-scalars` is repaired under §1(B) by
`Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`. Its recorded
`ProEtale.compactSupportRestrictionIso` acts on fixed ModuleCat sheaves, so cannot be
applied to the intrinsic constant-ring objects in b_f. The already published
`Scheme.sfCompactSupportRestriction` supplies the intrinsic open comparison, but uses
the sectionwise `proEtaleConstantDerivedDirectImage` model, whereas b_f uses the
identified-coefficient `directImageConstantPush` model. Those right-derived functors
are not definitionally equal. The repair uses the existing `sfOpenRestriction` and the
inverse of the existing `proEtaleRingRestrictionDerivedDirectImage`, so constructs exactly
the node's specified open/proper composite in the coordinates used by b_f. Both factors
retain their section/unit and K-injective normalizations. No arbitrary comparison,
bare Nonempty choice, downstream mate hypothesis or second compact-support functor is added.
`intrinsicCompactSupportRestriction_comp` states the node's coefficient-composition
clause with the original separated finite-type, compactification and invertible-prime
hypotheses. Both original intrinsic and fixed interfaces remain available without edits.
Only this dependency node's lean field changes, with the explanatory note. The two files
compile separately in dependency order and the final theorem exercises the repaired d_f
against the existing b_f, scalar adjunction, composition maps and identity unitor.

Validation: both modules compiled cleanly through scompile.py. The first dry run
found a truncated JSON signature (a named-argument `:=` had been mistaken for
the proof delimiter). The record now contains the entire signature verbatim;
the Lean statements themselves required no change.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
