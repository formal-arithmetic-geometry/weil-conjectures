## Worker report

Item `sk-lem-formal-closed-support`, Q57 stage 2, 2026-10-18.
Repair of return L on immutable head `71b965d0290e`.

`Sheaf.Paper.FormalClosedSupport` now imports
`Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction` and uses its existing
`AlgebraicGeometry.ProEtale.CondensedRing.formalClosedSupport` throughout. This is the
actual functor `formalSupportKernel Λ j ⋙ formalSupportPullback Λ i`, with the kernel of
the canonical open unit and coefficient-compatible inverse image. There is no definition
or theorem named `formalClosedSupport` in this delivery. The theorem is now named
`formalClosedSupportAssertions`: it asserts the paper's two clauses, including the
stratum formula, rather than defining a support functor. Its only postponed proof is
`sorry`. The sections helper retains real composite data.

Hypothesis correspondence:

* `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ]` and
  `[IsCommMonObj Λ]` give a commutative condensed ring. The coefficient sheaf is
  `condensedRingObj Λ X`. The general coefficient scope accepted in the previous return
  is retained, including every admissible coefficient ring.
* `(ℓ : ℕ) [Fact ℓ.Prime]`, `(k : Type u) [Field k]`, `(p : ℕ) [Fact p.Prime]`,
  `[CharP k p]` and `(hpℓ : p ≠ ℓ)` give the standing prime and base-field hypotheses.
* `{Z U X : Scheme.{u}}`, `[X.Over (Spec (.of k))]`, and `LocallyOfFiniteType`,
  `QuasiCompact` and `IsSeparated` on `X ↘ Spec (.of k)` give the standing separated
  scheme of finite type over k. Neither smoothness nor irreducibility is required.
* `i : Z ⟶ X`, `[IsClosedImmersion i]`, `j : U ⟶ X`, `[IsOpenImmersion j]`,
  `[QuasiCompact j]` and `hij : Set.range i.base = (Set.range j.base)ᶜ` give the closed
  immersion and its open complement. The quasi-compactness follows in this Noetherian
  setting, as in the previous packet.
* In clause (2), `{S : Scheme.{u}}`, `u : S ⟶ Z`, `[IsOpenImmersion u]` and
  `L : FormalSupportModules Λ S` give the specified stratum and coefficient module.
* The covering-and-retract antecedent is finite local projectivity: on a pro-étale
  covering `𝒰`, every restriction `(formalSupportPullback Λ (𝒰.f c)).obj L` is a
  `Retract` of `Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n` for some finite n.
  A retract includes inclusion, projection and their split identity. Rank can vary and
  can be zero; no categorical `[Projective L]` is substituted for this local condition.

Conclusion correspondence:

* `rightAdjoint` states clause (1)'s
  `(lowerStar Λ i).mapDerivedCategory ⊣ (formalClosedSupport Λ i j).rightDerivedFunctor`.
* `ordinaryAdjunction` and `counit_normalization` specify the same canonical support
  adjunction that the old packet named directly: composing the counit with the closed
  comparison gives `formalSupportKernelInclusion`. `rightAdjoint_eq` specifies its
  derived adjunction. These are normalization data, not extra assumptions on X or Λ.
* `fiber` is the natural localization triangle of that derived counit and the derived
  unit of the existing `formalSupportPullbackAdjunction Λ j`. Applying exact i^* and
  i^*i_* = id gives exactly the fiber formula of clause (1). The existing
  `formal_closed_support_adjunction` also states this identification for every
  distinguished fiber triangle of that unit.
* `globalRHom` gives the Hom-complex isomorphism for arbitrary A on Z and a K-injective
  representative I on X. Its degree-n component is `ordinaryAdjunction.homEquiv` in
  degrees p and q with p+n=q. These global Hom complexes compute the two RHom objects
  in clause (1), with their canonical normalization.
* In `stratum`, the left input of `derivedHom Λ X` is exactly the degree-zero embedding
  of `(lowerStar Λ i).obj ((openImmersionLowerShriek Λ u).obj L)`, namely a_!L=i_*u_!L.
* The dual is `(ihom L).obj (𝟙_ (FormalSupportModules Λ S))`, the ordinary internal
  module Hom from L to Λ_S, embedded in degree zero. It is the first input to
  `derivedTensor Λ S`. Finite local projectivity makes the derived tensor agree with
  the source's ordinary tensor.
* The other tensor input is obtained by
  `(formalClosedSupport Λ i j).rightDerivedFunctor ⋙
  (formalSupportPullback Λ u).mapDerivedCategory`, namely u^*RΓ_Z K.
* `formalClosedSupportSections Λ T` is
  `Mod.forget (condensedRingObj Λ T) ⋙ Sheaf.Γ (Scheme.ProEt.topology T) Ab.{u + 1}`.
  Its right derived functor is RΓ(T,-). Thus the left side is global RHom_X(a_!L,K)
  and the right side is RΓ(S,L^∨ ⊗ u^*RΓ_Z K), both in derived abelian groups.
* `Nonempty (F ≅ G)` states a natural isomorphism of functors on the entire unbounded
  derived category on X, hence the specified naturality in every K and derived map.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction` supplies
  `FormalSupportModules`, `formalSupportPullback`, `formalSupportPullbackAdjunction`,
  `formalSupportKernel`, `formalClosedSupport`, `formalSupportKernelComparison` and
  `formalSupportKernelInclusion`. Its `formal_closed_support_adjunction` supplies the
  canonical adjunction, Hom comparison, localization triangle and fiber interface.
  Its full source was read locally and confirmed using `scompile.py --source`.
* `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction` remains publicly imported
  only for its existing `closedSupport_lowerStarExact` instance: the statement uses
  exact closed direct image to form `mapDerivedCategory`. The statement no longer uses
  its alternative `closedSupport`, `supportPullback` or support-adjunction definitions.
* The recorded statement dependencies are imported and their full statements read:
  `Sheaf.Paper.CoefficientHeart` / `AlgebraicGeometry.ProEtale.coefficientHeart`, and
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` /
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
  The standing setting is rendered by the explicit theorem binders.
* The published ModuleObject framework and `coord/pefw-upstream-framework.md` were read.
  `ModuleObject.Derived.Hom` provides `derivedHom`; `ModuleObject.Derived.Tensor`
  provides `derivedTensor`; `ModuleObject.LowerShriek.Defs` provides the canonical
  coefficient-compatible `openImmersionLowerShriek`.
* `WeilConjectures.CategoryTheory.ModuleObjects.Free` provides `Mod.finiteFree`.
  Mathlib supplies `Retract`, `ihom`, `DerivedCategory.singleFunctor` and `Sheaf.Γ`.
  The sections helper's additivity is obtained from preservation of binary products.
* The two recorded proof nodes `det-lem-formal-closed-support-derived` and
  `det-lem-formal-closed-support-stratum` have no recorded Lean modules on shared main.
  The theorem docstring retains their complete two-step natural-language proof.

Edge cases checked: zero L and rank-zero retracts; variable rank on disconnected S;
empty S, Z, U or X; identity u; identity j with empty support; identity i with empty
open complement. The construction retains actual extension by zero and the actual
internal dual, and the functor formula covers unbounded K. There is no statement
correction and no STATEMENT-DISPUTED flag.

Searches retained from the original packet:

* `msearch.py ... leanfinder "formal closed support right adjoint fiber formula RHom extension by zero"`:
  generic condensed/internal-Hom matches; no exact theorem.
* `msearch.py ... loogle "CategoryTheory.Adjunction, DerivedCategory, RHom, kernel, fiber"`:
  no exact pro-étale closed-support theorem.
* `msearch.py ... grep "sectionsWithSupport|closedUpperShriek|formal.*closed.*support"`:
  no exact Mathlib/WeilConjectures match.
* `rg` on `lean/Sheaf` and `WeilConjectures/` found the canonical support module but
  no existing declaration for this item. The DAG's recorded searches agree.

Additional repair searches:

* `msearch.py ... leanfinder "finite locally projective sheaf locally a retract of finite free module on a covering"`:
  eight generic finite-presentation/generator hits, including
  `SheafOfModules.IsFinitePresentation`; no module-object finite-local-projective predicate.
* `msearch.py ... loogle "CategoryTheory.Mod.finiteFree"`:
  zero hits, unknown identifier (the published project source supplies this declaration).
* `msearch.py ... grep "FiniteLocallyProjective|finiteLocallyProjective|locally.*direct summand" Algebra/Category/ModuleCat`:
  zero hits. `rg` for `FiniteLocallyProjective|finiteLocallyProjective|IsLocallyProjective`
  over `lean/Sheaf` and upstream WeilConjectures also gave zero hits. The existing finite
  local freeness notion is different; the condition is therefore written directly with
  the existing `Scheme.Cover`, `Mod.finiteFree` and `Retract`, without adding a definition.
* `rg` on the DAG found the detailed stratum node and the finite-retract theorem
  `lem-sf-site-flat-fp-finite-retract`; their statements were read. Neither defines a
  different predicate to substitute here.
* Targeted `rg` over the published ModuleObject framework found and the source reads
  confirmed `derivedHom`, `derivedTensor` and `openImmersionLowerShriek`.

## Repair self-check

The saved report and packet were inspected first. The prescribed initial dry run passed
mechanically (`9db668c175`), but self-check against the return found the name collision
still present, so the packet was substantively repaired before another delivery.

L: the existing declaration at
`Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction` is a **definition of a functor**,
not the paper's two-clause theorem. The existing functor is now imported and reused in
every conclusion, including the stratum formula. The theorem name was changed because
its type is different: it asserts `Nonempty (FormalClosedSupportAssertions Λ i j hij)`
under the standing hypotheses. No second support-functor definition was introduced.
The structure uses the existing kernel comparison/inclusion to specify canonical
normalization, preserving the canonical maps in the earlier accepted clause (1).

Targeted `rg` over shared `lean/Sheaf` and upstream `WeilConjectures` found the existing
functor and no theorem named `formalClosedSupportAssertions`, and confirmed that no
existing whole result includes the stratum clause. The current shared node and sandbox
node agree in all fields other than `lean`; no mathematical node text was changed.
The saved report's older repair claims are superseded by the correspondence above.

Validation: the final `scompile.py Q57 sk-lem-formal-closed-support
lean/Sheaf/Paper/FormalClosedSupport.lean` passed cleanly in the sandbox and final module
paths (8.4 s and 10.7 s), with no warnings. Both the existing support module and this
repaired module are imported together successfully. Signature equality with the node's
`lean.statement`, line width, explicit universes/binders, one theorem `sorry`, absence of
a declaration of the colliding name, and lean-only node changes were checked directly.

## Independent review

This dispatcher-started worker was instructed not to start other agents. This self-check
is not presented as an independent second reading; the delivery is for the maintainer's
independent review.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
