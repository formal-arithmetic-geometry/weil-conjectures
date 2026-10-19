## Worker report

The module `Sheaf.Algebra.Homology.AlgebraicLocalDuality` states
`DerivedCategory.algebraic_local_duality`, with one `sorry` proof and no new definitions.
It renders the node unchanged, including existence of a hull and the assertion for
**every** hull. The source was read in `literature/stacks-project/dualizing.tex`:
lemma-special-case-local-duality (0AAK), lemma-injective-hull (08Y3), and
lemma-local-cohomology-noetherian (0955). No completeness assumption is introduced.

Hypothesis and conclusion correspondence:

- Nonzero commutative Noetherian local A: `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`. The last class already supplies `Nontrivial A`;
  an explicit extra binder was removed after the overlapping-instance compiler warning.
- The maximal ideal is `IsLocalRing.maximalIdeal A`; κ=A/m is
  `IsLocalRing.ResidueField A`, with its canonical A-module structure.
- Ω∈D(A): `(Ω : DerivedCategory (RingSiteModules A))` and
  `[HasDerivedCategory.{u} (RingSiteModules A)]`, using the dependency's exact ordinary
  one-object-site presentation and derived-category universe.
- Normalized algebraic dualizing: `hΩ : IsNormalizedAlgebraicDualizing A Ω`, retaining
  all three dualizing conditions and residue-field normalization through the recorded predicate.
- Existence of a hull: the first conjunct quantifies `∃ (E : ModuleCat.{u} A)
  (ι : IsLocalRing.ResidueField A →ₗ[A] E)`. `Function.Injective ι` is the injection,
  `Injective E` is injectivity, and `∀ N : Submodule A E, N ≠ ⊥ →
  N ⊓ LinearMap.range ι ≠ ⊥` is exactly essentiality as stated in the node.
- Every such hull: the second conjunct universally quantifies a fresh E and ι and assumes
  precisely the same injection, injectivity and essentiality properties. The result is not
  limited to the existential witness of the first conjunct.
- Every finitely generated module: `∀ (M : ModuleCat.{u} A) [Module.Finite A M]`.
- Every integer i≥0: `(i : ℕ)` ranges over exactly the nonnegative degrees; the Ext
  cohomological degree is `-(i : ℤ)`, including zero with no off-by-one shift.
- Ext is the evaluated cohomology of `derivedInternalHomOfUniverses.{u,u,u,u}` on
  `(op ((singleFunctor (RingSiteModules A) 0).obj (algebraicDualizingModuleSheaf A M)), Ω)`.
  Evaluation `.val.obj (op ⟨PUnit.unit⟩)` recovers the A-module from the shared one-object
  ringed site. This is the same RHom implementation used by the normalized predicate's
  `SignedRingedHom.hom`, whose definition was opened.
- Completed Ext: `AdicCompletion (IsLocalRing.maximalIdeal A)` applied to that module.
  Mathlib's definition is compatible quotient sequences modulo `m^n • ⊤` for n:ℕ;
  its n=0 quotient is zero, so deleting it gives exactly the node's n≥1 inverse limit.
- Γ_m(N) is the existing `ModuleCat.idealPowerTorsion`, constructed from
  `Ideal.primaryComponent`. Its n≥0 convention equals n≥1: if n=0 annihilates an
  element, that element is zero and is also annihilated by m. Local cohomology is
  `((ModuleCat.idealPowerTorsion (IsLocalRing.maximalIdeal A)).rightDerived i).obj M`.
- The right side is the A-module of `→ₗ[A] E` maps from that local cohomology object.
  `Nonempty (... ≃ₗ[A] ...)` asserts an A-linear isomorphism, not mere equality of
  dimensions or a chosen arbitrary comparison morphism.

Dependency declarations read and used:

- `Sheaf.Algebra.Homology.AlgebraicNormalizedDualizing`:
  `CategoryTheory.algebraicDualizingModuleSheaf`,
  `DerivedCategory.IsNormalizedAlgebraicDualizing` (and its constituent
  `DerivedCategory.IsAlgebraicDualizing`). Their full definitions and docstrings were opened.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution` was also read for the dependency's second clause.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, the finite-generation predicate.
- `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`:
  `ModuleCat.idealPowerTorsion`, `ModuleCat.idealPowerTorsion_additive`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`; the underlying module category is the
  recorded `CategoryTheory.RingSiteModules` from `RingHomExtensionDefs`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`.
- The recorded, available proof dependencies are imported without `public`:
  `CoherentRHomFiniteInjectiveDimension`, `IdealTorsionCechComputation`,
  `ExtendedCechCompletionModel`, `ConstantCompletionEquivalence`,
  `RingedStrictTowerHomotopyLimitIndependentCoefficients`, and Mathlib's `KInjective`.
  Four proof dependencies have no recorded declaration yet and therefore no import:
  `lem-per-algebraic-dualizing-torsion-hull`, `lem-per-algebraic-completion-rhom`,
  `lem-per-algebraic-torsion-completion-hom`, and
  `lem-per-derived-completion-finite-cohomology`. They are proof prerequisites only;
  none is required to type this statement. The docstring carries all six proof steps.

Edge cases checked before finalizing the statement: i=0 gives H⁰ and Ext⁰;
M=0 is permitted; a field (m=0) is permitted and completion then leaves the module
unchanged; a zero ring is excluded exactly by the existing local-ring class; the zero
submodule is excluded only in the essentiality test, while the hull's embedding is
still required to be injective. Neither completeness of A nor positivity of its dimension
is assumed. Module and site universes follow the recorded normalized-dualizing interface;
no equality between independent site universes is imposed. Finite modules are represented
in the coefficient universe as in the existing `ModuleCat` and torsion interfaces.

Searches for an existing statement (all by the prescribed tools or read-only rg):

- msearch LeanFinder: "Local duality completed Ext into normalized dualizing complex
  equals Matlis dual of local cohomology". Eight hits concerned localCohomology,
  Ext, the Hom equivalence, and a flatness criterion; none states local duality.
- msearch LeanSearch: "local duality completed Ext normalized dualizing complex".
  Eight hits concerned localCohomology, finite-dimensional duals, and perfect pairings;
  none states the assertion.
- msearch Loogle: "AdicCompletion, Module.Essential". No hits; the latter identifier
  does not exist. The desired essentiality condition is rendered inline, as in the node.
- msearch grep: "local_duality|LocalDuality|IsEssential|InjectiveHull|AdicCompletion".
  Hits were completion machinery and unrelated essentially-small declarations.
- rg in Mathlib's Algebra and RingTheory for `IsEssential|InjectiveHull|injectiveHull`:
  no injective-hull declaration. Opened `AdicCompletion` rather than recreating it.
- rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf` for
  `local_duality|localDuality|LocalDuality|lem-per-algebraic-local-duality`: no exact
  theorem. Side-library hits were an existing consumer's natural-language proof and
  references to the distinct étale affine-line local-duality module.
- rg in the DAG for `injective hull|injective-hull|injectiveHull`: only the item,
  its torsion-hull proof prerequisite, its top-nonvanishing consumer and two unrelated
  enough-injectives/mapping-cylinder statements. No missing definition node is needed:
  essentiality is explicitly expanded using ordinary submodules and linear-map range.

No statement correction, dependency repair or new node was needed. No disputed claim.
Compilation uses only the authorized scompile.py wrapper; final verification is recorded
by the delivery dry run.

## Second reading by Q21

Author self-reading, not an independent review: reopened the node and the full file and
checked every clause above. The final conjunction separates existence from the result for
an arbitrary hull; Ω is the dependency's normalized algebraic dualizing complex, not a
ring-as-dualizing special case. The source has general coherent K; the node expressly
restricts to M[0], which is exactly the input of RHom here. Checked negative degree -i,
ordinary completion, ideal-torsion right derivation, and the A-linear equivalence.
No mismatch remained. Removed the redundant explicit `Nontrivial A` instance to make
compilation warning-free; nonzeroness remains supplied by `IsLocalRing A`. Independent
mathematical review is supplied by the maintainer under the dispatcher's direct-delivery rule.
