## Worker report

The module `Sheaf.Paper.FiniteCoefficientDualConstructible` states
`AlgebraicGeometry.Etale.finiteCoefficient_dual_constructible` with one whole-proof
`sorry`. No definition, additional node, dependency repair or statement correction is
needed. The DAG statement, its proof and all dependency lists are unchanged.

The statement is rendered hypothesis by hypothesis and clause by clause:

- Field k: `(k : Type u) [Field k]`. The field is arbitrary, without algebraic
  closedness, perfection or finiteness assumptions.
- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is the coefficient universe used by the recorded ordinary small-etale interface;
  any smaller coefficient ring can be lifted without changing the mathematical category.
- Invertible additive exponent: `_hΛ : IsUnit (AddMonoid.exponent Λ : k)`.
  Mathlib's additive exponent is the least positive integer annihilating the additive
  group. For a finite ring it exists. In a field the `IsUnit` condition is precisely
  invertibility of this integer. The binder is named with an underscore only to avoid
  an unused-variable warning while the proof is postponed; it remains a hypothesis.
- Separated finite-type k-scheme with named structure map: `(T : Scheme.{u})`
  `(a : T ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]`.
  Locally finite type plus quasi-compact is finite type. Since the node names a,
  the explicit map is the prescribed over-field encoding.
- Compactifiability is supplied by the imported Nagata instance for these hypotheses,
  rather than assumed in an additional binder. The field spectrum is qcqs.
- All objects belong to the ordinary `DerivedCategoryModule Λ T`, the localization
  of complexes of `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
- The right adjoint a^× is the existing `rightDerivedUpperShriek`, available for finite
  coefficients by `isLeftAdjoint_rightDerivedLowerShriekOfCompactification` and its
  chosen-compactification instance. No arbitrary functor or adjunction is postulated.
- The object omega_T is the existing `dualizingComplex (ModuleCat.{u + 1} Λ) a`.
  Its definition is the exceptional inverse image of the monoidal unit, the existing
  `constantComplex Λ (Spec (.of k))`, i.e. the constant coefficient sheaf in degree zero.
- The first conjunct is exactly
  `DerivedCategory.isBoundedConstructible Λ T (dualizingComplex ... a)`.
  Its definition says that every cohomology sheaf is constructible and vanishes outside
  a finite interval with ordered endpoints.
- The second conjunct quantifies over every `K : DerivedCategoryModule Λ T` and assumes
  exactly `DerivedCategory.isBoundedConstructible Λ T K`.
- The object D_T K is `(verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)`.
  The existing definition is the recorded ordinary-etale `derivedHom` evaluated on K
  and the same `dualizingComplex`; it is not the pro-etale or finite-Tor dual.
- Its bounded-below conclusion is `_root_.DerivedCategory.TStructure.t.plus (...)`,
  the object property defining `DerivedCategory.Plus` for the standard t-structure.
- Its constructible-cohomology conclusion is `∀ q : ℤ,
  Scheme.IsConstructibleEtaleModuleSheaf ((DerivedCategory.homologyFunctor ... q).obj ...)`.
  The same dual object occurs in both conclusions. There is no upper bound on it and
  no finite Tor amplitude hypothesis.

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: module
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`, reexporting
  `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`; cohomology is
  `DerivedCategory.homologyFunctor`, and D+ is the standard t-structure's `plus`.
- `thm-nagata-compactification`: module
  `WeilConjectures.Compactification.NagataCompactification`, declaration
  `AlgebraicGeometry.NagataCompactification` and its `HasCompactification` instance.
  The current source constructs the compactification; no extra compactification data
  are required in the item.
- `thm-amb-etale-exceptional-adjoint`: module
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`, declaration
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
  The current upstream theorem gives the adjoint for finite coefficients without the
  obsolete Noetherian binders in its recorded signature. The item is within its scope.
  `UpperShriek` packages this as `rightDerivedUpperShriek` and the adjunction.
- `def-pur-derived-internal-hom`: module
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, generic declaration
  `CategoryTheory.derivedInternalHomOfUniverses` and its explicitly recorded reexport
  `AlgebraicGeometry.Etale.derivedHom` from
  `WeilConjectures.SixFunctors.Etale.Derived.Hom`. The latter is the correct ordinary
  fixed-coefficient presentation; the generic SheafOfModules encoding is not substituted.
- `def-weil-pbc-constructible-complexes`: recorded module
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, reexporting
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` from
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`.
  Its cohomology predicate is `Scheme.IsConstructibleEtaleModuleSheaf`, explicitly
  finite locally constant values on a finite locally closed stratification.

The additional public `Dualizing` import supplies the existing names `dualizingComplex`
and `verdierDual`, whose signatures and full docstrings were read. The module imports
all 19 recorded proof-dependency modules (the constructibility definition is already a
public import), non-publicly when used only by the future proof. The theorem docstring
records all five proof steps: affine localization; affine purity and closed support;
truncation/devissage and stratum Hom; finite free resolutions and hyper-Ext descent;
and bounded-below direct-image truncation. No biduality theorem is used as a replacement
for this proof route.

Edge cases checked before writing:

- Empty T is allowed; there is no Nonempty binder or nonempty-cover assumption.
- The zero coefficient ring is allowed; its additive exponent is 1, invertible in k,
  and its module category is zero. No Nontrivial Λ instance is required.
- K = 0 is allowed. No nonzero cohomology degree or nonempty interval of support is assumed.
- For T = Spec k and a the identity, omega is the coefficient object and the claim
  reduces to the ordinary finite-module derived Hom calculation.
- In characteristic zero every positive finite additive exponent is invertible;
  in characteristic p the hypothesis excludes exactly exponents divisible by p.
- Arbitrary finite rings, including nonregular rings, remain allowed. The result says
  D+ with individually constructible cohomology, never D^b for every dual.
- All universes and variables are explicit; no extra site universe equality is imposed.

Searches for an existing statement:

- `msearch.py leanfinder`, query:
  "Over a field with finite commutative coefficients of invertible additive exponent the
  exceptional dualizing complex is bounded constructible and derived internal Hom of a
  bounded constructible complex into it is bounded below with constructible cohomology".
  Eight hits, headed by the derived-category IsGE/IsLE comparison lemmas; no duality
  constructibility statement.
- `msearch.py loogle`, query:
  "AlgebraicGeometry.Etale.derivedHom, AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible".
  Zero hits, unknown project identifier `AlgebraicGeometry.Etale.derivedHom`.
- `msearch.py grep`, query:
  "Verdier|dualizingComplex|constructible.*[Hh]om|[Hh]om.*constructible".
  Twenty-five Mathlib hits, primarily bibliographic occurrences of Verdier and spectral
  object files; no etale coefficient-dual constructibility theorem.
- `msearch.py leansearch`, query:
  "Finite coefficient Verdier dual of a bounded constructible complex over an arbitrary
  field has constructible cohomology". Eight hits about finite module duals and dual bases;
  no sheaf or derived-etale match.
- `rg` on both project roots for dual/constructibility and the exact node id, and on
  `dag/lean_names_upstream.json` for finite-coefficient dual constructibility.
  No exact theorem. Existing `Stability.DerivedHom` results require finite Tor amplitude
  or a dualizable first argument; `WeilVerdierPreservationStrata` specializes to adic
  coefficient stages. Neither gives this arbitrary finite-ring D+ statement.
- `rg` for the chosen full declaration name in Mathlib, both project roots and the
  upstream-name index found no existing declaration.

Source checked: the BBD PDF around §§4.0–4.2, including the introductory coefficient
conventions, together with the node's explicit five-step finite-ring proof. The statement
is unchanged. There is no STATEMENT-DISPUTED flag or known statement fault.

Validation: `scompile.py NH lem-per-finite-coefficient-dual-constructible` compiled both
its sandbox check and the library module on the live server with no errors or warnings
(5.7 and 5.6 seconds respectively). No local or global build was run.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
