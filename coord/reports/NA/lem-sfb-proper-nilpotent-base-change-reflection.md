## Worker report

The module `Sheaf.AlgebraicGeometry.ProperNilpotentBaseChangeReflection` states
`AlgebraicGeometry.isProper_iff_of_nilpotent_quotient`. It has one named theorem,
with proof `sorry`, and no new definitions. The DAG copy changes only `lean`.
No statement correction, dependency repair, new node, or dispute is needed.

Source read: `literature/stacks-project/more-morphisms.tex`, the full statement of
`lemma-thicken-property-morphisms-cartesian` (Tag 09ZW), and its proof of (7),
together with `lemma-thicken-property-morphisms` (Tag 09ZV). The source identifies
properness with quasi-compactness, separatedness, local finite type and universal
closedness and reflects these across the specified finite order thickening.
The theorem docstring gives all six steps of the accepted DAG proof, including the
representable-algebraic-space substitution and the closed-image equality after
arbitrary base change.

Hypotheses and clauses, individually:

- Commutative ring A: `{A : Type u} [CommRing A]`. No nonzero-ring assumption.
- Ideal I in A: `(I : Ideal A)`. No finite-generation assumption.
- Integer N at least 1: `(N : ℕ) (hN : 1 ≤ N)`. Positive integers are exactly
  these naturals; negative exponents never occur in the source or the node.
- I^N = 0: `(hI : I ^ N = ⊥)`, where the bottom ideal is the zero ideal.
- Any scheme Y: `{Y : Scheme.{u}}`.
- Any scheme morphism f to Spec A: `(f : Y ⟶ Spec (CommRingCat.of A))`.
- Spec(A/I) → Spec A is the actual quotient-induced morphism
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.
- Y₀ is exactly the chosen fibre product `pullback f` with that quotient morphism.
  It is inferred as the domain of the projection; no separate arbitrary model or
  isomorphism is supplied as a hypothesis.
- f₀ is exactly `pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))`,
  with codomain `Spec (CommRingCat.of (A ⧸ I))`.
- Properness of f if and only if properness of f₀ is the single `IsProper f ↔
  IsProper (pullback.snd ...)` conclusion, in the node's orientation.
- No flatness, finite-type, Noetherian, nonemptiness or field hypothesis occurs.
  `set_option autoImplicit false` prevents accidental added binders.

All four statement dependencies were opened, including their recorded source
signatures and docstrings:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst` and
  `pullback.snd`, in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`. Its locally-of-finite-type
  formulation is equivalent to the node's finite-type formulation because
  `UniversallyClosed` gives `QuasiCompact`, as recorded by the dependency.

The statement modules are public imports. Recorded proof-dependency modules are
plain imports: `WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal`
(`quotientBaseChange_closedImmersion_ideal` and `quotientBaseChange_extendedIdeal_mul_pow`),
`WeilConjectures.AlgebraicGeometry.Thickening` (`IsFiniteOrderThickening`),
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
(the surjective-closed-immersion instance),
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (`LocallyOfFiniteType`),
`WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeThickening`
(`locallyOfFiniteType_iff_of_finiteOrderThickening`),
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`
(`AlgebraicGeometry.AlgebraicSpace.schemeSpace`), and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
(`IsClosedImmersion.isStableUnderBaseChange`).
The proper-base-change proof dependency is already supplied by the properness
statement import. The smoothness clause of that dependency is not used here.
`lem-sfb-space-thickening-topological-properties` has no recorded Lean module or
Mathlib match, so there is no module to import for that proof-only dependency.
It is still named with its precise substitution in the proof docstring; no
unstated notion is required for this theorem's signature.

Edge cases checked mathematically before writing:

- I = 0: quotient base change is isomorphic to the original morphism.
- N = 1: the assumption forces I = 0 and the same case applies.
- A the zero ring: both spectra are empty and a scheme over the empty spectrum
  is empty. The statement remains correct without a `Nontrivial A` hypothesis.
- Y empty: both morphisms are proper and no nonempty-source condition appears.
- Ideals need not be finitely generated; nilpotence gives a finite order
  thickening regardless. No Noetherian or flatness condition was introduced.
- A non-finite-type morphism is allowed as input. Reflection of local finite
  type belongs in the proof, not among the assumptions.
- The arbitrary common universe u follows Mathlib's scheme and spectrum APIs;
  it does not fix a particular size or introduce a small test-object universe.

Searches, all performed with the prescribed wrapper unless indicated:

1. `leanfinder`: "A scheme morphism to Spec A is proper if and only if its base
   change to Spec of A modulo a nilpotent ideal is proper". Eight hits, including
   `IsProper.isStableUnderBaseChange`, `IsProper`, `isProper_iff`, and composition
   properties. None reflects properness along a nilpotent quotient.
2. `leansearch`: "Proper morphisms of schemes are reflected by base change along
   a nilpotent quotient". Eight hits: properness and universal-closedness base
   change, plus unrelated formally unramified declarations. No reflection theorem.
3. `loogle`: "IsProper, Ideal.Quotient.mk". Zero hits, with unknown unqualified
   identifier `IsProper`. Repeated with "AlgebraicGeometry.IsProper": twelve hits
   on its definition, component projections, composition and base-change instances;
   none is the equivalence at hand.
4. Mathlib `grep` via msearch: `proper.*(nilpotent|thicken)|[Ii]sProper.*[Qq]uotient|[Ii]sProper.*[Tt]hicken`
   in AlgebraicGeometry. Zero hits.
5. Direct `rg -n -i` in both `lean/WeilConjectures` and `lean/Sheaf` for
   `proper.*(nilpotent|thicken)|isProper.*quotient|isProper.*thicken|nilpotent.*proper`:
   only unrelated text hits and the downstream isolated-curve proof docstring
   citing this item; no existing theorem.
6. Direct node-id search in `lean/WeilConjectures`: no hits. Proposed declaration
   name search in Mathlib, both project roots and `dag/lean_names_upstream.json`:
   no collision.

Validation: the prescribed `scompile.py NA lem-sfb-proper-nilpotent-base-change-reflection`
compiled this module as sandbox and library modules, in 1.5 s and 1.7 s respectively,
with no errors or unexpected warnings. The prescribed `deliver2.py --no-push`
then printed OK: preflight and compilation both passed (dry-run commit a5ae3982f8c).

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
