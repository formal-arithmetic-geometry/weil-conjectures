## Worker report

This delivery states `absolute_dedekind_normalization_reduced_fibres` in
`Sheaf.RingTheory.AbsoluteDedekindNormalizationReducedFibres`. The sole theorem
has proof `sorry`. The six supporting declarations contain concrete data: the
generic algebra, the specified base-change map, its ambient algebra and scalar
tower, the prescribed relative integral closure, and its canonical generic map.
They belong to this node's construction; no additional independent notion or DAG
node is introduced. The node changes only in `lean`.

Source checked: Anantharaman, *Schémas en groupes, espaces homogènes et espaces
algébriques sur une base de dimension 1*, Appendix II, Theorem 1, printed p.73
(PDF page 69), at https://www.numdam.org/article/MSMF_1973__33__5_0.pdf . Its
normalization is flat, separable, locally finitely presented over the absolute
integral base and finite over the base change. The affine formulation supplies
the finite presentation used here. The ten-step DAG proof is reproduced in the
theorem docstring, including the localization, spreading, eta-normality,
finite-product normality and arbitrary-field fibre arguments.

Clause-by-clause statement correspondence:

- `R : Type u`, `[CommRing R]`, `[IsDomain R]`, `[IsNoetherianRing R]`,
  `[IsIntegrallyClosed R]` and `hdim : ringKrullDim R = 1` give exactly a
  Noetherian integrally closed domain of dimension one. No semilocality or
  excellence is imposed.
- `K : Type v`, `[Field K]`, `[Algebra R K]`, `[IsFractionRing R K]` specify
  an arbitrary fraction-field realization; this does not impose a chosen model.
- `Ω : Type w`, `[Field Ω]`, `[Algebra K Ω]`, `[IsAlgClosure K Ω]` specify
  the chosen algebraic closure. `[Algebra R Ω] [IsScalarTower R K Ω]` only
  register the composite structural map, rather than introducing a new
  mathematical hypothesis.
- `integralClosure R Ω` is exactly B, with its usual subalgebra structure.
- `A : Type x`, `[CommRing A]`, `[Algebra R A]`,
  `[Algebra.FinitePresentation R A]`, `[Module.Flat R A]` are the specified
  commutative finitely presented flat R-algebra.
- `hgeom` quantifies over fields E/K and every prime p of
  `E ⊗[K] (K ⊗[R] A)`. The conclusion
  `IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed ...` is exactly
  the stated geometric normality condition. Scalar factors are on the left
  throughout, using tensor commutativity to identify these with the node's
  right scalar factors. Test fields live in `max u v w x y`, at least the
  universes of all input rings; there is no smaller-universe vacuity.
- B ⊗_R A is the node's A_B, with factors reversed to give the standard
  global B-algebra instance. `Generic R K Ω A` is Ω ⊗_K (K ⊗_R A), the
  canonically reordered D. `baseMap` sends b ⊗ a to b ⊗ (1 ⊗ a).
  `Function.Injective (baseMap R K Ω A)` is precisely the first assertion;
  it is a conclusion, not an added assumption.
- `ambientAlgebra` is induced by that specified map using `RingHom.toAlgebra`;
  `ambientTower` is its actual `IsScalarTower.of_algHom` witness. The
  abbreviation `closure R K Ω A` is `integralClosure (B ⊗[R] A) D`,
  literally the prescribed subalgebra C, not an existential substitute.
- `Module.Finite (B ⊗[R] A) C` gives finiteness over A_B;
  `Module.Flat B C` and `Algebra.FinitePresentation B C` give the next
  two conclusions with the induced B-algebra structure.
- The quantifier over every prime ideal of C and its normal-domain
  localization expresses normality, using the recorded inline normal-ring form.
- `genericMap` sends c ⊗ ω to the product of c's ambient value with the
  scalar ω in D; `Function.Bijective (genericMap R K Ω A)` says this
  particular algebra homomorphism is an isomorphism. Neither an arbitrary
  isomorphism nor an arbitrary map is substituted.
- The final clause quantifies over E with a B-algebra structure (equivalently
  every B → E ring homomorphism), E' with `[Algebra E E']`, and the induced
  compatible B-algebra structure on E'. Field homomorphisms are injective,
  so this is exactly E ⊆ E'. `IsReduced (C ⊗[B] E')` means absence of
  nonzero nilpotents. `E'` lives in `max u v w x y z`; its size is not
  forced equal to E's or any input ring's.
- No `IsDomain C`, `Nontrivial A`, Noetherian B, finite B/R, or excellence
  hypothesis occurs. Zero algebras and empty fibres remain included.

Statement dependency declarations used, with sources read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, line 196,
  self-module Noetherianity, equivalent to all ideals finitely generated.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`:
  `IsIntegrallyClosed` at line 74 and its fraction-field interpretation;
  normal rings use the node's inline conjunction over prime localizations.
  `Mathlib.RingTheory.Localization.AtPrime.Basic` supplies
  `Localization.AtPrime` at lines 54–58.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` (and its Basic import):
  `IsAlgClosure` at Basic line 264, an algebraically closed algebraic field
  extension. The dependency's `mathlib_match` explicitly permits this predicate.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`,
  lines 215–222, its carrier being exactly integral elements.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`,
  lines 42–46, a finite polynomial presentation with finitely generated kernel.
- `Mathlib.RingTheory.RingHom.Flat`: `Module.Flat` via the flat module API;
  `RingHom.Flat` at line 27 is this same property on the induced algebra.
  The injectivity formulation is documented at Flat.Basic lines 105–116.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, lines 78–82,
  the bilinearity quotient; multiplicative algebra structures and the
  canonical universal maps come from `Mathlib.RingTheory.TensorProduct.Maps`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, lines 116–120,
  finitely generated top submodule.

All recorded, stated proof-dependency modules are imported with ordinary
`import`. Their imports include the valuation normalization theorem and the
spreading/eta-normality results. Mathlib proof leaves are also imported by
recorded source module. `lem-trf-affine-geometric-fibre-reduced-comparison`
has neither a Lean record nor a Mathlib match in the read snapshot and therefore
has no module to import; it is only a proof dependency and is not needed to type
this statement. No import cycle was introduced.

Edge cases checked: A = 0 gives D = C = 0, whose normality condition is vacuous
because it has no prime ideals; its zero module is finite, flat and finitely
presented, and the generic map is bijective. Empty fibres are reduced, including
at points outside the support. No characteristic restriction is present. R is
not a field because its dimension is exactly one. Generic fibres can be products
of normal domains and need not be domains themselves; the statement uses all
prime localizations rather than imposing a domain on the whole ring. Field
extensions of different sizes are included with maximum-universe binders.

Searches actually run with the prescribed msearch.py wrapper:

- LeanFinder: “Normalization of a flat finitely presented algebra over the
  absolute integral closure of a Dedekind domain has reduced geometric fibres
  and is finite flat finitely presented”; eight hits, chiefly normal-closure
  finiteness for finite extensions and scheme relative-normalization instances;
  no match for the present theorem.
- Loogle: `integralClosure, Module.Flat, Algebra.FinitePresentation`; zero hits.
- grep in Mathlib/RingTheory: `normalization|integralClosure`; 25 reported hits,
  including NormalClosure and Smooth/IntegralClosure. They supply constructions
  and special cases, not Raynaud normalization over this absolute integral base.
- LeanSearch: “Normalization over the integral closure of a Dedekind domain in
  an algebraic closure has reduced geometric fibres”; eight hits, geometric
  reducedness predicates, finite-extension Dedekind closure, and relative
  normalization instances; no exact theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: patterns
  `valuationReduced|valuation_reduced|integralClosure.*TensorProduct|absoluteDedekind|absolute_dedekind|geometricallyNormal`
  and `absolute.*[Dd]edekind|[Dd]edekind.*normalization|[Dd]edekind.*[Rr]educed`.
  Found the existing valuation theorem and related geometric-normality material,
  but no duplicate absolute Dedekind theorem. Searching the full item id in
  `lean/WeilConjectures` returned no match. Full proposed names also have no
  entry in `dag/lean_names_upstream.json`.

No statement correction, dependency-interface repair or disputed statement.
Validation: scompile.py compiled both the sandbox and the actual module name
cleanly. The first deliver2.py --no-push completed with OK, passing server
preflight and per-file compilation. Before the final dry run I adjusted only
docstring wrapping to keep DAG identifiers unbroken across lines.

## Second reading by Q99

Re-read the node and the final source clause by clause in the same worker
session. The dispatcher prohibits starting other agents, so this is a self-check;
the maintainer's independent review remains required. In particular I checked
that B and C are the prescribed integral closures, injectivity is asserted and
not assumed, normality is local rather than a domain assertion, and the generic
map is the explicitly constructed one. The first compile caught the base map's
left input being typed as Ω instead of B; it was corrected to `Algebra.ofId B D`.
The generic map retains Ω as its scalar input. All seven conclusion clauses,
including the E/E' fibre clause, match the unchanged node. No mathematical
hypothesis or conclusion was altered.
