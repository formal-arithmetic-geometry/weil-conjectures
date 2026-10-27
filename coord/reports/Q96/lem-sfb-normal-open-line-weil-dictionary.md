## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.normal_open_line_weil_dictionary`
in `Sheaf.AlgebraicGeometry.NormalOpenLineWeilDictionary`. It has exactly one theorem,
with proof `sorry`; no new construction or proof is introduced. The module docstring
and declaration docstring cite Stacks Divisors Tags 02SF, 02SG, 0BE6 and 0BE8, read
in `literature/stacks-project/divisors.tex:6708-6912`. The declaration docstring gives
all seven steps of the accepted proof, including the finite-minimal-prime support
argument, localization at each point, and both directions of the triviality criterion.

Hypothesis and clause correspondence:

- The commutative Noetherian normal domain is `{A : Type u} [CommRing A]
  [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]`. The normal-domain
  conjunction is exactly the recorded inline convention of def-weil-pbc-normal-ring.
- Its field of fractions is `FractionRing A`; each occurrence of `K^×` is
  `(FractionRing A)ˣ`, so zero is excluded without an extra hypothesis.
- `H(A)` is `Ring.WeilHeightOnePrime A`, whose existing definition is the subtype
  of prime-spectrum points with nonzero ideal and no nonzero strictly smaller prime.
- The normalized DVR valuation is `Ring.weilFractionOrder q a.val`. Its actual
  construction subtracts the existing local length orders of numerator and denominator
  of `IsLocalization.sec`. On the domain's nonzero fractions this is precisely the
  normalized additive DVR valuation described in the node, with positive uniformizer
  value. No arbitrary valuation or extra DVR instance is assumed.
- The open subscheme is `(U : (Spec (CommRingCat.of A)).Opens)`, with scheme
  structure `U.toScheme`, the canonical restriction of the affine spectrum. The
  hypothesis `(hU : Nonempty U)` renders exactly its nonemptiness. This describes
  an open subscheme directly; there is no additional open-immersion hypothesis to
  supply, since the canonical `U.ι` is already an open immersion.
- The invertible module is `(L : U.toScheme.Modules) [L.IsInvertible]`, using the
  recorded upstream class for local triviality in rank one.
- The finitely supported integer family is the outer existential
  `∃ d : {q : Ring.WeilHeightOnePrime A // q.val ∈ U} →₀ ℤ`. Its index is exactly
  `H(A) ∩ U`, with no coefficients on the complement.
- The local-equation clause is `∀ t : PrimeSpectrum A, t ∈ U → ∃ a :
  (FractionRing A)ˣ, ∀ q : {q : Ring.WeilHeightOnePrime A // q.val ∈ U},
  q.val.val.asIdeal ≤ t.asIdeal → d q = Ring.weilFractionOrder q.val a.val`.
  One single `a` works for all the height-one primes contained in each fixed `t`.
  Restricting the tested index to those in `U` does not omit any prime contained
  in `t`: every open subset of a spectrum is stable under generalization, and
  containment of prime ideals is generalization in this direction. Thus all
  the primes specified by the node occur in this quantified subtype.
- The second conjunct is the biconditional between
  `Nonempty (L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)` and the existence
  of a single `a : (FractionRing A)ˣ` with the required equality for every index.
  The unit is exactly the structure sheaf as a module. Both sides use the same
  outer `d` as the local-equation clause; neither the family nor its quantifier
  changes between the conclusions.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (lines 193-204), all
  ideals finitely generated.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`
  (lines 63-74), integrally closed in the fraction ring, together with `IsDomain`.
- `Sheaf.RingTheory.WeilDivisorClassGroup`: `Ring.WeilHeightOnePrime` (lines
  27-34), `Ring.weilOrder` (lines 42-51), and its `AffineWeilDivisor` convention.
  This is the unchanged record of def-trf-affine-weil-divisor-class-group.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  (lines 53-58), the actual prime-complement localization used by `weilOrder`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`
  (lines 56-60), the local PID that is not a field. No extra assumption on `A`
  is imposed; only its height-one localizations are DVRs mathematically.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` (lines 469-472).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (lines 34-39); `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`,
  `Scheme.Opens.ι` and its canonical open-immersion instance (lines 44-57).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (docstring and lines 55-64),
  the recorded notion of invertible module. `SheafOfModules.unit` is the existing
  structure-sheaf module used by that class itself.
- `Sheaf.RingTheory.HeightOneFractionOrder`: `Ring.weilFractionOrder` (whole
  module read, lines 29-46), recorded by the already landed definition node
  def-trf-height-one-fraction-order. This existing node is added to `stmt_deps`
  under the rule allowing added landed definition nodes. No node is created
  or restated, and the mathematical statement is unchanged.

Plain proof imports retain the stated proof dependencies: FunctionField,
Properties, InvertibleModuleGenericStalk (its full signature and docstring read),
Spectrum.Prime.Topology, Ideal.MinimalPrime.Noetherian, Localization.Submodule,
and Localization.LocalizationLocalization. The proof dependency
lem-trf-normal-domain-principal-divisor-kernel currently has neither a Lean record
nor a Mathlib match, so no import is claimed for it. It is explicitly named in the
proof docstring; the stage-2 statement does not require its theorem to be available.

Edge cases checked mathematically before writing:

- If `A` is a field, `H(A)` is empty. The finitely supported family is uniquely
  zero; its equations are vacuous, while every invertible sheaf on the one-point
  open is trivial. The statement includes this case.
- At the generic point there are no contained height-one primes; `a_t = 1`
  satisfies the local condition. No existence of a height-one prime is assumed.
- `U = Spec A` is allowed, as is a proper non-affine open. No affineness or
  factoriality of `U` is added, nor a global trivialization of `L`.
- Empty support, including a rational section already a global frame, is allowed.
- The empty open is excluded exactly by the node's `hU`, and the zero ring is
  excluded exactly by its domain hypothesis.
- There are no characteristic or dimension restrictions, and `u` is arbitrary.
  The fixed `FractionRing A` is the node's `Frac(A)`, not a restriction on a
  separately given coefficient field or universe.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`
for this group/item:

1. LeanFinder: `An invertible sheaf on an open of a Noetherian normal affine scheme
   has a finite Weil divisor with local equations and is trivial exactly when that
   divisor is principal`. Eight hits, including
   `AlgebraicGeometry.StructureSheaf.normalize_finite_fraction_representation`,
   `ClassGroup.mk0_eq_one_iff`, and `ClassGroup.mk_eq_one_of_coe_ideal`.
   The former concerns structure-sheaf fraction representations; the latter concern
   ideals and (for mk0) Dedekind domains, not the open-scheme statement.
2. Loogle: `"WeilDivisor", "IsInvertible"`. Zero hits.
3. Grep of Mathlib: `WeilDivisor|normalC1|normal_c1|weilOrder|normalizedValuation`.
   Zero hits.
4. LeanSearch: `An invertible sheaf on an open normal Noetherian affine scheme is
   trivial if and only if its Weil divisor is principal`. Eight hits, principally
   ring-module Picard results such as `CommRing.Pic.mk_eq_one_iff_free` and
   `CommRing.Pic.instSubsingletonOfIsLocalRing`. None is this statement for an
   arbitrary open of a normal affine scheme.
5. `rg -n 'WeilDivisor|normalC1|normal_c1|weilOrder|WeilHeightOnePrime'
   lean/WeilConjectures lean/Sheaf`, and
   `grep -rn 'lem-sfb-normal-open-line-weil-dictionary' lean/WeilConjectures`.
   No upstream item match. Project hits give the existing WeilDivisorClassGroup,
   HeightOneFractionOrder, CartierFractionCover and other different divisor
   statements. The relevant definitions were read and reused, not duplicated.
6. The proposed full declaration name and its camel-case variant were searched
   in `lean/Sheaf`, `lean/WeilConjectures`, Mathlib and
   `dag/lean_names_upstream.json`; no collision.

Validation: the delivered module was compiled via the prescribed `scompile.py`
on 2026-10-24 against the live published library, both as a sandbox and at its
library module name. Both succeeded without errors or warnings. Every variable
and universe is bound explicitly (`set_option autoImplicit false`); all lines
are at most 85 characters. There is no statement dispute, correction, new node,
or dependency-record repair.

## Second reading by Q96

A separate final rereading of the node's TeX, the full declaration and the Stacks
source confirms the binder list is exactly a Noetherian integrally closed domain,
a nonempty open subscheme and an invertible module. In particular no unnecessary
DVR, UFD, affine-open or extra universe assumption has entered. The subtype in the
finsupp binder is exactly the height-one primes in the open; `≤` in the local
clause is non-strict ideal containment, so equality with a height-one `t` is
included. All contained primes are in the open by generalization, which resolves
the apparent restriction in the local index. Units in the fraction field express
all nonzero fractions. The outer existential scopes over the conjunction and
both sides of the biconditional, so both conclusions concern the same family.
The right side quantifies one fraction over all indices, while the local side
quantifies one fraction separately for each point. The isomorphism on the left
is to the actual structure-sheaf module, with both directions retained.

The existing height-one-fraction-order node and module were checked again:
`weilFractionOrder` uses actual numerator/denominator local lengths, with the
same normalized sign convention as the source. Adding this already landed node
to `stmt_deps` is the only change besides `lean`. No mismatch requiring a
statement change was found. This is Q96's final self-reading; the dispatcher's
instruction forbids starting another agent, and the maintainer's independent
review remains the separate review required by the assignment.
