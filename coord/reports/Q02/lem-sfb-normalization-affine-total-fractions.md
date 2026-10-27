## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizationAffineTotalFractions` states
`AlgebraicGeometry.Scheme.normalization_affine_total_fractions`, with `sorry` as its
entire proof. It constructs no new notion and changes only the item's `lean` record.
The source was read in `literature/stacks-project/morphisms.tex`,
`lemma-description-normalization` (Tag 035P), especially (1), (4) and their proof,
and `lemma-normalization-in-terms-of-components` (Tag 0CDV).

Hypotheses and clauses, in the order of the node:

- A reduced scheme is `(X : Scheme.{u}) [IsReduced X]`.
- Finitely many components on every quasi-compact open is exactly
  `hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite`.
  This is not a local Noetherianity assumption; it quantifies over every compact open.
- The normalization and its map are the recorded `X.reducedNormalization` and
  `X.fromReducedNormalization`, not an arbitrary scheme and map.
- `(U : X.affineOpens)` supplies the affine open. We take its canonical coordinate
  ring `A = Γ(X, U)`, with `U.2.isoSpec : U.1.toScheme ≅ Spec Γ(X, U)`.
  Any presentation of this same open as Spec A transports uniquely to this coordinate
  ring by global sections; the theorem therefore does not restrict affine presentations.
- The node's S_A is Mathlib's `nonZeroDivisors Γ(X, U)`. In a commutative ring its
  left and right conditions agree, so it is precisely the given condition sa = 0 ⇒ a = 0.
- Q(A) is `Localization (nonZeroDivisors Γ(X, U))`, the ring localization, and the
  integral closure is `integralClosure Γ(X, U) (Localization (nonZeroDivisors Γ(X, U)))`.
  Mathlib's ring localization and `LocalizedModule S A` have the same quotient type:
  see `example_localization_eq_localizedModule` in the recorded dependency's Basic.lean
  (definitionally equal). The ring specialization provides its canonical ring structure.
- The first conclusion `_root_.IsReduced Γ(X, U)` explicitly states reducedness of A.
- `(minimalPrimes Γ(X, U)).Finite` states finiteness of *all* minimal prime ideals;
  Mathlib's minimal primes are `Minimal Ideal.IsPrime`, with no enumeration supplied
  as an additional hypothesis.
- The existential `e` has source exactly `(X.fromReducedNormalization ⁻¹ᵁ U.1).toScheme`
  and target the spectrum of that integral closure. Its equation is an equality of
  maps to `U.1.toScheme`, not merely to X:
  `e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A Q))) ≫
  U.2.isoSpec.inv = X.fromReducedNormalization ∣_ U.1`.
  Thus the ring map is the specified canonical map into the actual subalgebra in Q,
  whose value, after inclusion in Q, is a/1. This is not an unconstrained isomorphism.
  Canonicity is determined by this equation: any two such isomorphisms differ by an
  A-automorphism of the integral-closure subring of Q. Every element of that subring
  is a fraction a/s with s a nonzerodivisor, so an A-automorphism fixes it after clearing
  s. Multiplication by s is injective in Q, hence in its subring. Consequently the
  automorphism is the identity. No extra isomorphism or arbitrary canonical-map datum
  is assumed, and no `Nonempty` choice is used to manufacture a definition.
- The conditional `U.1 = ⊥ → ...` explicitly records all empty-open clauses:
  `Subsingleton A`, `Subsingleton Q`, `Subsingleton (integralClosure A Q)`,
  `IsEmpty` of the inverse image, and `IsEmpty` of the integral-closure spectrum.
- There is no Noetherianity, nonemptiness, nontriviality, domain, or finiteness of
  normalization hypothesis. The only universe is the scheme universe u; all section
  rings and spectra have the appropriate same universe.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` and its
  section-wise condition, from def-pc-reduced-scheme.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, `IsIrreducible`, from
  def-weil-irreducible-components, whose `mathlib_match` is the usable declaration.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization`, including the full construction as a coproduct
  of the function-field normalizations of reduced induced components, from
  def-weil-pbc-reduced-normalization. Its component construction and docstrings were read.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, supplied by AffineScheme
  and ReducedNormalization, from def-weil-affine-spectrum.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, together with
  the definitionally equal ring specialization `Localization` and its ring algebra
  structure from `Mathlib.RingTheory.Localization.FractionRing`, from
  def-weil-pbc-module-localization. No new localization definition is introduced.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, its actual
  subalgebra carrier `{r | IsIntegral A r}` and structural algebra map, from
  def-weil-pbc-integral-closure.

Proof-dependency imports are included for the already stated
`Algebra.totalQuotientRing_isProduct_minimalPrimes` (Sheaf module
TotalQuotientRingMinimalProduct), `PrimeSpectrum.zeroLocus_minimalPrimes`
(Mathlib.RingTheory.Spectrum.Prime.Topology), the minimal-prime localization facts
in Mathlib.RingTheory.KrullDimension.Zero, affine stalk localization in AffineScheme,
and `Scheme.residueField` in Mathlib.AlgebraicGeometry.ResidueField.
The two proof-only nodes lem-sfb-normalization-generic-residue-affine-charts and
lem-sfb-reduced-weakass-minimal have no recorded Lean declaration at inspection;
they are not needed to type this statement and have no module to import yet.
The five-step docstring retains the full proof route and names these nodes.

Edge cases checked before writing: the empty X; empty U inside a nonempty X; the zero
ring (0 is a nonzerodivisor there, so localization is still a zero ring); no minimal
primes in the zero ring; a reducible reduced affine ring with finitely many minimal
primes; and a non-Noetherian reduced ring. In particular, neither FractionRing A
(which could incorrectly suggest a domain) nor a product over an assumed nonempty
finite set is used. No node fault or statement correction was needed.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Affine opens of the normalization of a reduced scheme
  are spectra of integral closures in total quotient rings"`: eight hits, all relative
  normalization interfaces in Mathlib.AlgebraicGeometry.Normalization. Those require
  a supplied qcqs map and normalize its section algebra, not this componentwise map.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.reducedNormalization, integralClosure,
  Localization"`: zero hits; the project-specific normalization name is unknown to
  Loogle's Mathlib index.
- `msearch.py ... grep 'totalRingOfFractions|fromNormalization_app|nonZeroDivisors'
  AlgebraicGeometry`: thirteen hits; relevant hits are relative normalization's
  `fromNormalization_app`, whose full signature and surrounding construction were read.
  It does not assert this absolute componentwise normalization chart theorem.
- `msearch.py ... leansearch "normalization of reduced affine scheme integral closure
  in total fraction ring"`: eight hits, on integral closure of domains, almost integral
  closure, and relative `ι_toNormalization`; none states this node.
- `rg` of `totalRingOfFractions|totalQuotient|normalization.*affine` in both
  lean/WeilConjectures and lean/Sheaf found TotalQuotientRingMinimalProduct,
  ComponentwiseNormalizationAffineCharts, relative normalization and downstream users.
  The full ComponentwiseNormalizationAffineCharts statement requires
  `[IsLocallyNoetherian X]` and gives products of fraction fields of quotients;
  it is not the present non-Noetherian theorem. The full recorded componentwise
  normalization source was read and reused.
- `grep -rn 'lem-sfb-normalization-affine-total-fractions' lean/WeilConjectures`:
  no matches. `rg` of the chosen declaration name in Mathlib, WeilConjectures and Sheaf:
  no matches. `dag/lean_names_upstream.json` has normalization and localization
  entries but no entry or declaration for this theorem.

Validation: the prescribed server `scompile.py Q02
lem-sfb-normalization-affine-total-fractions <module>` compiled both sandbox and
library-name versions cleanly (2.9 s and 4.5 s on the first pass). Every theorem proof
is precisely `sorry`; all binders and the universe are explicit. The delivery dry run
and final delivery are performed using the prescribed `deliver2.py` wrapper.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
