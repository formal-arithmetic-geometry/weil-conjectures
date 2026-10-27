# Local generic-fibre unit factorization

## Worker report

The module `Sheaf.RingTheory.LocalGenericUnitFactorization` states
`Algebra.local_generic_unit_factorization` with its sole proof `sorry`.
No definitions or dependency interfaces are duplicated. The accepted node statement,
statement dependencies, and ten-step proof are unchanged. The module docstring gives
the source and the declaration docstring records all ten proof steps.

The inherited refusal concerned reopening Q57's stage-1 split. The stage-2 handoff
in `coord/brief-stage2.md` §0 explicitly allows recording the Lean statement of that
accepted split. The current queue lists this item at stage 2 and the node has no Lean
record. There is no released repair note for this item.

Hypothesis and clause correspondence:

- The commutative rings A and B are `(A : Type u) (B : Type v) [CommRing A]
  [CommRing B]`, with independently bound universes; the map is the supplied
  `[Algebra A B]`'s `algebraMap A B`. Any ring homomorphism gives precisely such
  an algebra structure, so this does not require extra structure.
- Both integral domains: `[IsDomain A] [IsDomain B]`. Nontriviality is included.
- Both Noetherian rings: `[IsNoetherianRing A] [IsNoetherianRing B]`.
- The normal base domain: `[IsIntegrallyClosed A]` together with `[IsDomain A]`.
  No normality assumption is placed on B.
- Both unique maximal ideals: `[IsLocalRing A] [IsLocalRing B]`. The inverse-image
  maximal-ideal condition is `[IsLocalHom (algebraMap A B)]`: for local rings,
  reflecting units is equivalent to that condition (`IsLocalRing.local_hom_TFAE`).
- Flatness: `hflat : RingHom.Flat (algebraMap A B)`.
- For every prime p, the localized quotient is a nonzero integral domain:
  `hfibres : ∀ (p : Ideal A) [p.IsPrime], IsDomain (p.Fiber B)`.
  Mathlib `Ideal.Fiber` is κ(p) tensor B, canonically the localization of B/pB
  at images of A outside p. It is not the stronger assertion that B/pB is a domain.
- K is Mathlib's `FractionRing A`. The generic fibre B_K is represented by
  `FractionRing A ⊗[A] B`. Localization commutes with base change:
  `IsLocalization.tensorRight` in `Mathlib.RingTheory.Localization.BaseChange`
  realizes this as localization of B at the images of A's nonzero elements.
  This is an equivalent canonical construction of exactly B_K, not an arbitrary
  algebra or comparison map. No auxiliary hypothesis about embeddings is needed.
- The first conjunct quantifies over every unit f of this generic fibre and supplies
  `h : (FractionRing A)ˣ` and `w : Bˣ`. Its equation is f = image(h) * image(w).
  `algebraMap (FractionRing A) (FractionRing A ⊗[A] B)` is h ↦ h tensor 1;
  `Algebra.TensorProduct.includeRight` is w ↦ 1 tensor w.
- The second conjunct quantifies over h,h' in K units and w,w' in B units.
  Equality of their products implies `∃ a : Aˣ, algebraMap A (FractionRing A) a
  = (h : FractionRing A) / h'`. This is exactly h/h' in A units. A separate
  variable f is unnecessary because either product supplies the common unit f.
- The third conjunct quantifies over h in K units. Being the image of a B unit
  in B_K is equivalent to being the image of an A unit in K. Thus it states
  the entire final reflection clause, in both directions. The flat local map
  is faithfully flat and injective, and localization embeds B in Frac(B), so
  equality in B_K expresses exactly the source's ambient-field identification.

Recorded dependency declarations used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with its full definition
  read; it is Module.Flat for the map's algebra structure.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with its docstring
  and `isNoetherianRing_iff_ideal_fg` read.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  with its docstring and fraction-field definition read. This is the recorded
  normal-domain form of `def-weil-pbc-normal-ring`.

The Mathlib proof-dependency modules for faithful flatness, contraction, exact
tensoring, finite minimal primes, the height bound, DVRs, prime localization,
and Noetherian localization are imported without public visibility. The two stated
project proof dependencies are imported from their recorded upstream modules:
`WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight`
(`Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span`) and
`WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes`
(`Module.injective_pi_localization_associatedPrimes`). Their signatures and
proof docstrings were read. The remaining proof dependencies
`lem-trf-normal-domain-principal-divisor-kernel` and
`lem-sfb-symbolic-powers-flat-prime-extension` have no recorded Lean module and
are therefore not imported; neither is required to type the present statement.
There is no import cycle introduced.

Edge cases checked before writing:

- A is a field: B_K is B, and taking h = 1 supplies existence. Unit reflection
  reduces to the fact that every nonzero base element is already a base unit.
- Identity A → A: B_K is K; factorization may take w = 1 and h = f, and
  the quotient of two admissible h factors lies in A units.
- A DVR base, or the normal nonfactorial local surface from Q57's report:
  no factoriality, principal-height-one-prime, or regularity assumption is added.
- A zero ring is correctly excluded by IsDomain; zero is never admitted as h
  or f because these are units of nonzero rings. Integral fibres are nonempty.
- The empty list of primes over a unit t in the proof is allowed and uses the
  whole-ring intersection. The Lean signature introduces no finite-list restriction.
- The flat local ramified map k[t]_(t) → k[s]_(s), t ↦ s², has a nonintegral
  special fibre and correctly fails hfibres. The fibre condition is substantial.
- The independent universes u and v cover unequal-sized rings; all tensor and
  fraction constructions use Mathlib's inferred maximum universe.

Searches made (all service searches used the prescribed msearch.py wrapper):

- `grep` query `generic.*unit|unit.*generic|unit.*factorization` in `RingTheory`: 13 hits. DVR and power-series factorization hits do not state generic-fibre units over a general normal local base.
- `loogle` query `IsLocalHom, RingHom.Flat, Units`: 0 hits. No exact match.
- `leanfinder` query `For a flat local map of Noetherian domains with integral fibres over a normal domain, every unit on the generic fibre is a base fraction times a unit of the local target ring`: 8 hits. Norm, Zariski main, integral closure, fibre denominator, and stalk-unit results; no unit factorization theorem with these hypotheses and clauses.
- `leansearch` query `Every unit in the generic fiber of a flat local algebra over a normal Noetherian local domain with integral fibers is a product of a base fraction and a unit of the algebra`: 8 hits. Ordinary local unit reflection and localization lemmas; these do not factor a generic-fibre unit or reflect a fraction into base units.
- `rg -n 'generic.*unit|unit.*generic|unit.*factorization|local_generic_unit'`
  in both `lean/WeilConjectures` and `lean/Sheaf`: unrelated categorical units,
  stalk units, DVR factorization, and formally smooth generic-fibre derivations.
  None states this general local algebra theorem. Exact proposed-name searches
  across both source trees and Mathlib returned no declaration.
- `rg -n 'lem-sfb-local-generic-unit-factorization' lean/WeilConjectures`:
  no tag/declaration match.

Source checked: `literature/stacks-project/divisors.tex`,
`lemma-in-image-pullback`, affine paragraph s = a/r through s = ug/r,
and the following local uniqueness paragraph. The tensor representation is the
one used by the source itself, up to the canonical tensor symmetry. No statement
correction, disputed statement, new node, or dependency repair is needed.

Validation: the module compiled successfully through the mandated scompile.py
wrapper in module mode. All variables and universes are explicit, with
`set_option autoImplicit false`. The only postponed proof is the named theorem.
The final dry run and delivery use deliver2.py as required.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
