## Worker report

The module states `flat_smooth_fibre_smooth_at_prime`. It quantifies commutative rings `R,S`, a ring map `φ`, primes `p` and `q`, and an algebra structure on `S`; `hφ` identifies the algebra map with `φ`. The finite-presentation-near-`q` hypothesis is rendered as `∃ g : S, g ∉ q ∧ Algebra.FinitePresentation R (Localization.Away g)`. Flatness is rendered by `Module.Flat R S`. The fibre is Mathlib's `p.Fiber S`; smoothness at a prime of the fibre is rendered by an existential prime `Q` with an explicit `Q.IsPrime` witness and `@Algebra.IsSmoothAt p.ResidueField (p.Fiber S) ... Q hQ`. The conclusion is `Algebra.IsSmoothAt R q`.

Dependencies used: `Ideal.Fiber`, `Ideal.ResidueField`, and `Algebra.IsSmoothAt` from Mathlib (`Mathlib.RingTheory.Smooth.Fiber` and residue-field fibre modules); `Algebra.FinitePresentation` from `Mathlib.RingTheory.FinitePresentation`; `Module.Flat` from Mathlib flatness modules. The recorded localization, finite-presentation, flat-map, and singular-ideal dependency nodes are Mathlib notions and require no project modules.

Edge cases checked: `p` and `q` are explicit prime ideals; the fibre-prime witness carries its prime instance explicitly, avoiding an implicit-instance gap. The finite-presentation localization allows `g = 0` only when `0 ∉ q`, as required by the stated neighborhood condition.

Searches: `rg` over `lean/Sheaf` and the source repository for smooth-at-prime, finite-presentation, and flat-map declarations; Mathlib checks of `Algebra.IsSmoothAt`, `Algebra.FinitePresentation`, `Module.Flat`, `Ideal.Fiber`, and `Ideal.ResidueField`. No existing project declaration matched the node.

## Earlier second reading (a previous round; superseded)

Independent rereading confirms that every quantified object and each hypothesis is present in the Lean signature, and the conclusion is the smooth-at-prime predicate `Algebra.IsSmoothAt R q`. No mismatch was found.

## Second reading by K1

The node introduces a ring homomorphism `φ : R →+* S`, a prime `q : Ideal S`,
its contraction `p = φ⁻¹(q)`, the fibre `p.Fiber S`, and the canonical prime
`Q` corresponding to `q`.  It assumes: (1) some `g ∉ q` with
`Algebra.FinitePresentation R (Localization.Away g)`; (2) flatness of the induced
local map `R_p → S_q`; and (3) smoothness of `κ(p) → p.Fiber S` at `Q`, concluding
smoothness of `R → S` at `q`.

The Lean renders these as `φ`, `q` with `[q.IsPrime]`, `p` with `[p.IsPrime]`,
`hpq : p = Ideal.comap φ q`, and `hφ : algebraMap R S = φ`.  The localization
hypothesis is exactly `hfp`.  Local flatness is rendered by
`hflat : RingHom.Flat (Localization.localRingHom p q φ hpq)`, which uses the
localizations at the contracted and target primes.  The fibre is Mathlib's
`p.Fiber S`; `Q` has an explicit prime witness and `hQeq` identifies it with
`(PrimeSpectrum.preimageEquivFiber R S ⟨p, hp⟩ ...).asIdeal`, the kernel prime
of the canonical fibre-to-residue-field map.  `hsmooth` is the required
`@Algebra.IsSmoothAt p.ResidueField (p.Fiber S) ... Q hQ`, and the conclusion is
`Algebra.IsSmoothAt R q`.

The earlier worker had three mismatches: it omitted `p = φ⁻¹(q)`, assumed global
`Module.Flat R S` instead of flatness of the local map, and quantified over an
arbitrary smooth fibre prime.  I added `hpq`, replaced the flatness hypothesis
with `RingHom.Flat (Localization.localRingHom p q φ hpq)`, and added `hQeq` for
the canonical prime.  The node's mathematical statement and source were retained.

Edge cases checked: primes are explicit (including zero or empty-spectrum cases);
`p.Fiber S` is Mathlib's tensor fibre and no nonzero hypothesis is imposed; no
finite-index, characteristic, or universe restriction is added; `g` may be any
neighborhood element outside `q`.

Searches (`rg` and Mathlib source inspection) checked `Algebra.IsSmoothAt`,
`Ideal.Fiber`, `PrimeSpectrum.preimageEquivFiber`, `Localization.localRingHom`,
`RingHom.Flat`, and the project/source trees for an existing theorem.  No exact
existing declaration was found.  The repaired module compiles cleanly with
`scompile.py`; its only proof is `sorry` as required for stage 2.

## Reviewer fix (R-fss1040)

Smoothness at a prime was rendered by Mathlib `Algebra.IsSmoothAt` (formal smoothness of the local ring S_q), which is not the node's notion. The node's [def-weil-pbc-singular-ideal] is recorded at `Sheaf.RingTheory.SingularIdeal`, whose `Algebra.IsSmoothAtPrime R q` is exactly `∃ g ∉ q, Algebra.Smooth R (Localization.Away g)` (as in K1 e46109f71). Both hypothesis (3) and the conclusion now use it. The statement was also normalised to the landed form: `[Algebra R S]`, `q : PrimeSpectrum S`, `p = PrimeSpectrum.comap (algebraMap R S) q` definitionally (no separate φ/hφ/hpq), local flatness `(Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) rfl).Flat`, and the fibre prime `PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩` directly (no auxiliary Q/hQ/hQeq). Docstring carries the node's proof in words. Compiled clean with SHEAF_GROUP=L.
