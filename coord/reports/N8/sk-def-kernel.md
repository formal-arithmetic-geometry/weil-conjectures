## Worker report

The module `Sheaf.FourierTransform.KernelNatCastEqZero` defines
`AlgebraicGeometry.Etale.fourierKernelOfNatCastEqZero`. Its data are the existing
prime-field Artin–Schreier sheaf of the pairing; no theorem or sorry is added.
The node's statement and dependency list are unchanged.

Clause-by-clause reading:

- A prime `p` is `{p : ℕ} [Fact p.Prime]`.
- A commutative coefficient ring in which `p` is invertible is
  `(Λ : Type (u + 1)) [CommRing Λ] [Invertible (p : Λ)]`. Choosing an inverse
  carries no extra mathematical assumption: the inverse of a unit is unique.
- Arbitrary scheme maps to a common base are `{S V V' : Scheme.{u}}`,
  `(π : V ⟶ S)` and `(π' : V' ⟶ S)`. Their fiber product `W` is `pullback π π'`.
- The exact characteristic hypothesis, including empty `W`, is
  `(h : (p : Γ(pullback π π', ⊤)) = 0)`. It is deliberately not `CharP`.
- The pairing/global function is `(b : Γ(pullback π π', ⊤))`.
- The additive character is `(Ψ : AddChar (ZMod p) Λ)`. Mathlib's
  `AddChar.map_zero_eq_one` and `AddChar.map_add_eq_mul` give the two required
  identities. Though values are expressed in `Λ`, each is automatically a unit:
  `Ψ(a) Ψ(-a) = Ψ(0) = 1`, and the same holds in the opposite order. Thus this
  is exactly a character into `Λˣ`, also for the zero coefficient ring.
- The result `Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)`
  is the required sheaf of modules on the small étale site, with no finite,
  nontrivial-character, separatedness or finite-type condition.
- Its body `artinSchreierSheafOfNatCastEqZero h Ψ b` first installs
  `overSpecZModOfNatCastEqZero h`, then uses `artinSchreierSheafOf` for
  `ULift (ZMod p)` and the lifted character. The latter is literally the inverse
  image of `artinSchreierSheaf` along `AffineSpace.homOfVector` representing `b`.
  This renders `K_psi := L_{Psi,b} = b^* L_Psi` by definition, without a
  base-change claim. `ULift` places the prime field in the scheme universe and
  changes neither its arithmetic nor its character.
- The vector-bundle paragraph specifies inputs to this same definition, not a
  separate construction: insert the bundle and its dual for `V,V'` and their
  evaluation global function for `b`. Rank zero is allowed; rank one gives the
  product global function `x ξ`. The docstring explicitly records both
  specializations, the finite field from `FourierSetting.field`, the composite
  to the prime-field affine line, and the intended prime-field meaning of
  `L_{psi(x ξ)}`. No identification with the trace-character construction is
  asserted and no adic coefficient hypotheses are added.

Dependency declarations read and used:

- `WeilConjectures.FourierTransform.ArtinSchreier`:
  `AlgebraicGeometry.Etale.artinSchreierSheaf` (image of the specified character
  idempotent) and `AlgebraicGeometry.Etale.artinSchreierSheafOf` (its inverse
  image along the global function), the recorded dependency
  `def-fd-artin-schreier-sheaf`. Its `blueprint_update` is the current general
  finite-field construction and matches these declarations.
- `Sheaf.Paper.FourierSetting`: `WeilConjectures.FourierSetting`, the recorded
  `def-fourier-set` declaration, is publicly imported for the application
  conventions, without imposing those conventions on the general definition.
- `Sheaf.FourierTransform.ArtinSchreierFiniteLisse`:
  `AlgebraicGeometry.Etale.artinSchreierSheafOfNatCastEqZero` and its canonical
  structure-map helpers `overSpecZModOfNatCastEqZero` and
  `zmodRingHomOfNatCastEqZero` are reused. These are already published helper
  definitions owned by `lem-fd-artin-schreier-finite-lisse`; the lissity theorem
  in that module is not used, so its finite-coefficient assumption is not
  imported into this definition. No dependency repair or new notion is needed.

Edge cases checked before writing: empty fiber product (global sections are the
zero ring, so the natural-number equality still supplies the canonical map from
`F_p`); zero coefficient ring; `p = 2`; trivial character; zero pairing; vector
bundle rank zero and rank one. The definition requires neither nonempty schemes
nor nonzero coefficient rings. The recorded upstream Fourier kernel requires
`CharP Γ(W, ⊤) p`, which excludes the empty case, and hence cannot be attached to
this node. The existing general Artin–Schreier helper supplies all the data
without that restriction. Scheme universe `u` is arbitrary and coefficients use
the same `u + 1` site-size convention as the dependency; universes can be enlarged
for arbitrary input schemes and coefficients.

Searches made (2026-10-22):

- `msearch.py ... leanfinder` with query "Fourier kernel on a fiber product of
  schemes as the Artin Schreier sheaf pulled back along a global function":
  eight unrelated Mathlib scheme pullback/limit hits, no character sheaf kernel.
- `msearch.py ... loogle` with query "artinSchreierSheaf, fourierKernel": no hits;
  unknown identifier `artinSchreierSheaf` in Mathlib.
- `msearch.py ... grep` with query `artinSchreierSheaf|fourierKernel` in
  `AlgebraicGeometry`: no Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for `fourierKernel`,
  `artinSchreierSheaf`, `ArtinSchreier`, and `sk-def-kernel`: found upstream
  `FourierTransform.Defs.fourierKernel`, its `CharP`-restricted definition, the
  general Artin–Schreier dependency and the existing natural-cast-zero helper.
  Adic Weil-sheaf kernels use different coefficient categories and hypotheses.
- `rg` for `fourierKernelOfNatCastEqZero` in both Lean trees and the upstream
  declaration index: no declaration with this name.

Source read: current main-20261015 `sk-def-kernel/_section.md`, the node in full,
its stage-1 review, both statement-dependency nodes including the Artin–Schreier
blueprint update, and the full relevant Lean definitions and docstrings.
The source has no integrand clause here; the title is historical. No statement
correction and no STATEMENT-DISPUTED flag are needed.

Validation: the delivered module is checked individually using `scompile.py`;
then `deliver2.py --no-push` runs the server preflight and repeats the file check.
No global build or direct repository mutation is performed.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
