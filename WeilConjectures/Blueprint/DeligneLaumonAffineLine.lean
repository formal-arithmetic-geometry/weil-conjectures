/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

/-!
# Deligne–Laumon on the affine line

The affine-line weight estimate: if `j : U₀ ↪ 𝔸¹` over `𝔽_q` is a dense open immersion
and `F` is pure of weight `w` and unramified at infinity, then `Hᵣ_c (𝔸¹, j_* F)` has
weights at most `w + r`. The essential case is degree one; it is proved for irreducible
nonconstant sheaves by the Fourier transform of
`WeilConjectures.Blueprint.FourierTransform` and then extended along a composition
filtration.

Blueprint block `sec-deligne-laumon-a1`.
-/
