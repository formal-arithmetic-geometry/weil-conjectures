module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents

/-!
# Rational extension near a smooth section

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §4.4, proof of Theorem 1,
printed pp. 109–110 (PDF pp. 115–116), the reduction to the diagonal, in its
smooth-section form (blueprint: lem-sfb-smooth-section-rational-extension).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A rational map agreeing with a morphism along a smooth section extends near that section.
Source: BLR, Néron Models, §4.4, proof of Theorem 1, printed pp. 109–110, reduction to
the diagonal (blueprint: lem-sfb-smooth-section-rational-extension).

Proof:
1. Smooth normal ascent (lem-sfb-smooth-normal-ascent) and smooth reduced/local-Noetherian
   ascent (lem-trf-smooth-reduced-dense-pullback) make X normal, reduced and locally Noetherian.
   Take the union V of open B-morphism extensions of v. Relative separated equality
   (lem-sfb-relative-separated-dominant-ext) identifies them on overlaps, since D is dense
   and X reduced. Glue by lem-weil-pbc-scheme-morphism-gluing; D lies in V.
2. The inverse image of D along a contains every generic point of T, so is dense. Relative
   separated equality shows the glued map composed with a equals b on the inverse image of V.
3. Fix z in T. Using lem-weil-pbc-affine-opens-basis and
   lem-weil-pbc-morphism-factors-through-open-subscheme, choose affine neighbourhoods B₀ of
   t(z), H of b(z) over B₀, and W₀ of a(z) over B₀. The affine W₀ is Noetherian by
   lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.
   By lem-trf-normal-topologically-noetherian-components retain its integral clopen component
   through a(z), and choose an affine neighbourhood W₁ inside it.
4. Shrink T to T' = a⁻¹(W₁) ∩ b⁻¹(H) ∩ t⁻¹(B₀), and W₁ to W = W₁ ∩ q⁻¹(T'). The
   section and retraction restrict; smoothness follows from
   lem-weil-pbc-smooth-restrict-open-subschemes and Noetherianity from
   lem-weil-pbc-noetherian-open-subscheme-noetherian. The normal integral W has a dense
   nonempty open J = W ∩ V ∩ v_V⁻¹(H), since the section over T' ∩ a⁻¹(D) lies in J.
5. By lem-sfb-normal-affine-rational-indeterminacy, the map J → H has maximal extension
   E → H with empty or pure-codimension-one boundary F. It is over B₀: its structural
   map agrees with tq on dense J, and B₀ is affine, hence separated over Spec ℤ (the
   diagonal corresponds to the surjective multiplication map). Relative separated equality
   then identifies E → Y with v_V on E ∩ V and with v on E ∩ D. Thus E lies in V.
6. On the restricted section, a'⁻¹(E) = a'⁻¹(V): for the reverse inclusion use step 2 and
   b(T') ⊆ H. Hence a'⁻¹(F) contains no point with local dimension at most one, since
   open restriction preserves local rings. Apply lem-sfb-smooth-section-divisor-intersection
   to force a'⁻¹(F) empty, so a(z) lies in V.
7. This holds for every z. Take N = V and its glued B-morphism. All constructions were
   local on X and Y. If T is empty, q forces X empty and the empty open suffices. -/
theorem smooth_section_rational_extension
    {B T X Y : Scheme.{u}} [IsNoetherian T]
    (hnormal : ∀ z : T, IsDomain (T.presheaf.stalk z) ∧
      IsIntegrallyClosed (T.presheaf.stalk z))
    (t : T ⟶ B) (r : Y ⟶ B) [IsSeparated r]
    (q : X ⟶ T) [Smooth q] (a : T ⟶ X) (ha : a ≫ q = 𝟙 T)
    (D : X.Opens) (hD : Dense (D : Set X))
    (v : D.toScheme ⟶ Y) (hv : v ≫ r = D.ι ≫ q ≫ t)
    (b : T ⟶ Y) (hb : b ≫ r = t)
    (hcodim : ∀ z : T, ringKrullDim (T.presheaf.stalk z) ≤ 1 → a z ∈ D)
    (hagrees : (a ∣_ D) ≫ v = (a ⁻¹ᵁ D).ι ≫ b) :
    ∃ (N : X.Opens) (w : N.toScheme ⟶ Y),
      (∀ z : T, a z ∈ N) ∧ w ≫ r = N.ι ≫ q ≫ t ∧
      X.homOfLE (inf_le_left : N ⊓ D ≤ N) ≫ w =
        X.homOfLE (inf_le_right : N ⊓ D ≤ D) ≫ v := by
  sorry

end AlgebraicGeometry
