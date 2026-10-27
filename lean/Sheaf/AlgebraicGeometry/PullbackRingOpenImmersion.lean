module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Principal open unions in the spectrum of a ring fibre product

Source: Stacks Project, Limits, Tag 01Z9 (lemma-diagram), and More on Algebra,
Tag 01Z8 (lemma-diagram-localize) (blueprint: lem-sfb-pullback-ring-open-immersion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The second projection from the ring fibre product induces isomorphisms on the
specified localizations, and an open immersion on their union, with the specified image.

Source: Stacks Project, Tag 01Z9 (lemma-diagram), using Tag 01Z8
(lemma-diagram-localize) (blueprint: lem-sfb-pullback-ring-open-immersion).

Proof plan:
1. For P = B ×_R R', the sequence 0 → P → B ⊕ R' → R, with last map
   (b,r) ↦ s(b) - t(r), is exact at its first two terms as P-modules. Linearity
   follows from the defining compatibility of each element of P; no map is assumed
   surjective.
2. Localize at h = (g_l,f_l), using lem-weil-pbc-localization-module-exact
   (LocalizedModule.map_exact). The localized modules identify with B_g, R'_f,
   and R_s(g), since h acts on them by g, f, and s(g). For the direct sum use
   a common denominator. Exactness identifies P_h with B_g ×_{R_s(g)} R'_f,
   compatibly with the two projection homomorphisms.
3. Since the natural B_g → R_s(g) is an isomorphism, the second projection
   from this fibre product is an isomorphism: its inverse sends z to
   (s_g⁻¹(t_f(z)), z). Thus the canonical localization of the second projection
   is bijective, with fraction formula (b,r)/h^n ↦ r/f^n.
4. By lem-weil-pbc-principal-localization-open-immersion, spectra of the
   localized rings identify with the respective principal opens. The preceding
   isomorphism is the restriction of Spec(q), because the projection square
   commutes. Also Spec(q)⁻¹(D(h_l)) = D(f_l), directly on prime ideals.
5. If two points of the union have the same image, choose an index whose
   source principal open contains the first. The inverse-image equality places
   the second in that same open, where injectivity is known. Apply
   lem-weil-pbc-open-immersion-injective-local-source to these local open
   immersions. Each source principal open maps onto D(h_l), proving the image
   formula. The empty family and zero rings satisfy the same argument. -/
theorem pullbackRing_principalOpenUnion_isOpenImmersion
    {B R R' : CommRingCat.{u}} (s : B ⟶ R) (t : R' ⟶ R)
    (m : ℕ) (f : Fin m → R') (g : Fin m → B)
    (hf : ∀ l : Fin m, t.hom (f l) = s.hom (g l))
    (hs : ∀ l : Fin m, Function.Bijective (Localization.awayMap s.hom (g l))) :
    (∀ l : Fin m, Function.Bijective
      (Localization.awayMap (CommRingCat.pullbackCone s t).snd.hom
        ⟨(g l, f l), (hf l).symm⟩)) ∧
    IsOpenImmersion
      (Scheme.Opens.ι (X := Spec R') (⨆ l : Fin m, PrimeSpectrum.basicOpen (f l)) ≫
        Spec.map (CommRingCat.pullbackCone s t).snd) ∧
    Set.range
      (Scheme.Opens.ι (X := Spec R') (⨆ l : Fin m, PrimeSpectrum.basicOpen (f l)) ≫
        Spec.map (CommRingCat.pullbackCone s t).snd) =
      (⨆ l : Fin m, (PrimeSpectrum.basicOpen
        (⟨(g l, f l), (hf l).symm⟩ : (CommRingCat.pullbackCone s t).pt) :
          (Spec (CommRingCat.pullbackCone s t).pt).Opens)).carrier := by
  sorry

end AlgebraicGeometry
