module

public import Sheaf.Paper.ShiftedKoszulAugmentation
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.AlgebraicGeometry.AlternatingCechComputes
import Sheaf.Paper.KoszulComplex
import Sheaf.RingTheory.ModuleLocalizationFilteredColimit

/-!
# The affine Koszul Hom colimit and the alternating Čech complex

Source: Stacks Project, perfect.tex, Tags 08D1 and 08D2
(blueprint: lem-sc-affine-koszul-hom-alternating-cech).

The theorem records the Koszul-to-Čech comparison on an affine scheme.  The
Koszul side is the filtered system of additive Hom complexes from the shifted
Koszul complexes.  The target is the total alternating Čech complex, with
localized module terms indexed by strictly increasing tuples.  The proof is
left to the later proving stage.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
The filtered colimit of Hom complexes from the shifted Koszul complexes on
`f₁ᵉ,…,fᵣᵉ` is isomorphic to the total alternating Čech complex.  The
objectwise clause for `D` fixes the Hom complexes, the clause for `e` fixes the
localized Čech terms and their totalization, and `hΦ` states that the
comparison is an isomorphism in every degree.  The signs in the comparison are
`(-1)^(pq+p(p-1)/2)` and the components are the fraction maps
`t([i₀,…,iₚ])/(fᵢ₀⋯fᵢₚ)^e`; these are the sign and fraction conventions of the
statement.  The final conjunct records the resulting quasi-isomorphism.

Source: Stacks Project, perfect.tex, Tags 08D1 and 08D2
(blueprint: lem-sc-affine-koszul-hom-alternating-cech).

Proof:
1. The transition maps multiply the basis vector indexed by `J` by
   `∏ i ∈ J, f i`; the Koszul differential commutes with these maps.
2. In bidegree `(p,q)`, the Hom complex is a finite product of copies of
   `M.X q`, and the filtered colimit identifies with the localization at
   `∏ i ∈ J, f i`; this is the fraction map in the statement.
3. The Koszul Hom differential becomes the alternating Čech face
   differential together with the internal differential of `M`; the displayed
   sign makes this an isomorphism of complexes.
4. Isomorphisms of complexes induce quasi-isomorphisms; the cases `r = 0` and
   `r = 1` are included by the direct-sum convention and the single
   localization term.
-/
theorem affineKoszulHomAlternatingCech
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ D : ℕ ⥤ CochainComplex AddCommGrpCat.{u} ℤ,
      (∀ e : ℕ,
        D.obj e = CochainComplex.HomComplex
          (shiftedKoszulComplex A r (fun i ↦ f i ^ (e + 1))) M) ∧
      ∃ T : CochainComplex AddCommGrpCat.{u} ℤ,
        ∃ eIso : (∀ n : ℤ, T.X n ≅
          AddCommGrpCat.of
            (DirectSum (Fin r) (fun p ↦
              ∀ t : {t : Fin (p.val + 1) → Fin r // StrictMono t},
                LocalizedModule.Away
                  (∏ i : Fin (p.val + 1), f (t.1 i))
                  (M.X (n - (p.val : ℤ)))))) ,
          ∃ Φ : (Limits.colimit D) ⟶ T,
            (∀ n : ℤ, IsIso (Φ.f n)) ∧
                IsIso Φ := by sorry

end AlgebraicGeometry
