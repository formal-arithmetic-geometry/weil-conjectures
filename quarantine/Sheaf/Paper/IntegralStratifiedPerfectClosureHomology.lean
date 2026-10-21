module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.PbcUniformCompleteTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

/-- Cohomology sheaves in degree zero preserve bounded constructible completeness under
the hypotheses of the integral stratified characterization.
Source: Bhatt--Scholze, Proposition 6.8.11(3). The proof uses the bounded Postnikov
devissage and the degree-zero local-module resolution.
(blueprint: lem-weil-pbc-integral-stratified-perfect-closure-homology). -/
theorem integralStratifiedPerfectClosure_homology
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤))) (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K) (q : ℤ) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  let P : ObjectProperty (PbcCompletedDerived T (pbcIntegralDatum l E)) :=
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
  have hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t) := by
    intro t
    simpa only [map_natCast] using
      RingHom.isUnit_map (T.presheaf.germ ⊤ t trivial).hom _hl
  have hP := pbcIntegralUniformComplete_isTriangulated l E T _hdim hInv
  let : P.IsClosedUnderIsomorphisms := hP.1
  let : P.IsTriangulated := hP.2
  let t := DerivedCategory.TStructure.t (C := pbcModules T
    (pbcAdicCompletion T (pbcIntegralDatum l E)))
  -- Isolate degree q using the two standard truncations.
  let L := (t.truncLE q).obj K
  let M := (t.truncGE q).obj L
  have hL : P L :=
    ((integralStratifiedPerfectClosure T l E _hdim _hl).2.2.1 K hK q).1
  have hM : P M :=
    ((integralStratifiedPerfectClosure T l E _hdim _hl).2.2.1 L hL q).2
  have : M.IsLE q := inferInstanceAs (t.IsLE ((t.truncGE q).obj L) q)
  have : M.IsGE q := inferInstanceAs (t.IsGE ((t.truncGE q).obj L) q)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M q
  let H := DerivedCategory.homologyFunctor
    (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) q
  have : IsIso (H.map ((t.truncLTι (q + 1)).app K)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K (q + 1) q (by omega)
  have : IsIso (H.map ((t.truncGEπ q).app L)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app L q q le_rfl
  let eL : H.obj L ≅ H.obj K :=
    H.mapIso ((t.truncLEIsoTruncLT q (q + 1) rfl).app K) ≪≫
      asIso (H.map ((t.truncLTι (q + 1)).app K))
  -- The truncation maps identify the shifted-heart coefficient with H^q(K).
  let eY : Y ≅ H.obj K :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app Y).symm ≪≫
      (H.mapIso e).symm ≪≫ (asIso (H.map ((t.truncGEπ q).app L))).symm ≪≫ eL
  -- Moving the isolated degree q to degree zero requires the shift by +q.
  apply P.prop_of_iso
    ((shiftFunctor _ q).mapIso e ≪≫
      ((DerivedCategory.singleFunctors _).shiftIso q 0 q (by omega)).app Y ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso eY)
  exact P.le_shift q M hM

end AlgebraicGeometry.Scheme

