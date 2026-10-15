module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSections
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionCanonicalComparison
import Sheaf.AlgebraicGeometry.AffineChartTotalTensor
import Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance (X : Scheme.{u}) (L : X.Modules) :
    ((curriedTensor X.Modules).obj L).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf L

/-- The canonical chart coordinates commute with any augmented semilinear tensor comparison.

Proof in words: the augmentation formula for `a` gives the first chain square by
`tensorResolutionChartAugmentation_naturality`. The coefficient formula for `b`
and the pure-tensor formula for `k` give the second chain square by
`tensorResolutionChartTensorIso_naturality`: check each nonpositive degree on
pure tensors, then use the tensor-product universal property, and use the zero
object in the remaining degrees. The common K-flat zigzag is natural for those
two squares, so `tensorResolutionCoordinateSheafIso_naturality_of_squares`
gives equality of the sheaf comparison maps. Apply global sections on the two
affine spectra and the units of the affine restriction adjunction.
`tensorResolutionSection_naturality` identifies the resulting right-hand map
with restriction of the global homology sheaf. Finally,
`tensorResolutionSemilinearMap_homology` identifies the left-hand map with
`HomologicalComplex.homologyMap k` followed by `mapHomologyIso`. This is the
displayed equation after applying the two section equivalences. -/
theorem tensorResolutionCoordinateSections_naturality
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U, ProjectiveResolution (MA U))
    (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlat (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ)
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (b : NA U →ₛₗ[(Y.presheaf.map (homOfLE h).op).hom] NA V)
    (a : (P U).complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj
        (P V).complex)
    (k : ((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj (P U).complex ⟶
      ((ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex
        (.down ℕ)).obj
        (((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj (P V).complex))
    (ha : ∀ x : (P U).complex.X 0,
      sM V ((P V).π.f 0 (a.f 0 x)) =
        M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x)))
    (hb : ∀ y : NA U,
      sN V (b y) = N.val.map (homOfLE h).op (sN U y))
    (hk : ∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
      k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
        (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let Q := (CochainComplex.mapBifunctor K
      ((CochainComplex.singleFunctor Y.Modules 0).obj N)
      (curriedTensor Y.Modules)).homology (-(n : ℤ))
    let e := (((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj
      (P V).complex).sc n |>.mapHomologyIso
        (ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom)
    ∀ x, Q.val.map (homOfLE h).op
        (tensorResolutionCoordinateSections Y M N U (MA U) (NA U)
          (sM U) (sN U) (P U) K F q s hK hF hq hs n x) =
      tensorResolutionCoordinateSections Y M N V (MA V) (NA V)
        (sM V) (sN V) (P V) K F q s hK hF hq hs n
        (e.hom (HomologicalComplex.homologyMap k n x)) := by
  sorry

end AlgebraicGeometry
