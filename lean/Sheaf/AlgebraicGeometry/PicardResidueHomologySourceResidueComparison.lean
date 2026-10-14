module

public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # A strictly perfect affine model computes residue cycle homology

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-picard-residue-homology-comparison-source-residue)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The explicit degree-one residue quotient computes the derived fibre of a
represented object, independently of any geometric direct-image presentation.
Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-picard-residue-homology-comparison-source-residue)

Proof: Set A = Gamma(W,U) and let P be terminal sections of K, with the
section differentials. The finite free retractions in hK remain retractions
under sections, so every P.X j is a finite projective A-module, hence flat.
The bounds in hK give bounds for P. Thus P is K-flat by Tag 064K.
Transport the affine associated-sheaf adjunction to the localized site. Its
counit reconstructs finite free sheaves from their sections. Naturality makes
this counit invertible also on their retracts: the inverse on a retract is
obtained by composing the inclusion, the free counit's inverse and the
projection. Hence its components on K are invertible, and counit naturality
makes them a complex isomorphism from sheafified P to K (Tag 01IB).
Compose its derived image with hE. Apply affine_kFlat_residuePullback_model
to P and this representative. The resulting model of the derived fibre is
the associated sheaf of P tensored with the residue field at the affine
chart point. Affinity identifies that point's prime with the kernel of
W.evaluation U w hwU, which is p by hp. The chart and open-immersion residue
isomorphisms identify its field with W.residueField w, compatibly with A's
action. Therefore the model's section complex, after forgetting scalars,
is canonically isomorphic to the complex with terms affineResidueTerm.
These term comparisons are natural in module maps, so identify its
differentials with affineResidueDifferential, including degrees 0,1,2.
Sections on the one-point residue spectrum are exact; taking degree-one
homology therefore computes derivedFiberCohomology W E 1 w. Finally d^2=0
puts incoming boundaries in outgoing cycles. Module homology is the quotient
of these cycles by these boundaries (Tag 010V); its canonical projection has
exactly the kernel described by affineResidueCycleClass_surjective_kernel.
The first isomorphism theorem gives the stated additive equivalence. The
argument does not assume that differentials vanish or that projective terms
are free; it includes the zero complex and rank-zero retracts. -/
theorem picard_residue_homology_source_residue_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    Nonempty (affineResidueCycleHomology W U p K ≃+
      derivedFiberCohomology W E 1 w) := by sorry

end AlgebraicGeometry.Scheme
