module
public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison
import Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyGluing

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
/-- Target affine dictionary for a source comparison with a normalized linear lift.
Source: Stacks Project, Tags 02KH (both parts), 01XJ, 01E4 and 03FD.
(blueprint: new-flat-base-change-affine-target)

Proof: Write A = Gamma(V), B = Gamma(W), H = HOver(h,N,p), T = B tensor_A H,
and C = HOver(h_B,N_B,p). First use the canonical module/abelian comparison on
section complexes, denoted e0, rather than the supplied arbitrary additive eH.
As in the source construction, affine Leray and the tensor-pullback section
formula give a B-linear equivalence a0 from T to Gamma(g^*P,W), normalized by e0.
The affine chart square identifies U_B with f' inverse W and N_B with g'^*F
restricted there. Higher images of the latter are quasi-coherent by the qcqs
higher-image theorem; affine vanishing makes its cocycle-normalized Leray edge
invertible. Composing the chart and module/abelian comparisons with this edge
gives a canonical B-linear equivalence b0 from C to Gamma(Q,W).

On the common section complexes, an augmented resolution comparison computing
moduleCohomologyFMap(D.psi) and the exact inverse-image Ext comparison compute
the same map of cohomology classes. The augmentation and components equations
in D remove changes of resolutions, and D.unit_square identifies the coefficient
map with the pullback unit. Thus b0(baseChangeLinear(y)) is the displayed target
class evaluated on e0 inverse y, after restriction to W. This compatibility is
proved on complexes, without assuming the parent dictionary or beta isomorphism.

Let c : T equiv_B C be the canonical H.baseChange equivalence. It is invertible
by flat cohomology base change: B is A-flat by g.flat_appLE, U is qcqs by f and
V affine, and N is quasi-coherent. More explicitly, the separated case uses a
finite affine Cech cover and exact tensor; compact-open induction and the
Mayer-Vietoris gluing theorem extend it to qcqs U. No resolution beta is used.
Regard the supplied bijective linear a as an equivalence and put
b = b0 composed with c composed with a0 inverse composed with a composed with
c inverse. All factors are B-linear equivalences. Source normalization at s = 1
gives a(1 tensor xi) = a0(1 tensor e0(eH inverse xi)). Since
baseChangeLinear(xi) = c(1 tensor xi), cancellation gives
b(baseChangeLinear(xi)) = b0(baseChangeLinear(e0(eH inverse xi))). Apply the
canonical compatibility above and cancel e0 inverse with e0; this is the
required formula. Empty opens, zero coefficients and degree zero obey the same
identities. The normalized lift assumption is essential: an arbitrary additive
eH need not induce a B-linear change of coordinates. -/
theorem Scheme.Modules.exists_flatBaseChange_affine_target
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] [Flat (pullback.snd g f)]
    (F : X.Modules) [F.IsQuasicoherent]
    (I : InjectiveResolution F)
    (J : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f g F I J V) :
    letI : Algebra Γ(S, V) Γ(S', W) := (g.appLE V W eVW).hom.toAlgebra
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F
    let P := ((Scheme.Modules.pushforward f).rightDerived p).obj F
    let Q := ((Scheme.Modules.pushforward (pullback.fst g f)).rightDerived p).obj
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj F)
    ∀ (eH : ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+
          Scheme.Modules.HOver h N p)
      (a : TensorProduct Γ(S, V) Γ(S', W) (Scheme.Modules.HOver h N p) →ₗ[Γ(S', W)]
        Γ((Scheme.Modules.tensorPullback g).obj P, W)),
      Function.Bijective a →
      (∀ (s : Γ(S', W)) (xi : Scheme.Modules.HOver h N p),
        a (s ⊗ₜ[Γ(S, V)] xi) = s •
          ((Scheme.Modules.tensorPullback g).obj P).presheaf.map (homOfLE eVW).op
            (Scheme.Modules.Hom.app
              ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app P)
              V (D.sourceClass p (eH.symm xi)))) →
      ∃ b : Scheme.Modules.HOver (Scheme.Modules.baseChangeSnd (S := Γ(S', W)) h)
          (Scheme.Modules.baseChangedModule (S := Γ(S', W)) h N) p →ₗ[Γ(S', W)]
          Γ(Q, W),
        Function.Bijective b ∧
        (∀ xi : Scheme.Modules.HOver h N p,
          b (Scheme.Modules.H.baseChangeLinear (S := Γ(S', W)) h N p xi) =
            Q.presheaf.map (homOfLE eVW).op
              (D.targetClass p
                (Scheme.Modules.moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
                  ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p (eH.symm xi)))) := by
  sorry
end AlgebraicGeometry
