module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Local relatively ample models of generic symmetric line powers

Source: Raynaud, Faisceaux amples sur les schemas en groupes, XI 1.13 / XI 1.16;
Moret-Bailly VI 3.1; Lan, revised thesis, Lemma 4.2.1.6.
The originals are WANTED; the precise normal Noetherian generic-power formulation
and the specialization proof are agent-written, as recorded in the DAG.
(blueprint: lem-sfb-raynaud-generic-ample-power-model)

Generic comparison is written on the canonical intersection of the generic fibre
with the base-open restriction. Each covering open is nonempty, hence contains the
generic point of the integral base: this intersection is canonically the whole
generic fibre. No line on the total group, rigidification or cubical structure is input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- An ample symmetric line on the proper generic fibre has a positive tensor power
with a relatively ample ordinary line model on each member of an affine base cover.
Relative ampleness is required above every affine open of that member. Empty cover
members may be discarded, so all the generic comparisons concern the entire generic fibre.

Source: Raynaud XI 1.13 / XI 1.16, the auxiliary input of Moret-Bailly VI 3.1 and
Lan revised thesis Lemma 4.2.1.6; originals WANTED, formulation agent-written.
(blueprint: lem-sfb-raynaud-generic-ample-power-model)

Proof plan:
1. Apply lem-sfb-raynaud-generic-ample-symmetrization with S = T, G = H, L = M.
   Noetherian implies locally Noetherian. Normality, smoothness, separatedness,
   finite presentation and the semiabelian geometric fibres are exactly its hypotheses.
   It gives an affine cover and relatively ample Q_i whose generic restrictions are
   (M tensor inverse-pullback M) to positive powers a_i. The extra generic properness
   and symmetry hypotheses are not needed for this application. Discard empty cover members.
2. Choose the supplied symmetry theta. Tensoring id_M with theta identifies the
   symmetrization with M tensor M. Taking a_i tensor powers and associating the
   factors identifies its a_i-th power with M to the power 2*a_i. Set N_i = Q_i
   and d_i = 2*a_i, which is positive. Compose the generic isomorphisms; the
   relative ampleness of the same ordinary lines is unchanged. -/
theorem raynaud_generic_ample_power_model
    {T : Scheme.{u}} [IsAffine T] [IsIntegral T] [IsLocallyNoetherian T]
    (hT : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧
      IsIntegrallyClosed (T.presheaf.stalk t))
    (H : Grp (Over T)) [IsCommMonObj H.X]
    [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (hH : HasSemiabelianGeometricFibres H)
    [IsProper ((Over.pullback (T.fromSpecResidueField (genericPoint T))).mapGrp.obj H).X.hom]
    (M : ((Over.pullback (T.fromSpecResidueField (genericPoint T))).mapGrp.obj H).X.left.Modules)
    [M.IsInvertible] (hM : Scheme.Modules.IsAmple _ M)
    (symmetry :
      (Scheme.Modules.tensorPullback
        ι[((Over.pullback (T.fromSpecResidueField (genericPoint T))).mapGrp.obj H).X].left).obj M ≅
        M) :
    ∃ (I : Type u) (W : I → T.Opens), (⨆ i, W i) = ⊤ ∧
      ∀ i : I, IsAffineOpen (W i) ∧ Nonempty (W i) ∧
        ∃ d : ℕ, 1 ≤ d ∧
          ∃ N : (pullback H.X.hom (W i).ι).Modules, N.IsInvertible ∧
            Nonempty
              ((Scheme.Modules.tensorPullback
                (pullback.fst (pullback.fst H.X.hom (W i).ι)
                  (pullback.fst H.X.hom (T.fromSpecResidueField (genericPoint T))))).obj N ≅
                (Scheme.Modules.tensorPullback
                  (pullback.snd (pullback.fst H.X.hom (W i).ι)
                    (pullback.fst H.X.hom (T.fromSpecResidueField (genericPoint T))))).obj
                  (M.tensorPow d)) ∧
            ∀ V : (W i).toScheme.Opens, IsAffineOpen V →
              ∃ h : ((Scheme.Modules.tensorPullback
                (((pullback.snd H.X.hom (W i).ι) ⁻¹ᵁ V).ι)).obj N).IsInvertible,
                @Scheme.Modules.IsAmple ((pullback.snd H.X.hom (W i).ι) ⁻¹ᵁ V).toScheme
                  ((Scheme.Modules.tensorPullback
                    (((pullback.snd H.X.hom (W i).ι) ⁻¹ᵁ V).ι)).obj N) h := by
  sorry

end AlgebraicGeometry
