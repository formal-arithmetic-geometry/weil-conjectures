module

public import Sheaf.AlgebraicGeometry.SpaceCoherentAdicSystem
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.NoetherianAffineAtlasRelation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.FormalSystemsPushPullComparison
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine
import WeilConjectures.AlgebraicGeometry.TheoremFormalFunctions
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import WeilConjectures.AlgebraicGeometry.FormalSystemsPushPullAffineAnnihilation
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentAbelian

/-! # Formal push-pull comparison along a proper modification

Source: Stacks Project, More on Morphisms of Spaces, Tag 08BD,
lemma-inverse-systems-push-pull, and Tag 08BA
(blueprint: lem-sfb-space-adic-modification-push-pull).

The extended ideal is specified by its epimorphic factorization of the canonical
ideal tensor map. This determines its subobject uniquely. Being an isomorphism off
V(K) is tested on all etale charts where the ideal is the unit ideal. The comparison
of quotient diagrams is normalized by the actual quotient projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A representable proper modification gives a coherent direct image and a comparison
of coherent adic systems, with one positive exceptional-ideal exponent annihilating
all ordinary component kernels and cokernels. The comparison commutes with the fixed
tensor-adjunction unit and the given pullback-system isomorphism.
Source: Stacks Project, More on Morphisms of Spaces, Tag 08BD, including the comparison
equation in its proof; Tag 08BA, condition (1)
(blueprint: lem-sfb-space-adic-modification-push-pull).

Proof:
1. Proper coherent direct image (lem-sfb-space-proper-coherent-higher-images) makes
H = q_* E coherent. Choose a finite affine etale atlas by
lem-sfb-space-flat-proper-fp-locality; lem-sfb-noetherian-affine-atlas-relation makes
it and its relation Noetherian. Representability makes the source on each chart a
scheme; properness and the isomorphism away from the ideal survive base change.
2. Define gamma by the tensor-adjunction unit followed by q_* beta. The quotient
projection E -> E/I^(n+1)E kills J^(n+1) on direct image. The quotient universal
property defines kappa. Its uniqueness gives transition compatibility. Etale
restriction preserves these maps by lem-trf-space-etale-module-pushforward-restriction.
3. Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
lem-sfb-scheme-etale-module-exact-finiteness-comparison on an affine chart, and apply
lem-weil-pbc-formal-systems-push-pull-comparison, with level n denoting n+1.
4. Uniqueness on that chart follows from lem-weil-pbc-coherent-formal-modules-affine
and degree-zero lem-weil-pbc-theorem-formal-functions: the inverse limit of kappa is
an isomorphism and the projections from the source limit are surjective. The faithful
chart realization of lem-sfb-space-qcoh-affine-chart-calculus detects equality of maps.
5. The local comparisons agree on all affine opens of the atlas relation by uniqueness.
Glue their components by the sheaf condition. The transition and comparison equations
hold locally and hence globally; no termwise kernel computation in Coh(X,J) is used.
6. Apply lem-weil-pbc-formal-systems-push-pull-affine-annihilation to this very map on
the affine atlas, then lem-weil-pbc-formal-systems-annihilated-by-power to obtain a
single positive exponent for its ordinary component kernels and cokernels. The exact
scheme/etale comparison transports this assertion to the small etale site.
7. By lem-sfb-space-coherent-abelian these kernels and cokernels are coherent.
Restriction preserves ordinary kernels, cokernels and local ideal products. Thus the
same power kills them globally, because it kills them on a surjective etale cover. -/
theorem exists_adicModification_pushPull
    {S : Scheme.{u}} {V X : AlgebraicSpace S}
    (hlnV : ∀ T : V.EtaleSite, IsLocallyNoetherian (V.etaleForget.obj T))
    (hqcV : CompactSpace (Point V.obj.obj)) (hqsV : IsAbsolutelyQuasiSeparated V)
    (hlnX : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqcX : CompactSpace (Point X.obj.obj)) (hqsX : IsAbsolutelyQuasiSeparated X)
    (q : V ⟶ X) (hqrep : IsRepresentable q.hom.hom) (hqproper : MapIsProper q)
    (J K : QuasiCoherentIdeal X)
    (hU : ∀ T : X.EtaleSite, idealSectionImage K.val.arrow T = ⊤ →
      IsIso (Limits.pullback.snd q.hom.hom T.obj.hom))
    (I : QuasiCoherentIdeal V)
    (hI : ∃ e : (moduleTensorPullback q).obj (J.val : X.Modules) ⟶ (I.val : V.Modules),
      Epi e ∧ e ≫ I.val.arrow = idealTensorMap q J)
    (M : CoherentAdicSystem X J hlnX hqcX hqsX)
    (E : V.Modules) (hEqc : E.IsQuasicoherent)
    (hEcoh : ∀ T : V.EtaleSite, RingedSpace.IsCoherent (V.etaleForget.obj T).toRingedSpace
      ((V.schemeRestriction T).obj E))
    (β : (coherentAdicPullbackDiagram q).obj M.obj ≅
      (coherentAdicCompletionDiagram I).obj E) :
    ∃ hH : ((moduleDirectImage q).obj E).IsQuasicoherent ∧
        ∀ T : X.EtaleSite, RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj ((moduleDirectImage q).obj E)),
      ∃ κ : (coherentAdicCompletionDiagram J).obj ((moduleDirectImage q).obj E) ⟶
          (coherentAdicCompletionDiagram I).obj E ⋙ moduleDirectImage q,
        ∃ a : M ⟶ (coherentAdicCompletion J hlnX hqcX hqsX).obj
            ⟨(moduleDirectImage q).obj E, hH⟩,
          CoherentAdicKernelCokernelKilled K a.hom ∧
          (∀ n : ℕ,
            (adicQuotientModel J).projection ((moduleDirectImage q).obj E) n ≫
                κ.app (op n) =
              (moduleDirectImage q).map ((adicQuotientModel I).projection E n)) ∧
          (∀ n : ℕ, a.hom.app (op n) ≫ κ.app (op n) =
            (moduleTensorAdjunction q).unit.app (M.obj.obj (op n)) ≫
              (moduleDirectImage q).map (β.hom.app (op n))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
