/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.QuasicoherentSheafHom
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation

import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.CategoryTheory.FiniteTypeRestrictionExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact

/-! # Tensor and internal Hom under the small étale comparison

Source: Stacks Project, Descent, Tag 06VE(7),(8); Modules on Sites, Tags 03EL and 0GN2
(blueprint: lem-sfb-scheme-etale-tensor-hom-comparison).

The tensor maps below are normalized by the adjunction unit on all Zariski opens.
The Hom comparison is a linear equivalence on every object, with its restriction
law on every arrow: precisely an isomorphism of module sheaves. The final conjunct
states the tensor and Hom squares along every étale scheme morphism using the
canonical pullback comparisons of the equivalence.

## Main definitions and statements

- `smallEtaleModuleHasSheafCompose`: proof-only sheaf-compose interface on the full site.
- `schemeEtaleTensorPullbackIso`: canonical tensor pullback comparison on schemes.
- `schemeEtaleHomPullbackMap`: transpose of pulled-back evaluation on schemes.
- `scheme_etale_tensor_hom_comparison`: the tensor/Hom isomorphisms and restriction squares.

The sectionwise presentation avoids forcing
the generic internal Hom (in universe u+1) into universe u of module sections.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Forgetting commutativity preserves the sheaf condition on the full small étale
site without identifying its object universe u+1 with its morphism universe u.
Source: Stacks Project, Descent, Tags 03DU, 03FH
(blueprint: lem-sfb-scheme-etale-tensor-hom-comparison).
Proof: a compatible family of ring sections glues uniquely in the underlying
commutative-ring sheaf. The same glued section and the same uniqueness witnesses
work after forgetting commutativity: addition, multiplication, zero and one are
unchanged. Equivalently, compute sheaf gluing on the affine étale dense basis,
which is essentially u-small, where the forgetful functor preserves the required
u-small limits, and transport the resulting sheaf condition to the full site.
This is proof data for the existing ringed-site construction, not a new ring. -/
@[instance]
theorem smallEtaleModuleHasSheafCompose (T : Scheme.{u}) :
    T.smallEtaleTopology.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := by
  sorry

/-- The canonical tensor comparison for the tensor-formula scheme pullback,
transported from the monoidal ordinary pullback by its unit-preserving comparison.
Source: Stacks Project, Modules, tensor products and pullback (lemma-tensor-product-pullback)
(blueprint: lem-sfb-scheme-etale-tensor-hom-comparison). -/
noncomputable def schemeEtaleTensorPullbackIso {U T : Scheme.{u}} (a : U ⟶ T)
    (M N : T.Modules) :
    (tensorPullback a).obj M ⊗ (tensorPullback a).obj N ≅
      (tensorPullback a).obj (M ⊗ N) :=
  tensorIso ((tensorOrdinaryPullbackIso a).app M) ((tensorOrdinaryPullbackIso a).app N) ≪≫
    Functor.Monoidal.μIso (pullback a) M N ≪≫
      ((tensorOrdinaryPullbackIso a).app (M ⊗ N)).symm

/-- The canonical scheme Hom base-change map is the transpose of pulled-back evaluation.
It is an isomorphism for an étale map and finitely presented first argument (0C6I).
Source: Stacks Project, Modules, Tag 0C6I
(blueprint: lem-sfb-scheme-etale-tensor-hom-comparison). -/
noncomputable def schemeEtaleHomPullbackMap {U T : Scheme.{u}} (a : U ⟶ T)
    (M N : T.Modules) :
    (tensorPullback a).obj (SheafOfModules.homObj (R := T.sheaf) M N) ⟶
      SheafOfModules.homObj (R := U.sheaf)
        ((tensorPullback a).obj M) ((tensorPullback a).obj N) :=
  MonoidalClosed.curry ((schemeEtaleTensorPullbackIso a M
    (SheafOfModules.homObj (R := T.sheaf) M N)).hom ≫
      (tensorPullback a).map ((ihom.ev M).app N))

set_option maxHeartbeats 1600000 in
-- Elaborating the full comparison unfolds several tensor-localization functors.
/-- Tensor and finite-presentation Hom commute with the canonical small étale
association. The contexts contain only proofs enabling the canonical tensor extension;
they contain no chosen functor or comparison map. Tensor maps are specified on the
unit images of sections on every open. These images generate tensor extension locally.
Hom is specified by evaluation on every étale object, not just on open subschemes.
The final conjunct gives both scheme-object restriction squares for every étale
a : U -> T using zariskiEtalePullbackComparison. The scheme Hom identification
is the transpose of pulled-back evaluation. The étale pullback tensor comparison
and the pullback of h are pinned by their unit-section formulas, and the latter
has the full restriction law on U_et.
Source: Stacks Project, Descent, Tag 06VE(7),(8)
(blueprint: lem-sfb-scheme-etale-tensor-hom-comparison).

Proof:
1. Identify canonical extension with the associated sheaf by
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence. Tensor closure is
   lem-weil-pbc-quasi-coherent-tensor-product-affine-sections. Apply
   lem-weil-pbc-ringed-topoi-module-pullback-tensor. On pure tensors the balanced
   map is (s tensor m) tensor (t tensor n) -> st tensor (m tensor n), with inverse
   s tensor (m tensor n) -> (s tensor m) tensor (1 tensor n). This gives the unit formula.
2. Hom is quasi-coherent by lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent.
   Apply extension to evaluation M tensor Hom(M,N) -> N and the tensor comparison.
   Its value at h on W -> V defines the local transformation m -> ev(h|W,m).
   Bilinearity gives linearity and the pairing's restriction law gives naturality.
3. On an open with a finite free presentation O^a -> O^b -> M -> 0,
   lem-weil-pbc-sheaf-hom-finite-presentation-kernel identifies Hom(M,N) with
   ker(N^b -> N^a), by evaluation on the presented generators. The module
   adjunction preserves coproducts. The quasi-coherent image and cokernel theorems,
   together with lem-sfb-scheme-etale-module-exact-finiteness-comparison, identify
   the extended kernel with the kernel of the same pulled-back matrix.
4. On every slice, a map from the cokernel presentation is a tuple of sections
   annihilating the relations. Restriction preserves the presentation by
   lem-weil-pbc-finite-type-restriction-exact. Sectionwise kernels therefore give
   exactly the same matrix kernel for the étale Hom, using
   lem-weil-pbc-abelian-exact-epi-cokernel and
   lem-weil-pbc-module-sheaves-limits-sectionwise.
5. The evaluation comparison is the identity under these kernel identifications.
   Étale composition and cancellation identify T_et/V with V_et. Zariski charts
   cover every étale object after inverse image; the local inverses glue uniquely.
6. Tensor naturality is checked on locally generating pure tensors. Hom naturality
   is g(h(f(m))). Restriction compatibility is (h(m))|W = h|W(m|W), on every
   further slice object; use lem-sfb-localized-site-tensor-restriction for tensors.
7. For an étale scheme object u:U -> T, finite presentation and quasi-coherence
   pull back. Since u is flat, exact pullback takes the finite-presentation Hom
   kernel to the pulled-back matrix kernel (Modules Tag 0C6I). The comparison
   evaluates on the same pulled-back generators. Choose hp and the direct-image
   comparison r with its preimage-open normalization from the cited equivalence;
   p is their specified left-adjoint mate. The balanced small-etale tensor map k
   sends tensors of pullback-unit sections to the unit of their tensor. The tensor
   square follows on these local generators from the identical multiplication
   formula. The scheme map b is the transpose of pulled-back evaluation, hence
   is invertible by the flat finite-presentation kernel argument. The section
   equivalences j are pullback of h_T followed by the étale Hom base-change map:
   their evaluation formula on all U_et objects is the pullback of h_T's pairing,
   and on unit sections it is literally the unit of h_T(s)(m). This pins j without
   choosing an arbitrary map or identifying section universes. Their restriction
   law follows from evaluation. Transporting j by p_M and p_N equals h_U after
   A_U(b) and p_H inverse, because both sides evaluate to the same pairing on
   every further étale object. These are the two explicit scheme restriction squares.
   No Noetherian or separation assumption enters any step; zero ranks and the empty
   scheme are included. -/
theorem scheme_etale_tensor_hom_comparison
    (c : ∀ T : Scheme.{u}, ZariskiEtaleModuleContext T) :
    ∃ t : ∀ (T : Scheme.{u}) (M N : T.Modules)
        [M.IsQuasicoherent] [N.IsQuasicoherent],
        (SheafOfModules.siteSheafTensorRight
          (A := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
          ((c T).extension.obj N)).obj ((c T).extension.obj M) ≅
            (c T).extension.obj (M ⊗ N),
      (∀ (T : Scheme.{u}) (M N : T.Modules)
          [M.IsQuasicoherent] [N.IsQuasicoherent]
          (W : T.Opens) (m : Γ(M, W)) (n : Γ(N, W)),
        (t T M N).hom.val.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W))
          (SheafOfModules.siteSheafTensorTmul
            (A := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
            ((c T).extension.obj M) ((c T).extension.obj N)
            (op ((AlgebraicGeometry.gabberOpenEtale T).obj W))
            (((c T).adjunction.unit.app M).app W m)
            (((c T).adjunction.unit.app N).app W n)) =
          ((c T).adjunction.unit.app (M ⊗ N)).app W (tmulSection m n)) ∧
      (∀ (T : Scheme.{u}) (M M' N N' : T.Modules)
          [M.IsQuasicoherent] [M'.IsQuasicoherent]
          [N.IsQuasicoherent] [N'.IsQuasicoherent] (f : M ⟶ M') (g : N ⟶ N'),
        (SheafOfModules.siteSheafTensorRight
          (A := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
          ((c T).extension.obj N)).map ((c T).extension.map f) ≫
            SheafOfModules.siteSheafTensorSecondMap
              (A := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
              ((c T).extension.obj M') ((c T).extension.map g) ≫ (t T M' N').hom =
          (t T M N).hom ≫ (c T).extension.map (f ⊗ₘ g)) ∧
      ∃ q : ∀ (T : Scheme.{u}) (M N : T.Modules)
          [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFinitePresentation],
          (SheafOfModules.homObj (R := T.sheaf) M N).IsQuasicoherent,
        ∃ h : ∀ (T : Scheme.{u}) (M N : T.Modules)
            [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFinitePresentation] (V : T.Etale),
            ((c T).extension.obj (SheafOfModules.homObj (R := T.sheaf) M N)).val.obj (op V)
              ≃ₗ[T.etaleStructurePresheaf.obj (op V)]
                (SheafOfModules.homObj
                  (R := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
                  ((c T).extension.obj M) ((c T).extension.obj N)).val.obj (op V),
          (∀ (T : Scheme.{u}) (M N : T.Modules)
              [iM : M.IsQuasicoherent] [iN : N.IsQuasicoherent]
              [iP : M.IsFinitePresentation] (V : T.Etale)
              (s : ((c T).extension.obj
                (SheafOfModules.homObj (R := T.sheaf) M N)).val.obj (op V))
              (m : ((c T).extension.obj M).val.obj (op V)),
            (h T M N V s).app (op (Over.mk (𝟙 V))) m =
              ((c T).extension.map ((ihom.ev M).app N)).val.app (op V)
                ((@t T M (SheafOfModules.homObj (R := T.sheaf) M N)
                    iM (@q T M N iM iN iP)).hom.val.app (op V)
                  (SheafOfModules.siteSheafTensorTmul
                    (A := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
                    ((c T).extension.obj M)
                    ((c T).extension.obj (SheafOfModules.homObj (R := T.sheaf) M N))
                    (op V) m s))) ∧
          (∀ (T : Scheme.{u}) (M M' N N' : T.Modules)
              [M.IsQuasicoherent] [M'.IsQuasicoherent]
              [N.IsQuasicoherent] [N'.IsQuasicoherent]
              [M.IsFinitePresentation] [M'.IsFinitePresentation]
              (f : M' ⟶ M) (g : N ⟶ N') (V : T.Etale)
              (s : ((c T).extension.obj
                (SheafOfModules.homObj (R := T.sheaf) M N)).val.obj (op V)),
            h T M' N' V
              (((c T).extension.map (SheafOfModules.homObjMap (R := T.sheaf) f g)).val.app
                (op V) s) =
              (SheafOfModules.homObjMap
                (R := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
                ((c T).extension.map f) ((c T).extension.map g)).val.app (op V)
                  (h T M N V s)) ∧
          (∀ (T : Scheme.{u}) (M N : T.Modules)
              [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFinitePresentation]
              (V W : T.Etale) (g : W ⟶ V)
              (s : ((c T).extension.obj
                (SheafOfModules.homObj (R := T.sheaf) M N)).val.obj (op V)),
            h T M N W
              (((c T).extension.obj (SheafOfModules.homObj (R := T.sheaf) M N)).val.map
                g.op s) =
              PresheafOfModules.restrictOverMap g (h T M N V s)) ∧
          (∀ (U T : Scheme.{u}) (a : U ⟶ T) [Etale a],
            ∃ (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
              (r : smallEtaleModulePushforward a ⋙ (c T).restriction ≅
                (c U).restriction ⋙ pushforward a),
              (∀ (G : SmallEtaleModules U) (W : T.Opens),
                (r.hom.app G).app W =
                  G.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso a W).hom.op) ∧
              let P := smallEtaleModulePullback a hp
              let p := zariskiEtalePullbackComparison a (c U) (c T) hp r
              ∃ k : ∀ A B : SmallEtaleModules T,
                  (SheafOfModules.siteSheafTensorRight
                    (A := ⟨U.etaleStructurePresheaf, U.isSheaf_etaleStructurePresheaf⟩)
                    (P.obj B)).obj (P.obj A) ≅
                    P.obj ((SheafOfModules.siteSheafTensorRight
                      (A := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
                      B).obj A),
                (∀ (A B : SmallEtaleModules T) (V : T.Etale)
                    (m : A.val.obj (op V)) (n : B.val.obj (op V)),
                  (k A B).hom.val.app (op (a.Etale.obj V))
                    (SheafOfModules.siteSheafTensorTmul
                      (A := ⟨U.etaleStructurePresheaf, U.isSheaf_etaleStructurePresheaf⟩)
                      (P.obj A) (P.obj B) (op (a.Etale.obj V))
                      (((smallEtaleModuleAdjunction a hp).unit.app A).val.app (op V) m)
                      (((smallEtaleModuleAdjunction a hp).unit.app B).val.app (op V) n)) =
                    ((smallEtaleModuleAdjunction a hp).unit.app
                      ((SheafOfModules.siteSheafTensorRight
                        (A := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
                        B).obj A)).val.app (op V)
                          (SheafOfModules.siteSheafTensorTmul
                            (A := ⟨T.etaleStructurePresheaf, T.isSheaf_etaleStructurePresheaf⟩)
                            A B (op V) m n)) ∧
                (∀ (M N : T.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent],
                  (SheafOfModules.siteSheafTensorRight
                    (A := ⟨U.etaleStructurePresheaf, U.isSheaf_etaleStructurePresheaf⟩)
                    ((c U).extension.obj ((tensorPullback a).obj N))).map
                      (p.hom.app M) ≫
                    SheafOfModules.siteSheafTensorSecondMap
                      (A := ⟨U.etaleStructurePresheaf, U.isSheaf_etaleStructurePresheaf⟩)
                      (P.obj ((c T).extension.obj M)) (p.hom.app N) ≫
                    (k ((c T).extension.obj M) ((c T).extension.obj N)).hom ≫
                    P.map (t T M N).hom =
                  (t U ((tensorPullback a).obj M) ((tensorPullback a).obj N)).hom ≫
                    (c U).extension.map (schemeEtaleTensorPullbackIso a M N).hom ≫
                    p.hom.app (M ⊗ N)) ∧
                ∀ (M N : T.Modules) [iM : M.IsQuasicoherent] [iN : N.IsQuasicoherent]
                    [iF : M.IsFinitePresentation],
                  letI : ((tensorPullback a).obj M).IsFinitePresentation :=
                    isFinitePresentation_tensorPullback a M
                  letI : (SheafOfModules.homObj (R := T.sheaf) M N).IsQuasicoherent :=
                    @q T M N iM iN iF
                  ∃ b : (tensorPullback a).obj (SheafOfModules.homObj (R := T.sheaf) M N) ≅
                      SheafOfModules.homObj (R := U.sheaf)
                        ((tensorPullback a).obj M) ((tensorPullback a).obj N),
                    b.hom = schemeEtaleHomPullbackMap a M N ∧
                    ∃ j : ∀ W : U.Etale,
                        (P.obj ((c T).extension.obj
                          (SheafOfModules.homObj (R := T.sheaf) M N))).val.obj (op W)
                          ≃ₗ[U.etaleStructurePresheaf.obj (op W)]
                            (SheafOfModules.homObj
                              (R := ⟨U.etaleStructurePresheaf, U.isSheaf_etaleStructurePresheaf⟩)
                              (P.obj ((c T).extension.obj M))
                              (P.obj ((c T).extension.obj N))).val.obj (op W),
                      (∀ (V W : U.Etale) (g : W ⟶ V)
                          (s : (P.obj ((c T).extension.obj
                            (SheafOfModules.homObj (R := T.sheaf) M N))).val.obj (op V)),
                        j W ((P.obj ((c T).extension.obj
                          (SheafOfModules.homObj (R := T.sheaf) M N))).val.map g.op s) =
                            PresheafOfModules.restrictOverMap g (j V s)) ∧
                      (∀ (W : U.Etale)
                          (s : (P.obj ((c T).extension.obj
                            (SheafOfModules.homObj (R := T.sheaf) M N))).val.obj (op W))
                          (m : (P.obj ((c T).extension.obj M)).val.obj (op W)),
                        (j W s).app (op (Over.mk (𝟙 W))) m =
                          (P.map ((t T M (SheafOfModules.homObj (R := T.sheaf) M N)).hom ≫
                            (c T).extension.map ((ihom.ev M).app N))).val.app (op W)
                              ((k ((c T).extension.obj M) ((c T).extension.obj
                                (SheafOfModules.homObj (R := T.sheaf) M N))).hom.val.app (op W)
                                  (SheafOfModules.siteSheafTensorTmul
                                    (A := ⟨U.etaleStructurePresheaf,
                                      U.isSheaf_etaleStructurePresheaf⟩)
                                    (P.obj ((c T).extension.obj M))
                                    (P.obj ((c T).extension.obj
                                      (SheafOfModules.homObj (R := T.sheaf) M N)))
                                    (op W) m s))) ∧
                      (∀ (V : T.Etale)
                          (s : ((c T).extension.obj
                            (SheafOfModules.homObj (R := T.sheaf) M N)).val.obj (op V))
                          (m : ((c T).extension.obj M).val.obj (op V)),
                        (j (a.Etale.obj V)
                          (((smallEtaleModuleAdjunction a hp).unit.app
                            ((c T).extension.obj (SheafOfModules.homObj
                              (R := T.sheaf) M N))).val.app (op V) s)).app
                                (op (Over.mk (𝟙 (a.Etale.obj V))))
                                  (((smallEtaleModuleAdjunction a hp).unit.app
                                    ((c T).extension.obj M)).val.app (op V) m) =
                          ((smallEtaleModuleAdjunction a hp).unit.app
                            ((c T).extension.obj N)).val.app (op V)
                              ((h T M N V s).app (op (Over.mk (𝟙 V))) m)) ∧
                      ∀ (W : U.Etale)
                          (s : (P.obj ((c T).extension.obj
                            (SheafOfModules.homObj (R := T.sheaf) M N))).val.obj (op W)),
                        h U ((tensorPullback a).obj M) ((tensorPullback a).obj N) W
                          (((c U).extension.map b.hom).val.app (op W)
                            ((p.inv.app (SheafOfModules.homObj (R := T.sheaf) M N)).val.app
                              (op W) s)) =
                          (SheafOfModules.homObjMap
                            (R := ⟨U.etaleStructurePresheaf, U.isSheaf_etaleStructurePresheaf⟩)
                            (p.hom.app M) (p.inv.app N)).val.app (op W) (j W s)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
