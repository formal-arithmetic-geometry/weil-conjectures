/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.FpqcTensorSections
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Big fppf to Zariski ringed comparison

Source: Stacks Project, Descent, Tags 070R and 070S(1)
(blueprint: lem-sfb-big-fppf-zariski-ringed-comparison).

The ring sheaf, the section presheaf functor and the comparison are existentially
specified together with their actual section formulas. This avoids choosing any
uncharacterized data. Module pullback is Mathlib's canonical left adjoint along the
continuous open inclusion and its structural ring map, i.e. the ringed tensor pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme

/-- The tensor inverse image to the big fppf site is the sheafification of pullback
sections, naturally in every Zariski module, including modules that are not quasi-coherent.
Source: Stacks Project, Descent, Tags 070R and 070S(1)
(blueprint: lem-sfb-big-fppf-zariski-ringed-comparison).

Proof (the node's ten steps):
1. The rank-one tilde theorem makes O_S quasi-coherent on affine opens. Pullback of
O_S is O_T, compatibly with its unit; fppf covers are fpqc, and fpqc descent of sections
therefore makes the regular-function presheaf a sheaf of rings. This uses quasi-coherence
only for O_S, never for the arbitrary module M.
2. The inclusion of opens preserves the terminal object and intersections, hence finite
limits (open-preimage fibre products). Zariski covers are fppf covers. The left-exact site
inverse-image theorem gives the geometric adjunction with restriction as direct image.
The continuous ringed-topos construction applied to the identity on structure sheaves
supplies the ringed morphism and its module restriction, including the scalar action.
3. Scheme tensor-pullback adjunctions give unit-normalized composition isomorphisms.
Composite adjunctions and conjugate-unit uniqueness prove their associativity; open
pullback is ordinary restriction with the same unit.
4. Define P_M(u) = Gamma(T,u^*M). Its arrow map is pullback of sections followed by the
normalized composition comparison. Units give identity and composition, semilinearity,
and naturality in M; on opens this identifies P_M with M.
5. For a big-site module G, restrict G to opens of each T. A map beta:M -> RG gives
b_u:M -> u_*G_u by restriction to u^{-1}W. Its scheme-adjoint a_u:u^*M -> G_u defines
the map P_M(u) -> G(u) on global sections.
6. For every big-site arrow h, the transposes of a_uh c_hu and d_h h^*a_u agree:
both send m to its restriction along (uh)^{-1}W -> W. Injectivity of the composite
adjunction gives equality and hence naturality on all big-site arrows, with scalars.
7. Conversely a map P_M -> G restricts to beta on opens. Its maps on all opens of T
form a_u. The unit equation identifies its transpose with b_u, so the constructions
are inverse, including the open and identity cases.
8. Naturality of scheme adjunctions makes these Hom bijections natural in both M and G.
Compose them with the module-sheafification adjunction: P followed by sheafification
is left adjoint to the actual module restriction functor.
9. Ringed tensor pullback is also left adjoint to that restriction (the ringed-topoi
module-adjunction theorem). Uniqueness of left adjoints gives the natural comparison
carrying units to units. Its components are module-sheaf maps and thus preserve every
restriction and scalar action. Naturality identifies its map with sheafification of P_v.
10. The unit of the sheafified-section adjunction is q_M on opens, after the canonical
open-pullback identification. The unit equation for the unique left-adjoint comparison
gives exactly the final displayed formula, compatibly with open restrictions and v.
-/
theorem bigFppfZariskiRingedComparison (S : Scheme.{u}) :
    ∃ (_ : (fppfTopology.over S).HasSheafCompose (CategoryTheory.forget RingCat.{u}))
      (_ : (fppfTopology.over S).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u}))
      (_ : HasWeakSheafify (fppfTopology.over S) AddCommGrpCat.{u})
      (_ : (fppfTopology.over S).WEqualsLocallyBijective AddCommGrpCat.{u})
      (_ : S.restrictFunctor.IsContinuous (Opens.grothendieckTopology S)
        (fppfTopology.over S)),
    ∃ (O : Sheaf (fppfTopology.over S) RingCat.{u})
      (o : O.obj ≅ (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)
      (φ : S.ringCatSheaf ⟶
        (S.restrictFunctor.sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology S) (fppfTopology.over S)).obj O),
    (∀ (W : S.Opens) (a : Γ(S, W)),
      o.hom.app (op (S.restrictFunctor.obj W)) (φ.hom.app (op W) a) = W.topIso.inv a) ∧
    ∃ (p : RingedToposMorphismOnSites O S.ringCatSheaf)
      (d : p.direct ≅ S.restrictFunctor.sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology S) (fppfTopology.over S)),
    p.modules = SheafOfModules.pushforward φ ∧
    (p.adj.homEquiv _ _ p.ringMap) ≫
        d.hom.app ((sheafCompose (fppfTopology.over S) (CategoryTheory.forget RingCat.{u})).obj O) =
      (sheafCompose (Opens.grothendieckTopology S) (CategoryTheory.forget RingCat.{u})).map φ ∧
    ∃ (_ : (SheafOfModules.pushforward.{u} φ).IsRightAdjoint)
      (P : S.Modules ⥤ _root_.PresheafOfModules.{u} O.obj)
      (s : ∀ (M : S.Modules) (U : Over S),
        (P.obj M).obj (op U) ≃+ Γ((Modules.tensorPullback U.hom).obj M, ⊤)),
    (∀ (M : S.Modules) (U : Over S) (a : O.obj.obj (op U))
      (x : (P.obj M).obj (op U)),
      s M U (a • x) = @id Γ(U.left, ⊤) (o.hom.app (op U) a) • s M U x) ∧
    (∀ (M : S.Modules) (U U' : Over S) (h : U' ⟶ U)
      (x : (P.obj M).obj (op U)),
      s M U' ((P.obj M).map h.op x) =
        (eqToHom (congrArg (fun f ↦ (Modules.tensorPullback f).obj M) h.w)).app ⊤
          (((Modules.tensorPullbackSectionComp h.left U.hom).inv.app M).app ⊤
            (((Modules.tensorPullback h.left).obj
              ((Modules.tensorPullback U.hom).obj M)).presheaf.map
                (homOfLE h.left.preimage_top.ge).op
                  (((Modules.tensorPullbackSectionAdjunction h.left).unit.app
                    ((Modules.tensorPullback U.hom).obj M)).app ⊤ (s M U x))))) ∧
    (∀ (M N : S.Modules) (v : M ⟶ N) (U : Over S) (x : (P.obj M).obj (op U)),
      s N U ((P.map v).app (op U) x) =
        ((Modules.tensorPullback U.hom).map v).app ⊤ (s M U x)) ∧
    ∃ e : SheafOfModules.pullback.{u} φ ≅
      P ⋙ PresheafOfModules.sheafification (𝟙 O.obj),
    ∀ (M : S.Modules) (W : S.Opens) (x : Γ(M, W)),
      (e.hom.app M).val.app (op (S.restrictFunctor.obj W))
        (((SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).val.app (op W) x) =
      (CategoryTheory.toSheafify (fppfTopology.over S) (P.obj M).presheaf).app
        (op (S.restrictFunctor.obj W))
        ((s M (S.restrictFunctor.obj W)).symm
          (((Modules.tensorPullback W.ι).obj M).presheaf.map
            (homOfLE W.ι_preimage_self.ge).op
              (((Modules.tensorPullbackSectionAdjunction W.ι).unit.app M).app W x))) := by
  sorry

end AlgebraicGeometry.Scheme
