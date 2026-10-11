/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
public import Sheaf.CategoryTheory.Galois.AutProfinite
public import Mathlib.GroupTheory.Index

/-!
# The fundamental-group equivalence and base change

Source: Stacks Project, Theorem 0BND and Remark 0DV6; SGA 1, Exposé V,
Proposition 6.13 and §7 (blueprint: thm-galois-fundamental).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The fibre equivalence, on finite étale covers and finite locally constant sheaves,
including the identification of the fundamental group and finite-limit/colimit compatibility.
Source: Stacks Project, Theorem 0BND (1), Remark 0DV6; SGA 1 V §7
(blueprint: thm-galois-fundamental).

Proof: `lem-fet-galois-category` and `thm-galois-abstract-equivalence` give the existing
`equivalenceContAction`. `lem-galois-aut-profinite` gives the evaluation topology.
The Yoneda equivalence `thm-galois-lc-etale` identifies both fibre functors; conjugation
along it identifies their automorphism groups, homeomorphically because evaluation
coordinates correspond and every sheaf is represented. Transporting the first equivalence
along its inverse gives the FLC equivalence. Its action is the evaluation action under
this group identification. Finally `lem-galois-equivalence-preserves-limits` says that
both equivalences preserve finite limits and colimits. -/
theorem exists_fiber_flc_equivalence {Y : Scheme.{w}} [ConnectedSpace Y]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (G : Type w) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G] :
    ∃ (Φ : Y.FiniteEtale ≌ Y.FLC) (E : Y.FLC ≌ ContAction FintypeCat.{w} G)
      (γ : G ≃ₜ* Aut (ObjectProperty.ι (IsFiniteLocallyConstantEtaleSheafOfSets (T := Y)) ⋙
        (pointSmallEtale s).sheafFiber (A := Type (w + 1)))),
      Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{w + 1}) ∧
      Nonempty (Φ.functor ⋙ E.functor ≅ (equivalenceContAction s G).functor) ∧
      (∃ τ : E.functor ⋙ forget₂ (ContAction FintypeCat.{w} G) FintypeCat.{w} ⋙
          CategoryTheory.forget FintypeCat.{w} ⋙ uliftFunctor.{w + 1, w} ≅
          ObjectProperty.ι _ ⋙ (pointSmallEtale s).sheafFiber (A := Type (w + 1)),
        ∀ (F : Y.FLC) (g : G) (z : ULift.{w + 1} (E.functor.obj F).obj.V),
          τ.hom.app F ⟨((E.functor.obj F).obj.ρ g).hom z.down⟩ =
            (γ g).hom.app F (τ.hom.app F z)) ∧
      PreservesFiniteLimits (equivalenceContAction s G).functor ∧
      PreservesFiniteColimits (equivalenceContAction s G).functor ∧
      PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor := by
  sorry

/-- Base change corresponds to restriction of the action along the continuous map on π₁.
Source: Stacks Project, Theorem 0BND (3)
(blueprint: thm-galois-fundamental).

Proof: `lem-galois-pi1-functoriality` gives `fundamentalGroupMap`, its continuity,
and `pullbackFiberIso`. Its characterization is precisely equivariance of the
components of that natural isomorphism. The component bijections therefore lift
to an isomorphism of functors to continuous finite actions. -/
theorem fiber_equivalence_baseChange
    {X Y : Scheme.{w}} [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y)
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (GX GY : Type w) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX]
    [CompactSpace GX] [∀ Q, MulAction GX ((fiber s).obj Q)]
    [IsFundamentalGroup (fiber s) GX]
    [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY] :
    ∃ h : GX →ₜ* GY,
      h.toMonoidHom = fundamentalGroupMap (pullbackFiberIso f s) GX GY ∧
      ∃ η : pullback f ⋙ (equivalenceContAction s GX).functor ≅
          (equivalenceContAction (s ≫ f) GY).functor ⋙ ContAction.res FintypeCat.{w} h,
        ∀ (P : Y.FiniteEtale) (z : (fiber s).obj ((pullback f).obj P)),
          (η.hom.app P).hom.hom z = (pullbackFiberIso f s).hom.app P z := by
  sorry

/-- For finite étale base change the map is injective with open finite-index stabilizer image.
Source: SGA 1, Exposé V, Proposition 6.13 and §7, p. 116
(blueprint: thm-galois-fundamental).

Proof: `lem-galois-pi1-finite-etale-injective` gives injectivity.
`lem-galois-pi1-finite-etale-image-stabilizer` gives the image, openness and index,
the latter equal to the size of the finite geometric fibre (`def-galois-categories`).
The preceding base-change clause then says that pullback is restriction to this
open subgroup. Profinite compactness and Hausdorffness identify the source group
homeomorphically with its image (`lem-galois-aut-profinite`). -/
theorem fiber_equivalence_finiteEtale_baseChange
    {X Y : Scheme.{w}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (GX GY : Type w) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX]
    [CompactSpace GX] [∀ Q, MulAction GX ((fiber s).obj Q)]
    [IsFundamentalGroup (fiber s) GX]
    [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY] :
    Function.Injective (fundamentalGroupMap (pullbackFiberIso f s) GX GY) ∧
      (fundamentalGroupMap (pullbackFiberIso f s) GX GY).range =
        MulAction.stabilizer GY
          (fiberMk (s ≫ f) ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩ s rfl) ∧
      IsOpen ((MulAction.stabilizer GY
        (fiberMk (s ≫ f) ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩ s rfl)) : Set GY) ∧
      (MulAction.stabilizer GY
        (fiberMk (s ≫ f) ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩ s rfl)).FiniteIndex := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
