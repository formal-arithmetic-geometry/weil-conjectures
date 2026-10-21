/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Smallness of module sheaves with prescribed local models

Source: Stacks Project, Sites, Tag 04TQ and Modules on Sites, Tag 03EM; the
Essentially small paragraph of the current blueprint's Brown hypotheses proof
(blueprint: lem-sfb-locally-prescribed-modules-small).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

private theorem essentiallySmall_embeds
    {A : Type*} [Category* A] {D : Type*} [Category* D]
    [LocallySmall.{u} D] [WellPowered.{u} D]
    (F : A ⥤ D) (hF : F.FullyFaithful) (Q : D) :
    ObjectProperty.EssentiallySmall.{u}
      (fun X ↦ ∃ f : F.obj X ⟶ Q, Mono f) := by
  classical
  let S := {s : Subobject Q // ∃ X : A, Nonempty (F.obj X ≅ (s : D))}
  let repr : S → A := fun s ↦ s.property.choose
  have hre (s : S) : Nonempty (F.obj (repr s) ≅ (s.val : D)) :=
    s.property.choose_spec
  refine ⟨ObjectProperty.ofObj repr, inferInstance, ?_⟩
  intro X ⟨f, hf⟩
  let s : S := ⟨Subobject.mk f, X, ⟨(Subobject.underlyingIso f).symm⟩⟩
  exact ⟨repr s, ⟨s⟩,
    ⟨hF.preimageIso ((Subobject.underlyingIso f).symm ≪≫ (hre s).some.symm)⟩⟩

private theorem hom_ext_over_cover
    {C : Type u} [Category.{u} C] [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck RingCat.{u})
    {F G : SheafOfModules.{u} R} (a b : F ⟶ G)
    {ι : Type u} (U : ι → C) (f : ∀ j, U j ⟶ ⊤_ C)
    (hf : Presieve.ofArrows U f ∈ J (⊤_ C))
    (h : ∀ j, (overFunctor R (U j)).map a = (overFunctor R (U j)).map b) :
    a = b := by
  apply (forget R ⋙ PresheafOfModules.toPresheaf R.obj).map_injective
  apply NatTrans.ext
  funext W
  obtain ⟨W⟩ := W
  obtain ⟨P, p, q, hpq, hp⟩ := hJ.2.2 ι (⊤_ C) U f hf W (terminal.from W)
  apply G.isSheaf.hom_ext_ofArrows p (J.generate_mem_toGrothendieck hp)
  intro j
  have hj := congrArg (fun k ↦ k.val.app (Opposite.op (Over.mk (q j)))) (h j)
  have hj' := congrArg (fun k ↦ (CategoryTheory.forget₂ _ AddCommGrpCat).map k) hj
  change ((PresheafOfModules.toPresheaf R.obj).map a.val).app (Opposite.op W) ≫
      G.val.presheaf.map (p j).op =
    ((PresheafOfModules.toPresheaf R.obj).map b.val).app (Opposite.op W) ≫
      G.val.presheaf.map (p j).op
  exact (((PresheafOfModules.toPresheaf R.obj).map a.val).naturality (p j).op).symm.trans
    ((congrArg (fun k ↦ F.val.presheaf.map (p j).op ≫ k) hj').trans
      (((PresheafOfModules.toPresheaf R.obj).map b.val).naturality (p j).op))

/-- Module sheaves locally among prescribed small families are essentially small.

Source: Stacks Project, Sites, Tag 04TQ, Modules on Sites, Tag 03EM, and the
Essentially small paragraph of `sk-lem-brown-hypotheses-small.proof.md`
(blueprint: lem-sfb-locally-prescribed-modules-small).

The universe `u` is the fixed universe of the small site, section sets and local
model labels. The cover uses the original precoverage, not just its generated
covering sieves. `ObjectProperty.EssentiallySmall.exists_small_le` expresses the
conclusion as a small family of members representing all the isomorphism classes.

Proof: (1) Presheaves of modules on the small category are well-powered. For a
fixed presheaf Q, the sheaves whose underlying presheaves embed into Q form an
essentially small class: assign each embedding its subobject of Q, restrict the
small subobject set to those whose underlying objects are isomorphic to a sheaf,
and choose one such sheaf for each. Full faithfulness of the forgetful functor
lifts the resulting presheaf isomorphisms to sheaf isomorphisms.
(2) A code consists of an object support S and one local-model label t(U) for
each U in S. These codes form a small type. To each code assign the product of
the direct images of B(U,t(U)) along the slice projections. The right adjoints
exist by the finite-limit hypothesis and Mathlib's restriction-pushforward
adjunction. These are actual products of already given module sheaves.
(3) For a locally prescribed M, take the support of its original witnessing
cover, choose one label and trivialization for each distinct object, and transpose
the trivializations through those adjunctions. Their product is a map from M to
the product assigned to its code.
(4) This map is monic. Equality after composition with it implies equality after
all product projections. Adjunction naturality and cancellation of the local
trivializations give equality after restriction to every original cover member.
Pull that original cover back to each object and apply sheaf separation to obtain
global equality. Repeated cover objects are retained throughout this argument.
(5) The forgetful functor to presheaves preserves finite limits, hence sends the
monomorphism to a presheaf monomorphism. Step 1 applies to each fixed code's
product, and a small union of these essentially small properties is essentially
small. The locally prescribed property is a subproperty of that union. This uses
only the uniqueness part of descent and does not require effectivity of arbitrary
descent data. -/
theorem essentiallySmall_locally_prescribed
    {C : Type u} [Category.{u} C] [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (hR : Presheaf.IsSheaf J.toGrothendieck (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (I : C → Type u)
    (B : ∀ U : C, I U → ringedSiteModules.{u}
      (Sheaf.over (⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩ :
        Sheaf J.toGrothendieck RingCat.{u}) U)) :
    ObjectProperty.EssentiallySmall.{u}
      (fun M : ringedSiteModules.{u} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩ ↦
        ∃ (ι : Type u) (U : ι → C) (f : ∀ j : ι, U j ⟶ ⊤_ C),
          Presieve.ofArrows U f ∈ J (⊤_ C) ∧
            ∀ j : ι, ∃ t : I (U j),
              Nonempty
                (((overFunctor.{u} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩
                  (U j)).obj M) ≅ B (U j) t)) := by
  classical
  let R' : Sheaf J.toGrothendieck RingCat.{u} :=
    ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩
  let Code := Σ S : Set C, (∀ U : S, I U.val)
  let family (k : Code) (U : k.1) : SheafOfModules.{u} R' :=
    (pushforward (pushforwardOver U.val)).obj (B U.val (k.2 U))
  let Q : Code → SheafOfModules.{u} R' := fun k ↦ ∏ᶜ (family k)
  let P : Code → ObjectProperty (SheafOfModules.{u} R') := fun k M ↦
    ∃ f : M.val ⟶ (Q k).val, Mono f
  have hP (k : Code) : ObjectProperty.EssentiallySmall.{u} (P k) :=
    essentiallySmall_embeds.{u} (forget R') (fullyFaithfulForget R') (Q k).val
  let (k : Code) : ObjectProperty.EssentiallySmall.{u} (P k) := hP k
  apply ObjectProperty.EssentiallySmall.of_le (Q := ⨆ k, P k)
  intro M hM
  obtain ⟨ι, U, f, hf, ht⟩ := hM
  let S : Set C := Set.range U
  have hs (V : S) : ∃ t : I V.val, Nonempty (M.over V.val ≅ B V.val t) := by
    obtain ⟨j, hj⟩ := V.property
    rw [← hj]
    exact ht j
  choose t e using hs
  let k : Code := ⟨S, t⟩
  let localMap (V : S) : M.over V.val ⟶ B V.val (t V) := (e V).some.hom
  let adj (V : S) := overPushforwardOverAdj (R := R') V.val
  let φ : M ⟶ Q k := Pi.lift (f := family k) (fun V : S ↦ (adj V).homEquiv _ _ (localMap V))
  have hφ : Mono φ := by
    constructor
    intro L a b hab
    apply hom_ext_over_cover J hJ R' a b U f hf
    intro j
    let V : S := ⟨U j, ⟨j, rfl⟩⟩
    have hlocal : a ≫ (adj V).homEquiv _ _ (localMap V) =
        b ≫ (adj V).homEquiv _ _ (localMap V) := by
      simpa only [φ, Category.assoc, Pi.lift_π] using congrArg
        (fun z ↦ z ≫ Pi.π (family k) V) hab
    apply (cancel_mono (localMap V)).1
    apply (adj V).homEquiv _ _ |>.injective
    exact ((adj V).homEquiv_naturality_left a (localMap V)).trans
      (hlocal.trans ((adj V).homEquiv_naturality_left b (localMap V)).symm)
  have hval : Mono φ.val := by
    let : Mono φ := hφ
    let : PreservesFiniteLimits (forget.{u} R') :=
      SheafOfModules.Finite.forgetPreservesFiniteLimits R'
    let : PreservesLimitsOfShape WalkingCospan (forget.{u} R') := inferInstance
    exact preserves_mono_of_preservesLimit (forget.{u} R') φ
  exact (show P k M from ⟨φ.val, hval⟩) |> (le_iSup P k M)

end SheafOfModules
