/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.SixFunctors.IntegralBrownAdjoint
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.SixFunctors.IntegralExceptionalAffineChart
import Sheaf.SixFunctors.IntegralRestrictionGlue
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.SixFunctors.IntegralLocalizingCompactSupport
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Restriction of the integral exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
_section.md and sk-thm-int-restriction.proof.md (blueprint: sk-thm-int-restriction).

The Brown adjoint acts on the ordinary localizing closure of the recorded constant-model
bounded constructible objects. The assertion below uses the recorded finite-Tor subcategory
and restricts the actual functors by full-subcategory lifts, on objects and morphisms alike.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Preservation of Dctf by `G` and the adjunction of the actual restricted functors.
`hY` only supplies the full inclusion of Dctf in Loc(Dbc); it is a conclusion, not
an extra assumption. `hL` and `hR` give the membership proofs for the two restrictions.
The left lift is the recorded compactification composite. The right lift is `G`
preceded by the full inclusion and followed by the ambient full inclusion.
Thus neither restricted functor is an arbitrary functor with the same object types.
Source: blueprint sk-thm-int-restriction, both sentences
(blueprint: sk-thm-int-restriction). -/
def ctfRestrictionAssertions (c : Compactification f)
    (G : (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory) : Prop :=
  ∃ hY : (constantModelBoundedConstructible Λ Y ⊓
      DerivedCategory.finiteTorAmplitude _) ≤ localizing Λ Y,
    ∃ hL : ∀ K : ConstantModelConstructibleFiniteTor Λ X,
      (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _)
        ((image Λ c).obj K.obj),
    ∃ hR : ∀ K : ConstantModelConstructibleFiniteTor Λ Y,
      (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _)
        (G.obj ((ObjectProperty.ιOfLE hY).obj K)).obj,
    Nonempty
      (((constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _).lift
          ((constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _).ι ⋙
            image Λ c) hL) ⊣
        ((constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _).lift
          (ObjectProperty.ιOfLE hY ⋙ G ⋙ (localizing Λ X).ι) hR))

private theorem ctfRestrictionAssertions_of_preservation (c : Compactification f)
    (h : ∀ K, localizing Λ X K → localizing Λ Y ((image Λ c).obj K))
    (G : (localizing Λ Y).FullSubcategory ⥤ (localizing Λ X).FullSubcategory)
    (adj : lowerShriek Λ c h ⊣ G)
    (hY : (constantModelBoundedConstructible Λ Y ⊓
      DerivedCategory.finiteTorAmplitude _) ≤ localizing Λ Y)
    (hL : ∀ K : ConstantModelConstructibleFiniteTor Λ X,
      (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _)
        ((image Λ c).obj K.obj))
    (hR : ∀ K : ConstantModelConstructibleFiniteTor Λ Y,
      (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _)
        (G.obj ((ObjectProperty.ιOfLE hY).obj K)).obj) :
    ctfRestrictionAssertions Λ c G := by
  let hX : (constantModelBoundedConstructible Λ X ⊓
      DerivedCategory.finiteTorAmplitude _) ≤ localizing Λ X :=
    fun K hK _P _hP hS ↦ hS K hK.1
  refine ⟨hY, hL, hR, ⟨Adjunction.mkOfHomEquiv ?_⟩⟩
  refine
    { homEquiv := fun A B ↦
        { toFun := fun m ↦ ObjectProperty.homMk
            ((adj.homEquiv ((ObjectProperty.ιOfLE hX).obj A)
              ((ObjectProperty.ιOfLE hY).obj B) (ObjectProperty.homMk m.hom)).hom)
          invFun := fun m ↦ ObjectProperty.homMk
            (((adj.homEquiv ((ObjectProperty.ιOfLE hX).obj A)
              ((ObjectProperty.ιOfLE hY).obj B)).symm (ObjectProperty.homMk m.hom)).hom)
          left_inv := ?_
          right_inv := ?_ }
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · rename_i A B
    intro m
    apply ObjectProperty.hom_ext
    exact congrArg (fun n ↦ n.hom)
      ((adj.homEquiv ((ObjectProperty.ιOfLE hX).obj A)
        ((ObjectProperty.ιOfLE hY).obj B)).symm_apply_apply
          (ObjectProperty.homMk m.hom))
  · rename_i A B
    intro m
    apply ObjectProperty.hom_ext
    exact congrArg (fun n ↦ n.hom)
      ((adj.homEquiv ((ObjectProperty.ιOfLE hX).obj A)
        ((ObjectProperty.ιOfLE hY).obj B)).apply_symm_apply
          (ObjectProperty.homMk m.hom))
  · intro A A' B m n
    apply ObjectProperty.hom_ext
    exact congrArg (fun q ↦ q.hom)
      (adj.homEquiv_naturality_left_symm
        ((ObjectProperty.ιOfLE hX).map m) (ObjectProperty.homMk n.hom))
  · intro A B B' m n
    apply ObjectProperty.hom_ext
    exact congrArg (fun q ↦ q.hom)
      (adj.homEquiv_naturality_right
        (ObjectProperty.homMk m.hom :
          (lowerShriek Λ c h).obj ((ObjectProperty.ιOfLE hX).obj A) ⟶
            (ObjectProperty.ιOfLE hY).obj B)
        ((ObjectProperty.ιOfLE hY).map n))

/-- The integral Brown right adjoint preserves constructible finite-Tor complexes,
and its restriction is right adjoint to the restricted compactly supported image.
The preservation proof `h` and `adj` specify precisely the functor and adjunction
of det-prop-int-brown-adjoint; that node supplies such data. Quantifying over their
choices avoids choosing data from a nonunique existence theorem.

Source: blueprint main-20261015, sk-thm-int-restriction/_section.md and its proof
(blueprint: sk-thm-int-restriction).

Proof plan:
1. In the standing separated finite-type setting, X and Y are qcqs by
   lem-weil-pbc-qcqs-over-affine. Apply det-def-localizing-closure-ctf-equals-bc(2)
   to identify Dctf with Dbc and their localizing closures for O_E. Fix K in Dbc(Y).
2. Cover Y by finitely many affine V and each inverse image by finitely many affine U.
   A finite set of algebra generators gives a surjection from a polynomial ring,
   hence a closed immersion i : U -> A^d_V, by def-weil-finite-type-morphism and
   def-weil-closed-immersion. These U form a finite open cover of X.
3. The chart schemes are qcqs by lem-weil-pbc-affine-scheme-qcqs; the open inclusions
   u and v are quasi-compact by lem-weil-pbc-qcqs-morphism-permanence(1).
   det-sf-mate-open-restriction(1) gives their extension/restriction adjunctions.
   det-prop-int-brown-construction identifies Rf_! u_! with v_! Rp_! Ri_!.
   Apply these adjunctions and det-prop-int-brown-adjoint to obtain the natural
   Hom chain identifying u^* G K with i^! p^! v^* K on the localizing categories.
   Yoneda, using the images of identity maps, supplies the inverse isomorphisms.
4. det-thm-int-restriction-line identifies p^! with p^*(d)[2d] and gives preservation.
   sk-lem-int-tensor supplies constructibility of v^* K. Then
   det-thm-int-restriction-closed gives constructibility of i^! p^! v^* K.
   Thus the restrictions of G K to all members of the finite cover are in Dbc.
5. det-thm-int-restriction-glue(1), finite-cover locality alone, gives G K in Dbc(X).
   det-prop-int-brown-construction supplies preservation by Rf_!. Transfer both
   statements to Dctf using step 1. The full-subcategory lifts in the conclusion
   have exactly the ambient Hom sets, so the given adjunction supplies their
   natural Hom equivalences and hence their adjunction. This uses no claim of
   constructibility of G K before step 5, and no clause (2) of the gluing node.
-/
theorem integralExceptionalRestriction (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, localizing (Profinite.padicIntegersRingObj ℓ E.val) X K →
      localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((image (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj).obj K))
    (G : (localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (localizing (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory)
    (_adj : lowerShriek (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ G) :
    ctfRestrictionAssertions (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj G := by
  classical
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have eX : (constantModelBoundedConstructible Λ X ⊓
      DerivedCategory.finiteTorAmplitude _) = constantModelBoundedConstructible Λ X :=
    (localizingClosure_ctf_equals_bc ℓ X Λ
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.1
  have eY : (constantModelBoundedConstructible Λ Y ⊓
      DerivedCategory.finiteTorAmplitude _) = constantModelBoundedConstructible Λ Y :=
    (localizingClosure_ctf_equals_bc ℓ Y Λ
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.1
  let hY : (constantModelBoundedConstructible Λ Y ⊓
      DerivedCategory.finiteTorAmplitude _) ≤ localizing Λ Y :=
    fun K hK _P _hP hS ↦ hS K hK.1
  apply ctfRestrictionAssertions_of_preservation Λ c.obj.obj h G _adj hY
  · intro K
    rw [eY]
    obtain ⟨pres, _, _, _⟩ := integralLocalizingCompactSupport ℓ E k
    let XS : Spaces k := ⟨Over.mk (X ↘ Spec (.of k)),
      ⟨inferInstanceAs (IsSeparated (X ↘ Spec (.of k))),
        inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k))),
        inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))⟩⟩
    let YS : Spaces k := ⟨Over.mk (Y ↘ Spec (.of k)),
      ⟨inferInstanceAs (IsSeparated (Y ↘ Spec (.of k))),
        inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k))),
        inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))⟩⟩
    let fs : XS ⟶ YS := ObjectProperty.homMk (f.asOver (Spec (.of k)))
    exact pres.maps_constructible (f := fs) c.obj K.obj K.property.1
  · intro K
    rw [eX]
    have charts : ∀ x : X, ∃ (U : X.Opens) (V : Y.Opens),
        IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ f ⁻¹ᵁ V := by
      intro x
      obtain ⟨V, hV, hxV, _⟩ :=
        exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x) (U := ⊤) trivial
      obtain ⟨U, hU, hxU, hUV⟩ :=
        exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hxV
      exact ⟨U, V, hU, hV, hxU, hUV⟩
    choose U V hU hV hxU hUV using charts
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen)
      (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
    have hcover : (⨆ a : s, U a.val) = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩
    apply (IntegralRestriction.integralRestrictionGlue.{u, u} ℓ E k).1
      X s (fun a ↦ U a.val) hcover (G.obj ((ObjectProperty.ιOfLE hY).obj K)).obj
    intro a
    exact integralExceptionalAffineChart ℓ E k f c h G _adj
      (U a.val) (V a.val) (hU a.val) (hV a.val) (hUV a.val)
      ((ObjectProperty.ιOfLE hY).obj K) K.property.1


end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
