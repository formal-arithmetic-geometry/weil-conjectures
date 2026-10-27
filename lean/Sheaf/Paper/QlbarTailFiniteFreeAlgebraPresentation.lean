module

public import Sheaf.Paper.QlbarTailModuleColimit
public import Sheaf.Topology.ProfiniteCondensedRing
import Sheaf.Paper.CartesianCoefficientsFiniteFree
import Sheaf.CategoryTheory.FilteredRingObjectCoconeColimit
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-! # Finite-free coefficient algebras on the cofinal finite-field tail

Source: Bhatt--Scholze, Lemma 6.8.2(2), and blueprint main-20261015,
sk-prop-sfb-qlbar-colimit-x, third comparison, and
sk-prop-sfb-cartesian-coefficients, assertion (2).
(blueprint: lem-sfb-qlbar-tail-finite-free-algebra-presentation).

Commutative ring sheaves are expressed as commutative ring objects in abelian sheaves,
using the recorded section-ring equivalence. Algebra morphisms are ring morphisms
commuting with the specified scalar map. The module universal property is expressed
on sections under that same equivalence. No basis enters any transition or cocone leg.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

set_option backward.isDefEq.respectTransparency false in
/-- The specified closure maps give the finite-free ring, algebra and module presentation
on the cofinal tail of fields containing E.
Source: Bhatt--Scholze 6.8.2(2); blueprint coefficient colimit on X, third comparison,
and Cartesian coefficients, finite-free assertion (2).
(blueprint: lem-sfb-qlbar-tail-finite-free-algebra-presentation).

Proof:
1. Finite intermediate fields are subsets of the set PadicAlgCl ell, hence small;
   the tail is a subtype. It contains E, and the compositum FG bounds F and G.
   Above any H the compositum EH is an initial object, and further composita bound
   pairs. This gives nonemptiness, directedness, filteredness and cofinality, by
   det-def-sfb-qlbar-condensed-subextensions.
2. Point-level maps are inclusions. Functoriality of coefficient pullback gives
   identities and compositions. lem-sfb-subfield-coefficient-map-comp gives the
   compatibility with the closure legs, including the scalar maps from E.
3. lem-sfb-local-field-integral-basis gives an integral basis of size [F:E].
   det-prop-sfb-cartesian-coefficients-finite-free gives the rational module
   isomorphism of this rank for the actual inclusion. For E itself use the basis
   (1), degree one, and the identity coefficient inclusion.
4. By sk-prop-sfb-qlbar-colimit-x the full ring cocone is a colimit. Extend a tail
   cocone t to all H by t_EH composed with a_H,EH. For H contained in J, EH is
   contained in EJ, so the composition law and cocone compatibility make this a
   full cocone. Its unique factorization restricts to the prescribed t_F since
   EF = F. Conversely every tail factorization agrees on H after passing to EH,
   so full-colimit uniqueness proves tail uniqueness.
5. For an S-algebra B with structure s, the E-leg of an algebra cocone is s,
   since a_E,E is the identity. The ring factorization therefore satisfies
   q_E followed by t = s. Ring uniqueness gives algebra uniqueness.
6. Apply lem-sfb-directed-ring-sheaf-module-colimit with the tail ring diagram,
   scalar maps a_E,F and q_E, and its original closure legs. The equivalence
   def-weil-pbc-internal-abelian-sheaf-module-equivalence keeps all underlying
   abelian sections and restrictions, giving exactly the displayed module
   universal property. Bases witness finite freeness only; the specified maps
   were constructed from field inclusions before choosing any basis. -/
theorem qlbar_tail_finite_free_algebra_presentation
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ) :
    Small.{u + 1} (FiniteIntermediateField ℓ) ∧
    Small.{u + 1} {F : FiniteIntermediateField ℓ // E ≤ F} ∧
    Nonempty {F : FiniteIntermediateField ℓ // E ≤ F} ∧
    IsFiltered {F : FiniteIntermediateField ℓ // E ≤ F} ∧
    (∀ F G : {F : FiniteIntermediateField ℓ // E ≤ F},
      ∃ K : {F : FiniteIntermediateField ℓ // E ≤ F}, F ≤ K ∧ G ≤ K) ∧
    (∀ H : FiniteIntermediateField ℓ,
      Nonempty {F : FiniteIntermediateField ℓ // E ≤ F ∧ H ≤ F} ∧
      ∀ F G : {F : FiniteIntermediateField ℓ // E ≤ F ∧ H ≤ F},
        ∃ K : {F : FiniteIntermediateField ℓ // E ≤ F ∧ H ≤ F}, F ≤ K ∧ G ≤ K) ∧
    (∀ H : FiniteIntermediateField ℓ,
      padicSubfieldRingObjMap X ℓ (le_refl H) = 𝟙 (padicSubfieldRingObj X ℓ H)) ∧
    (∀ (H J K : FiniteIntermediateField ℓ) (h : H ≤ J) (k : J ≤ K),
      padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjMap X ℓ k =
        padicSubfieldRingObjMap X ℓ (h.trans k)) ∧
    (∀ (H J : FiniteIntermediateField ℓ) (h : H ≤ J),
      padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjToPadicAlgCl X ℓ J =
        padicSubfieldRingObjToPadicAlgCl X ℓ H) ∧
    (∀ (F : FiniteIntermediateField ℓ) (h : E ≤ F),
      Nonempty ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
        (Mod.regular (padicSubfieldRingObj X ℓ F)) ≅
          Mod.finiteFree (padicSubfieldRingObj X ℓ E)
            (@Module.finrank E F inferInstance inferInstance
              (Module.compHom F (IntermediateField.inclusion h).toRingHom)))) ∧
    (@Module.finrank E E inferInstance inferInstance
      (Module.compHom E (IntermediateField.inclusion (le_refl E)).toRingHom) = 1) ∧
    (∀ (B : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
      (t : ∀ F : {F : FiniteIntermediateField ℓ // E ≤ F},
        {f : padicSubfieldRingObj X ℓ F.1 ⟶ B // IsMonHom f}),
      (∀ (F G : {F : FiniteIntermediateField ℓ // E ≤ F}) (h : F ≤ G),
        padicSubfieldRingObjMap X ℓ h ≫ (t G).1 = (t F).1) →
      ∃! f : {f : padicAlgClRingObj X ℓ ⟶ B // IsMonHom f},
        ∀ F : {F : FiniteIntermediateField ℓ // E ≤ F},
          padicSubfieldRingObjToPadicAlgCl X ℓ F.1 ≫ f.1 = (t F).1) ∧
    (∀ (B : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
      (s : padicSubfieldRingObj X ℓ E ⟶ B) [IsMonHom s]
      (t : ∀ F : {F : FiniteIntermediateField ℓ // E ≤ F},
        {f : padicSubfieldRingObj X ℓ F.1 ⟶ B // IsMonHom f}),
      (∀ (F G : {F : FiniteIntermediateField ℓ // E ≤ F}) (h : F ≤ G),
        padicSubfieldRingObjMap X ℓ h ≫ (t G).1 = (t F).1) →
      (∀ F : {F : FiniteIntermediateField ℓ // E ≤ F},
        padicSubfieldRingObjMap X ℓ F.2 ≫ (t F).1 = s) →
      ∃! f : {f : padicAlgClRingObj X ℓ ⟶ B // IsMonHom f},
        padicSubfieldRingObjToPadicAlgCl X ℓ E ≫ f.1 = s ∧
        ∀ F : {F : FiniteIntermediateField ℓ // E ≤ F},
          padicSubfieldRingObjToPadicAlgCl X ℓ F.1 ≫ f.1 = (t F).1) ∧
    (∀ (M : ringedSiteModules.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (ProEt.topology X) (padicSubfieldRingObj X ℓ E))))
      (t : ∀ F : {F : FiniteIntermediateField ℓ // E ≤ F}, qlbarTailStage X ℓ F.2 ⟶ M),
      (∀ (F G : {F : FiniteIntermediateField ℓ // E ≤ F}) (h : F ≤ G)
        (U : X.ProEtᵒᵖ) (x : (padicSubfieldRingObj X ℓ F.1).obj.obj U),
        (t G).val.app U ((padicSubfieldRingObjMap X ℓ h).hom.app U x) =
          (t F).val.app U x) →
      ∃! f : qlbarTailVertex X ℓ E ⟶ M,
        ∀ (F : {F : FiniteIntermediateField ℓ // E ≤ F})
          (U : X.ProEtᵒᵖ) (x : (padicSubfieldRingObj X ℓ F.1).obj.obj U),
          f.val.app U ((padicSubfieldRingObjToPadicAlgCl X ℓ F.1).hom.app U x) =
            (t F).val.app U x) := by
  classical
  let I := {F : FiniteIntermediateField ℓ // E ≤ F}
  have hdir : ∀ F G : I, ∃ K : I, F ≤ K ∧ G ≤ K := by
    intro F G
    obtain ⟨K, hF, hG⟩ := exists_ge_ge F.1 G.1
    exact ⟨⟨K, F.2.trans hF⟩, hF, hG⟩
  have : Nonempty I := ⟨⟨E, le_rfl⟩⟩
  have : IsDirectedOrder I := ⟨hdir⟩
  have : IsFiltered I := isFiltered_of_directed_le_nonempty I
  have hid (H : FiniteIntermediateField ℓ) :
      padicSubfieldRingObjMap X ℓ (le_refl H) = 𝟙 (padicSubfieldRingObj X ℓ H) := by
    change (upperStarFromPoint X).map (𝟙 _) = _
    exact (upperStarFromPoint X).map_id _
  have hcomp (H J K : FiniteIntermediateField ℓ) (h : H ≤ J) (k : J ≤ K) :
      padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjMap X ℓ k =
        padicSubfieldRingObjMap X ℓ (h.trans k) := by
    change (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map _ = _
    rw [← Functor.map_comp]
    rfl
  let inc : I → FiniteIntermediateField ℓ := Subtype.val
  have hinc : Monotone inc := fun _ _ h ↦ h
  have : hinc.functor.Final := (hinc.final_functor_iff).2 (by
    intro H
    obtain ⟨K, hE, hH⟩ := exists_ge_ge E H
    exact ⟨⟨K, hE⟩, hH⟩)
  let D : I ⥤ Mon (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
    { obj := fun F ↦ Mon.mk (padicSubfieldRingObj X ℓ F.1)
      map := fun h ↦ Mon.Hom.mk (padicSubfieldRingObjMap X ℓ (leOfHom h))
      map_id := fun F ↦ Mon.Hom.ext (hid F.1)
      map_comp := fun a b ↦ Mon.Hom.ext (hcomp _ _ _ (leOfHom a) (leOfHom b)).symm }
  let c : Cocone D :=
    { pt := Mon.mk (padicAlgClRingObj X ℓ)
      ι :=
        { app := fun F ↦ Mon.Hom.mk (padicSubfieldRingObjToPadicAlgCl X ℓ F.1)
          naturality := by
            intro F G h
            apply Mon.Hom.ext
            exact (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (leOfHom h)).trans
              (Category.comp_id _).symm } }
  have hc : IsColimit ((Mon.forget _).mapCocone c) :=
    (Functor.Final.isColimitWhiskerEquiv hinc.functor
      (padicAlgClRingObjCocone X ℓ)).symm (isColimitPadicAlgClRingObjCocone X ℓ)
  obtain ⟨⟨hcRing⟩, _⟩ := Mon.filtered_cocone_isColimit c hc
  have hring (B : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj B] [IsCommMonObj B]
      (t : ∀ F : I, {f : padicSubfieldRingObj X ℓ F.1 ⟶ B // IsMonHom f})
      (ht : ∀ (F G : I) (h : F ≤ G),
        padicSubfieldRingObjMap X ℓ h ≫ (t G).1 = (t F).1) :
      ∃! f : {f : padicAlgClRingObj X ℓ ⟶ B // IsMonHom f},
        ∀ F : I, padicSubfieldRingObjToPadicAlgCl X ℓ F.1 ≫ f.1 = (t F).1 := by
    let d : Cocone D :=
      { pt := Mon.mk B
        ι :=
          { app := fun F ↦ { hom := (t F).1, isMonHom_hom := (t F).2 }
            naturality := by
              intro F G h
              apply Mon.Hom.ext
              exact (ht F G (leOfHom h)).trans (Category.comp_id _).symm } }
    refine ⟨⟨(hcRing.desc d).hom, inferInstance⟩, ?_, ?_⟩
    · intro F
      exact congrArg Mon.Hom.hom (hcRing.fac d F)
    · intro f hf
      apply Subtype.ext
      exact congrArg Mon.Hom.hom
        (hcRing.uniq d { hom := f.1, isMonHom_hom := f.2 } (fun F ↦ Mon.Hom.ext (hf F)))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdir, ?_, hid,
    hcomp, fun _ _ h ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h, ?_, ?_,
    hring, ?_, (qlbar_tail_module_colimit X ℓ E).2.2⟩
  · intro H
    obtain ⟨K, hE, hH⟩ := exists_ge_ge E H
    refine ⟨⟨⟨K, hE, hH⟩⟩, ?_⟩
    intro F G
    obtain ⟨K, hF, hG⟩ := exists_ge_ge F.1 G.1
    exact ⟨⟨K, F.2.1.trans hF, F.2.2.trans hF⟩, hF, hG⟩
  · intro F h
    obtain ⟨⟨b⟩, hb, _⟩ := cartesianCoefficients_finiteFree ℓ h
    obtain ⟨_, e, _⟩ := hb b
    exact ⟨(e X).symm⟩
  · change Module.finrank E E = 1
    exact Module.finrank_self E
  · intro B _ _ s _ t ht hs
    obtain ⟨f, hf, huniq⟩ := hring B t ht
    refine ⟨f, ⟨?_, hf⟩, fun g hg ↦ huniq g hg.2⟩
    have hE := hs ⟨E, le_rfl⟩
    rw [hid, Category.id_comp] at hE
    exact (hf ⟨E, le_rfl⟩).trans hE

end AlgebraicGeometry.ProEtale
