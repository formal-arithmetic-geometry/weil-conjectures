module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatum
import Sheaf.AlgebraicGeometry.EtaleRepresentableDescentGlue
import Sheaf.AlgebraicGeometry.FiniteEtaleDescent
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteConstant_localRepresentative
    {T : Scheme.{u}} (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (S : Type (u + 1)) [Finite S]
    (e : E.over U ≅ (constantSheaf (T.smallEtaleTopology.over U) (Type (u + 1))).obj S) :
    ∃ Q : U.left.FiniteEtale,
      Nonempty (((Etale.overSheafEquiv U (Type (u + 1))).functor.obj
        (E.over U)).obj ≅ uliftYoneda.{u + 1}.obj Q.obj) := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let J := ULift.{u, 0} (Fin (Fintype.card S))
  let v : S ≅ ULift.{u + 1, u} J :=
    (Fintype.equivFin S |>.trans Equiv.ulift.symm |>.trans Equiv.ulift.symm).toIso
  let π : (∐ fun _ : J ↦ U.left) ⟶ U.left := Sigma.desc fun _ ↦ 𝟙 U.left
  have : Etale π := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have hπ : IsFinite π := inferInstance
  let Q : U.left.FiniteEtale := ⟨Etale.mk π, hπ⟩
  obtain ⟨hH, _, _, φ, _, hφ, _⟩ := constantSheaf_sets_representable U.left J
  let : IsIso φ := hφ
  let H : Sheaf U.left.smallEtaleTopology (Type (u + 1)) :=
    ⟨constantSetCoproductPresheaf U.left J, hH⟩
  let C := Etale.overSheafEquiv U (Type (u + 1))
  let c := (Etale.overEquiv U).constantSheafSheafCongrIso
    (T.smallEtaleTopology.over U) U.left.smallEtaleTopology (Type (u + 1))
    Over.mkIdTerminal
  let j : C.functor.obj (E.over U) ≅ H :=
    C.functor.mapIso e ≪≫ c.app S ≪≫
      (constantSheaf U.left.smallEtaleTopology (Type (u + 1))).mapIso v ≪≫ asIso φ
  let b : H.obj ≅ uliftYoneda.{u + 1}.obj Q.obj :=
    NatIso.ofComponents (fun W ↦
      { hom := ↾fun s ↦ ⟨MorphismProperty.Over.homMk s.down.left s.down.w⟩
        inv := ↾fun s ↦ ⟨Over.homMk s.down.left (MorphismProperty.Over.w s.down)⟩
        hom_inv_id := by ext s; rfl
        inv_hom_id := by ext s; rfl })
      (fun f ↦ by ext s; rfl)
  exact ⟨Q, ⟨(sheafToPresheaf U.left.smallEtaleTopology (Type (u + 1))).mapIso j ≪≫ b⟩⟩

/-- Effective descent glues finite constant local models into a finite etale scheme.

Source: Stacks Project, Tag 03RV, converse descent part.
(blueprint: lem-weil-pbc-finite-locally-constant-sets-descent)

Proof: Choose the cover and local values in hlocal. Replace each finite S in
universe u+1 by ULift of Fin n for its cardinality n, transporting the constant
sheaf by this equivalence. The equivalence between the site localized at U -> T
and the small etale site of U identifies the given restriction with this constant
sheaf. Apply constantSheaf_sets_representable to Fin n: its representative is the
coproduct of n copies of U with the codiagonal. This morphism is finite and etale,
including n=0. On overlaps the two restrictions both identify with the restriction
of E. Yoneda full faithfulness turns their comparison into a unique isomorphism of
representing schemes; its faithfulness gives the cocycle on triple overlaps.
Take the coproduct of the cover members. It is an etale surjection onto T. The
coproduct of the local representatives is finite etale over it, since the preimage
of each open component is the corresponding finite etale representative. The
overlap isomorphisms give a descent datum on this object. Apply finiteEtaleDescent
to obtain a finite etale scheme P over T with these local representatives.
The local isomorphisms of presheaves agree by the chosen datum; the sheaf condition
on E and the subcanonical small etale topology glue them and their inverses.
This yields the displayed isomorphism with uliftYoneda of Etale.mk pi. If the
cover is empty, T is empty; use the empty scheme and the unique sheaf on its
small etale site. No quasi-compactness of T or bound on the local ranks is used. -/
theorem finiteLocallyConstant_descent_of_local_models
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hlocal : ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      ∃ S : Type (u + 1), Finite S ∧
        Nonempty ((E.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf (T.smallEtaleTopology.over
            (𝒰.etalePrecoverageToEtale i)) (Type (u + 1))).obj S)) :
    ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : Etale π),
      Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Etale.mk π)) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hlocal
  have hrep : ∀ i, ∃ Q : (𝒰.etalePrecoverageToEtale i).left.FiniteEtale,
      Nonempty (((Etale.overSheafEquiv (𝒰.etalePrecoverageToEtale i)
        (Type (u + 1))).functor.obj (E.over (𝒰.etalePrecoverageToEtale i))).obj ≅
          uliftYoneda.{u + 1}.obj Q.obj) := by
    intro i
    obtain ⟨S, hS, ⟨e⟩⟩ := h𝒰 i
    let : Finite S := hS
    exact finiteConstant_localRepresentative E (𝒰.etalePrecoverageToEtale i) S e
  obtain ⟨U, hU, D, e, he⟩ := finiteLocalModels_descentDatum T E 𝒰 hrep
  let : Surjective U.hom := hU
  let : Etale U.hom := U.prop
  let : Etale D.obj.V.hom := D.property.2
  obtain ⟨F, q, ⟨hF⟩, hq, _⟩ := finiteEtaleDescent U.hom
  let : F.IsEquivalence := hF
  let P := F.objPreimage D
  let d : F.obj P ≅ D := F.objObjPreimageIso D
  let k : D.obj.V ≅ (F.obj P).obj.V :=
    { hom := d.inv.hom.hom
      inv := d.hom.hom.hom
      hom_inv_id := congrArg (fun f : D ⟶ D ↦ f.hom.hom) d.inv_hom_id
      inv_hom_id := congrArg (fun f : F.obj P ⟶ F.obj P ↦ f.hom.hom) d.hom_inv_id }
  let r : D.obj.V.left ⟶ P.obj.left := k.hom.left ≫ q P
  obtain ⟨_, hp, ht⟩ := hq P
  have hpr : IsPullback r D.obj.V.hom P.obj.hom U.hom := by
    apply hp.of_iso' ((Over.forget U.left).mapIso k)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [r]
    · simp
    · simp
    · simp
  have htr : ∀ {W : Scheme.{u}} (a b : W ⟶ U.left)
      (h : a ≫ U.hom = b ≫ U.hom) (z : Over.mk a ⟶ D.obj.V),
      (D.obj.datum.transport a b h z).left ≫ r = z.left ≫ r := by
    intro W a b h z
    have hk := d.inv.hom.commutes a b h z
    calc
      (D.obj.datum.transport a b h z).left ≫ r =
          ((F.obj P).obj.datum.transport a b h (z ≫ k.hom)).left ≫ q P := by
        simpa [r, k, Category.assoc] using
          (congrArg (fun f ↦ f.left ≫ q P) hk).symm
      _ = (z ≫ k.hom).left ≫ q P := ht a b h (z ≫ k.hom)
      _ = z.left ≫ r := by simp [r, Category.assoc]
  let : IsFinite P.obj.hom := P.property
  let : Etale P.obj.hom := P.obj.prop
  exact ⟨P.obj.left, P.obj.hom, inferInstance, inferInstance,
    etaleRepresentable_descentGlue T E U D.obj e he
      P.obj.left P.obj.hom r hpr htr⟩

end AlgebraicGeometry.Scheme
