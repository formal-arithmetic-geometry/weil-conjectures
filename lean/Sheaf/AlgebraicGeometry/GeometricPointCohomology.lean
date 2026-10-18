module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Étale cohomology of one geometric point

Source: Stacks Project, Étale Cohomology, Theorem 03QT, Lemmas 03QU and 04JM,
Section 03QQ (specialized to an algebraically closed field)
(blueprint: lem-weil-pbc-geometric-point-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For the spectrum of an algebraically closed field, étale cohomology is concentrated
in degree zero, and degree zero is the geometric stalk. The isomorphism is natural in
an abelian étale sheaf. The proof follows Lemma 03QU using Lemma 04JM: the absolute
Galois group is trivial, global sections identify with the chosen geometric stalk,
and the stalk functor is exact; exactness gives the vanishing in positive degrees and
identifies degree zero with the displayed stalk.
(blueprint: lem-weil-pbc-geometric-point-cohomology)
-/
theorem geometricPoint_etaleCohomology
    (k : Type u) [Field k] [IsAlgClosed k]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (cbar : Spec (.of Ω) ⟶ Spec (.of k))
    :
    (∀ (q : ℤ), 0 < q →
      ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat),
        IsZero ((Etale.cohomology AddCommGrpCat (Spec (.of k)) q).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) ∧
    ∃ α : ∀ F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat,
      (Etale.cohomology AddCommGrpCat (Spec (.of k)) 0).obj
          ((DerivedCategory.singleFunctor _ 0).obj F) ≅
        (Scheme.pointSmallEtale cbar).sheafFiber.obj F,
      ∀ (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat)
        (f : F ⟶ G),
        (α F).hom ≫ (Scheme.pointSmallEtale cbar).sheafFiber.map f =
          (Etale.cohomology AddCommGrpCat (Spec (.of k)) 0).map
              ((DerivedCategory.singleFunctor _ 0).map f) ≫ (α G).hom := by
  let : IsAlgClosed (IsLocalRing.ResidueField k) :=
    IsAlgClosed.of_ringEquiv k (IsLocalRing.ResidueField k)
      (RingEquiv.ofBijective (IsLocalRing.residue k)
      ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩)
  let : IsStrictlyHenselianLocalRing k :=
    (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed k).2
      ⟨inferInstance, inferInstance⟩
  obtain ⟨hgerm, hnat⟩ := Scheme.strictlyHenselianSections_geometricStalk_isIso.{u, u}
    (R := k) inferInstance cbar (by exact Subsingleton.elim _ _)
  let Γ := Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}
  let γ : (sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 (Spec (.of k))))) ⟶
      (Scheme.pointSmallEtale cbar).sheafFiber :=
    { app := fun F ↦ (Scheme.pointSmallEtale cbar).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of k))))
        (Over.homMk cbar (Category.comp_id cbar)) F.obj
      naturality := fun _ _ f ↦ (hnat _ _ f).symm }
  have : ∀ F, IsIso (γ.app F) := hgerm
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  let δ : Γ ≅ (Scheme.pointSmallEtale cbar).sheafFiber :=
    Sheaf.ΓNatIsoSheafSections _ _
      (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) _) ≪≫ asIso γ
  have : PreservesFiniteColimits Γ := preservesFiniteColimits_of_natIso δ.symm
  let e (q : ℤ) := (Γ.rightDerivedFunctorHomologyFunctorIso q).symm
  constructor
  · intro q hq F
    refine IsZero.of_iso (Γ.map_isZero ?_)
      ((e q).app ((DerivedCategory.singleFunctor _ 0).obj F))
    exact DerivedCategory.isZero_of_isLE _ 0 q hq
  · let ε : DerivedCategory.singleFunctor _ 0 ⋙
        Etale.cohomology AddCommGrpCat (Spec (.of k)) 0 ≅
        (Scheme.pointSmallEtale cbar).sheafFiber :=
      Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0) (e 0) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0) Γ ≪≫
        Functor.leftUnitor Γ ≪≫ δ
    exact ⟨fun F ↦ ε.app F, fun F G f ↦ (ε.hom.naturality f).symm⟩

end AlgebraicGeometry
