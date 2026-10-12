module

public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.CategoryTheory.Sites.Point.Over
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Finite constant local models exist on a trivializing cover.

Source: Stacks Project, Tag 03RV, local-model step, with the geometric stalk
comparison of Tag 03Q1.
(blueprint: lem-weil-pbc-finite-locally-constant-sets-local-models)

Proof: Choose the cover in hloc. The essential-image definition of IsConstant
supplies a value S and an isomorphism to the constant sheaf on the localized site.
For a nonempty member U, choose a point and an algebraic closure of its residue
field in universe u. This gives a geometric point of U and, by composition, of T.
The stalk of E restricted to U at this point is the stalk of E at the composed
point: pointed etale neighbourhoods are compared by fibre products. Sheafification
preserves stalks, and the filtered colimit of the constant diagram S over pointed
neighbourhoods is S. Thus the local isomorphism identifies S with a stalk of E.
The hypothesis hfin makes this stalk finitely generated as a set, equivalently
finite, so S is finite. Discard the empty members of the cover; its nonempty members
still jointly cover T. Their index set is a subtype in universe u, hence gives a
Cover of the required universe. If T is empty this subtype is empty, and the
conclusion is vacuous on the empty cover. Values may be empty, and different
members may have different finite cardinalities; no uniform bound is needed. -/
theorem finiteLocallyConstant_exists_local_models
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hloc : ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)))
    (hfin : IsFiniteSheaf E) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      ∃ S : Type (u + 1), Finite S ∧
        Nonempty ((E.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf (T.smallEtaleTopology.over
            (𝒰.etalePrecoverageToEtale i)) (Type (u + 1))).obj S) := by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  have := hfin
  obtain ⟨𝒱, h𝒱⟩ := hloc
  let 𝒰 : Cover.{u} etalePrecoverage T :=
    { I₀ := { i : 𝒱.I₀ // Nonempty (𝒱.X i) }
      X i := 𝒱.X i.1
      f i := 𝒱.f i.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun x ↦ ?_, fun i ↦ 𝒱.map_prop i.1⟩
        obtain ⟨i, y, hy⟩ := 𝒱.exists_eq x
        exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩ }
  refine ⟨𝒰, fun i ↦ ?_⟩
  have := h𝒱 i.1
  obtain ⟨S, ⟨e⟩⟩ := (E.over (𝒱.etalePrecoverageToEtale i.1)).mem_essImage_of_isConstant
  let U := 𝒱.etalePrecoverageToEtale i.1
  have : Nonempty U.left := i.2
  let x : U.left := Classical.arbitrary _
  let Ω := SeparableClosure (U.left.residueField x)
  let s : Spec (.of Ω) ⟶ U.left := (SpecToEquivOfField Ω _).2
    ⟨x, CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)⟩
  let Φ := pointSmallEtale (s ≫ U.hom)
  let lift : Φ.fiber.obj U := Over.homMk s rfl
  let Ψ := Φ.over lift
  let neighbourhoods := FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber lift
  let forgetLift := neighbourhoods.functor ⋙ Over.forget (Φ.fiber.elementsMk U lift)
  have : forgetLift.Initial := inferInstance
  have eStalk : Ψ.sheafFiber.obj (E.over U) ≅ Φ.sheafFiber.obj E := by
    change Limits.colimit ((CategoryOfElements.π Ψ.fiber).op ⋙ (E.over U).obj) ≅
      Limits.colimit ((CategoryOfElements.π Φ.fiber).op ⋙ E.obj)
    have h : (CategoryOfElements.π Ψ.fiber).op ⋙ (E.over U).obj =
        forgetLift.op ⋙ (CategoryOfElements.π Φ.fiber).op ⋙ E.obj := rfl
    rw [h]
    exact Functor.Final.colimitIso forgetLift.op _
  let eValue : (pointSmallEtale (s ≫ U.hom)).sheafFiber.obj E ≅ S :=
    eStalk.symm ≪≫ Ψ.sheafFiber.mapIso e.symm ≪≫ Ψ.sheafFiberConstantSheafIso S
  have hgen := (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
    (F := E) Ω (s ≫ U.hom)).of_iso eValue
  exact ⟨S, (ConcreteCategory.isFinitelyGenerated_iff_finite S).mp hgen, ⟨e.symm⟩⟩

end AlgebraicGeometry.Scheme
