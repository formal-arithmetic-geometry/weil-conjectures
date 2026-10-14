module
public import Sheaf.AlgebraicGeometry.AbelianCounitResolutionCalculation
import Sheaf.Algebra.Homology.MappingCylinderSplitFactorization
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.Algebra.Homology.ModelCategory.Injective

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

/-- The first comparison construction, before the second homotopy is imposed.
The proof is the mapping-cylinder lift of Tags 013P and 013S described in the
core node.
Source: Stacks Project, Tags 013P and 013S.
(blueprint: new-abelian-replacement-section-homotopies-core-counit) -/
theorem exists_section_map_with_counit_homotopy {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op) :
    ∃ q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
        ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
          (standardAbelianResolution X F).cocomplex,
      Nonempty (Homotopy
        (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
        (counitSectionMap f F J)) := by sorry

/-- The lifting homotopy for a map already carrying the counit homotopy.
This is the uniqueness-up-to-homotopy step of Tag 013S.
Source: Stacks Project, Tag 013S.
(blueprint: new-abelian-replacement-section-homotopies-core-second) -/
theorem second_section_homotopy_of_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op)
    (q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
        (standardAbelianResolution X F).cocomplex)
    (hq : Nonempty (Homotopy
      (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
      (counitSectionMap f F J))) :
    Nonempty (Homotopy
      ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
        (forgottenResolutionMap X I))) := by sorry

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
