module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import Sheaf.Algebra.Homology.FilteredTensorLocalization
public import Sheaf.Algebra.Homology.CanonicalTruncationFiltration
public import Sheaf.Algebra.Homology.BoundedDerivedRoofs
import Sheaf.Algebra.Homology.FilteredQuasiIsoFractions
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Canonical truncations lift bounded derived modules to finite filtered localization

Source: Stacks Project, `more-algebra.tex`, Tag 0H7Z; `homology.tex`, Tag 0118;
Derived Categories, Tags 05RW, 05S2 and 05S6
(blueprint: lem-kun-derived-canonical-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open CochainComplex

namespace DerivedCategory

variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Canonical truncation filtration on bounded derived modules.

Source: Stacks Project, `more-algebra.tex`, Tag 0H7Z; `homology.tex`, Tag 0118;
Derived Categories, Tags 05RW, 05S2 and 05S6
(blueprint: lem-kun-derived-canonical-filtration).

Proof steps. (1) Use `DerivedCategory.boundedDerivedRoofs` to represent bounded
objects and morphisms by bounded complexes and bounded roofs. (2) Apply
`CochainComplex.exists_canonicalTruncationFiltration`; its good truncations form a
finite filtered complex, its two-term graded quotient maps quasi-isomorphically to
shifted cohomology, and its maps and homotopies are filtration preserving.
(3) Use `CochainComplex.filteredTensor_localization` and the filtered
quasi-isomorphism fractions to descend these constructions to the localization.
(4) Forgetting the filtration gives the original derived object and morphism, while
the graded comparison gives `H⁻ⁱ(C)[i]`; naturality of the representative maps
identifies every derived morphism with `u` and `H⁻ⁱ(u)[i]`.
(5) For every bounded representative and every identification `eC : C ≅ Q(K)`,
provide `rep C K hK eC : T(C) ≅ Q_W q(K,F)`. Its chain-map equation is the
representative formula for `T`; its roof equation says the conjugate of `T(u)`
is `Q_W(q(s))⁻¹ ≫ Q_W(q(g))` for every bounded roof representing `u`.
The common-refinement clause of `DerivedCategory.boundedDerivedRoofs`, followed by
`CochainComplex.finiteFilteredModuleQuasiIso_fractions`, makes this independent of
roofs and representatives. In particular, applying the roof equation to an identity
morphism determines the transition `rep_K⁻¹ ≫ rep_L` between any two representatives.
(6) The natural representative identifications `eForget` and `eGrade` specify the
forgetful and graded functors on all finite filtered complexes and maps. The two
normalization equations tie `rep` to `eOmega` via `eC` and to `eGr` via the specified
quotient `pi`, the canonical homology comparison, and the single-complex shift
isomorphism. Thus the representative transitions preserve both comparisons.
No termwise functorial choice of a bounded representative is made.
-/
theorem exists_derivedCanonicalFiltration :
    ∃ (F : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
        DecreasingFiltration K)
      (pi : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (F K).gradedPiece i ⟶
          (CochainComplex.singleFunctor (ModuleCat.{u} R) (-i)).obj
            (K.homology (-i))),
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (F K).step i = Subobject.mk (K.ιTruncLE (-i))) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
        (∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) →
          ∃ (a b : ℤ), a < b ∧ (F K).step a = ⊤ ∧ (F K).step b = ⊥) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (i : ℤ),
        ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ)
          (e : (F K).gradedPiece i ≅ M)
          (e₀ : M.X (-i - 1) ≅ cokernel (kernel.ι (K.d (-i - 1) (-i))))
          (e₁ : M.X (-i) ≅ K.cycles (-i)),
          (∀ (r : ℤ), r ≠ -i - 1 → r ≠ -i → IsZero (M.X r)) ∧
          Mono (M.d (-i - 1) (-i)) ∧
          cokernel.π (kernel.ι (K.d (-i - 1) (-i))) ≫ e₀.inv ≫
              M.d (-i - 1) (-i) ≫ e₁.hom ≫ K.iCycles (-i) =
            K.d (-i - 1) (-i) ∧
          (pi K i).f (-i) ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-i)
                (K.homology (-i))).hom =
            e.hom.f (-i) ≫ e₁.hom ≫ K.homologyπ (-i) ∧
          QuasiIso (pi K i)) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        ∃ (φ : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
          φ.hom = f ∧
          ∀ (i : ℤ), FilteredObject.gradedMapSteps φ i ≫ pi L i =
            pi K i ≫
              (CochainComplex.singleFunctor (ModuleCat.{u} R) (-i)).map
                (HomologicalComplex.homologyMap f (-i))) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f g : K ⟶ L) (h : Homotopy f g),
        ∃ (hf : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
          hf.hom = f ∧
          ∃ (hg : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
            hg.hom = g ∧
            ∀ (i : ℤ),
              ∃ (hf_i hg_i :
                  ((F K).step i : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
                    ((F L).step i : CochainComplex (ModuleCat.{u} R) ℤ))
                (h_i : Homotopy hf_i hg_i),
                hf_i ≫ ((F L).step i).arrow =
                    ((F K).step i).arrow ≫ f ∧
                  hg_i ≫ ((F L).step i).arrow =
                    ((F K).step i).arrow ≫ g ∧
                  ∀ (n m : ℤ),
                    ((F K).step i).arrow.f n ≫ h.hom n m =
                      h_i.hom n m ≫ ((F L).step i).arrow.f m) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L), (∀ (r : ℤ), IsIso (K.homologyMap f r)) →
          ∀ (i : ℤ), ∃ (φ : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
            φ.hom = f ∧ QuasiIso (FilteredObject.gradedMapSteps φ i)) ∧
      ∃ (T : DerivedCategory.Bounded (ModuleCat.{u} R) ⥤
        (finiteFilteredModuleQuasiIso R).Localization)
        (omega : (finiteFilteredModuleQuasiIso R).Localization ⥤
          DerivedCategory (ModuleCat.{u} R))
        (gr : ℤ → (finiteFilteredModuleQuasiIso R).Localization ⥤
          DerivedCategory (ModuleCat.{u} R))
        (eOmega : T ⋙ omega ≅ DerivedCategory.Bounded.ι)
        (eGr : ∀ i : ℤ,
          T ⋙ gr i ≅
            DerivedCategory.Bounded.ι ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-i) ⋙
              DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
              shiftFunctor (DerivedCategory (ModuleCat.{u} R)) i)
        (eForget : ∀ P : FiniteFilteredModuleComplex R,
          omega.obj ((finiteFilteredModuleHomotopyQuotient R ⋙
            (finiteFilteredModuleQuasiIso R).Q).obj P) ≅
              DerivedCategory.Q.obj P.obj.obj)
        (eGrade : ∀ (i : ℤ) (P : FiniteFilteredModuleComplex R),
          (gr i).obj ((finiteFilteredModuleHomotopyQuotient R ⋙
            (finiteFilteredModuleQuasiIso R).Q).obj P) ≅
              DerivedCategory.Q.obj (P.obj.filtration.gradedPiece i))
        (hfinite : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
          (∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) →
            (F K).IsFinite)
        (rep : ∀ (C : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K),
          T.obj C ≅ (finiteFilteredModuleHomotopyQuotient R ⋙
            (finiteFilteredModuleQuasiIso R).Q).obj ⟨⟨K, F K⟩, hfinite K hK⟩),
        (∀ (P P' : FiniteFilteredModuleComplex R) (f : P ⟶ P'),
          omega.map ((finiteFilteredModuleHomotopyQuotient R ⋙
              (finiteFilteredModuleQuasiIso R).Q).map f) ≫ (eForget P').hom =
            (eForget P).hom ≫ DerivedCategory.Q.map f.hom.hom) ∧
        (∀ (i : ℤ) (P P' : FiniteFilteredModuleComplex R) (f : P ⟶ P'),
          (gr i).map ((finiteFilteredModuleHomotopyQuotient R ⋙
              (finiteFilteredModuleQuasiIso R).Q).map f) ≫ (eGrade i P').hom =
            (eGrade i P).hom ≫
              DerivedCategory.Q.map (FilteredObject.gradedMapSteps f.hom i)) ∧
        (∀ (C : DerivedCategory.Bounded (ModuleCat.{u} R)),
          ∃ (a b : ℤ) (K : CochainComplex (ModuleCat.{u} R) ℤ),
            a ≤ b ∧ K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧
              Nonempty (C.1 ≅ DerivedCategory.Q.obj K)) ∧
        (∀ (C : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K),
          eOmega.hom.app C ≫ eC.hom =
            omega.map (rep C K hK eC).hom ≫
              (eForget ⟨⟨K, F K⟩, hfinite K hK⟩).hom) ∧
        (∀ (i : ℤ) (C : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K),
          (eGr i).hom.app C ≫
              (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
                shiftFunctor (DerivedCategory (ModuleCat.{u} R)) i).map
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-i)).map eC.hom ≫
                  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-i)).hom.app K) =
            (gr i).map (rep C K hK eC).hom ≫
              (eGrade i ⟨⟨K, F K⟩, hfinite K hK⟩).hom ≫
              DerivedCategory.Q.map (pi K i) ≫
              ((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso
                i (-i) 0 (add_neg_cancel i)).inv.app (K.homology (-i))) ∧
        (∀ (C C' : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K L : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K)
          (eC' : C'.1 ≅ DerivedCategory.Q.obj L)
          (f : FilteredObject.HomPreservingSteps ⟨K, F K⟩ ⟨L, F L⟩),
          T.map (ObjectProperty.homMk
              (eC.hom ≫ DerivedCategory.Q.map f.hom ≫ eC'.inv)) ≫
              (rep C' L hL eC').hom =
            (rep C K hK eC).hom ≫
              (finiteFilteredModuleHomotopyQuotient R ⋙
                (finiteFilteredModuleQuasiIso R).Q).map
                (ObjectProperty.homMk f :
                  (⟨⟨K, F K⟩, hfinite K hK⟩ : FiniteFilteredModuleComplex R) ⟶
                    ⟨⟨L, F L⟩, hfinite L hL⟩)) ∧
        (∀ (C C' : DerivedCategory.Bounded (ModuleCat.{u} R))
          (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
          (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
          (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
          (hM : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (M.X r))
          (eC : C.1 ≅ DerivedCategory.Q.obj K)
          (eC' : C'.1 ≅ DerivedCategory.Q.obj L)
          (s : FilteredObject.HomPreservingSteps ⟨M, F M⟩ ⟨K, F K⟩)
          (g : FilteredObject.HomPreservingSteps ⟨M, F M⟩ ⟨L, F L⟩)
          (hs : QuasiIso s.hom) (f : C ⟶ C'),
          f.hom = eC.hom ≫ inv (DerivedCategory.Q.map s.hom) ≫
            DerivedCategory.Q.map g.hom ≫ eC'.inv →
          ∃ (_hs' : IsIso ((finiteFilteredModuleHomotopyQuotient R ⋙
            (finiteFilteredModuleQuasiIso R).Q).map
              (ObjectProperty.homMk s :
                (⟨⟨M, F M⟩, hfinite M hM⟩ : FiniteFilteredModuleComplex R) ⟶
                  ⟨⟨K, F K⟩, hfinite K hK⟩))),
          (rep C K hK eC).inv ≫ T.map f ≫ (rep C' L hL eC').hom =
            inv ((finiteFilteredModuleHomotopyQuotient R ⋙
              (finiteFilteredModuleQuasiIso R).Q).map
                (ObjectProperty.homMk s :
                  (⟨⟨M, F M⟩, hfinite M hM⟩ : FiniteFilteredModuleComplex R) ⟶
                    ⟨⟨K, F K⟩, hfinite K hK⟩)) ≫
              (finiteFilteredModuleHomotopyQuotient R ⋙
                (finiteFilteredModuleQuasiIso R).Q).map
                (ObjectProperty.homMk g :
                  (⟨⟨M, F M⟩, hfinite M hM⟩ : FiniteFilteredModuleComplex R) ⟶
                    ⟨⟨L, F L⟩, hfinite L hL⟩)) ∧
        (∀ (C C' : DerivedCategory.Bounded (ModuleCat.{u} R)) (f : C ⟶ C'),
          eOmega.hom.app C ≫ DerivedCategory.Bounded.ι.map f =
            (T ⋙ omega).map f ≫ eOmega.hom.app C') ∧
        (∀ (i : ℤ) (C C' : DerivedCategory.Bounded (ModuleCat.{u} R))
          (f : C ⟶ C'),
          (eGr i).hom.app C ≫
              (DerivedCategory.Bounded.ι ⋙
                DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-i) ⋙
                DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
                shiftFunctor (DerivedCategory (ModuleCat.{u} R)) i).map f =
            (T ⋙ gr i).map f ≫ (eGr i).hom.app C') := by
  sorry

end DerivedCategory
