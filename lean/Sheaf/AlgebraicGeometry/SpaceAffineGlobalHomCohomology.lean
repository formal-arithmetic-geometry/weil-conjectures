module

public import Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
public import Sheaf.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Canonically normalized cohomology of scalar global Hom

Source: Stacks 08JA, 0A8Z (blueprint: def-sfb-space-affine-global-hom-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace AlgebraicGeometry.AlgebraicSpace
section
variable {S : Scheme.{u}} (A : Type u) [CommRing A]
  (Y : Over S) (e : Y.left ≅ Spec (.of A))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)

/-- Scalar-valued global cochains of the actual sheaf Hom complex.
Source: Stacks 0A8Z (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
abbrev affineHomSectionsComplex (P I : CochainComplex X.SmallModules ℤ) :=
  ((affineScalarSections A Y e X f).mapHomologicalComplex (.up ℤ)).obj
    (homComplex (R := X.smallStructureSheaf) P I)

/-- The global Hom-complex comparison is specified componentwise by product projections.
Source: Stacks 0A8Z (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def AffineHomSectionsComplexNormalization (P I : CochainComplex X.SmallModules ℤ)
    (d : ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
        (affineHomSectionsComplex A Y e X f P I) ≅ CochainComplex.HomComplex P I) : Prop :=
  ∀ (n p q : ℤ) (h : p + n = q)
    (s : (affineHomSectionsComplex A Y e X f P I).X n),
    ((d.hom.f n) s).v p q h =
      SheafOfModules.homObjSectionsEquiv (P.X p) (I.X q)
        ((SheafOfModules.homObj (R := X.smallStructureSheaf) (P.X p) (I.X q)).unitHomEquiv
          (s ≫ homComplexπ (R := X.smallStructureSheaf) P I n p q h))

/-- Unique identification of global sheaf Hom cochains with ordinary morphism cochains.
Source: Stacks 0A8Z (blueprint: def-sfb-space-affine-global-hom-cohomology).
Proof: sections commute with products. The product projections, followed by
Hom(O,Hom(Pp,Iq))=Hom(Pp,Iq), give a bijection onto the families of morphisms.
The Hom differential becomes d_I s - (-1)^n s d_P componentwise. This gives the
chain isomorphism, and the component formula determines every component uniquely. -/
theorem affineHomSectionsComplex_existsUnique (P I : CochainComplex X.SmallModules ℤ) :
    ∃! d, AffineHomSectionsComplexNormalization A Y e X f P I d := by
  sorry

/-- The projection-normalized global-cochain isomorphism.
Source: Stacks 0A8Z (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def affineHomSectionsComplexIso (P I : CochainComplex X.SmallModules ℤ) :=
  Classical.choose (affineHomSectionsComplex_existsUnique A Y e X f P I)

/-- Cohomology of global Hom cochains, with the exact forgetful comparison retained.
Source: Stacks 0A8Z (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def affineHomSectionsCohomology (P I : CochainComplex X.SmallModules ℤ) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (DerivedCategory.Q.obj (affineHomSectionsComplex A Y e X f P I))) ≃+
        (CochainComplex.HomComplex P I).homology n :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app _).toLinearEquiv.toAddEquiv
    |>.trans
      ((((affineHomSectionsComplex A Y e X f P I).sc n).mapHomologyIso
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat)).symm.addCommGroupIsoToAddEquiv) |>.trans
      (((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).mapIso
        (affineHomSectionsComplexIso A Y e X f P I)).addCommGroupIsoToAddEquiv)

variable [HasDerivedCategory.{w} X.SmallModules]

/-- The fixed Hom resolution is K-injective and the Hom complex from a K-flat is so.
Source: Stacks 0A96 (blueprint: def-sfb-space-affine-global-hom-cohomology).
Proof: the recorded resolution is K-injective. Tensoring any acyclic complex with
P is acyclic by K-flatness; tensor-Hom adjunction identifies maps into Hom(P,I)
with maps from that acyclic tensor into I, which are null homotopic. -/
theorem affineHomResolution_isKInjective
    (P M : CochainComplex X.SmallModules ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
      (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf) P) :
    (homComplex (R := X.smallStructureSheaf) P
      ((coefficientHomResolution.{u, u, u} X.smallEtaleModelTopology
        X.smallStructureSheaf).obj M)).IsKInjective := by
  sorry

/-- The ordinary Hom-complex cohomology map into derived morphisms is canonical.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def affineExternalDerivedEquiv (P I : CochainComplex X.SmallModules ℤ)
    [I.IsKInjective] (n : ℤ) :
    (CochainComplex.HomComplex P I).homology n ≃+
      (DerivedCategory.Q.obj P ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
  (CochainComplex.HomComplex.homologyAddEquiv P I n).trans
    ((CochainComplex.HomComplex.CohomologyClass.homAddEquiv (K := P) (L := I) (n := n)).trans
      ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
        (CochainComplex.IsKInjective.Qh_map_bijective _ (I⟦n⟧))).trans
        (Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso X.SmallModules).app P)
          ((DerivedCategory.quotientCompQhIso X.SmallModules).app (I⟦n⟧) ≪≫
            (DerivedCategory.Q.commShiftIso n).app I)).toAddEquiv))

/-- The derived sections unit is invertible on every K-injective complex.
Source: Stacks 070K (blueprint: def-sfb-space-affine-global-hom-cohomology).
Proof: its homotopy-category derived unit is invertible on K-injectives. The two
quotient comparison isomorphisms and the mapHomotopyCategory factorization are
invertible; their composite is exactly the displayed complex-level unit. -/
@[instance] theorem affineSectionsComplexUnit_isIso
    (P : CochainComplex X.SmallModules ℤ) [P.IsKInjective] :
    IsIso (affineSectionsComplexUnit A Y e X f P) := by
  sorry

/-- The fixed representative-to-global-Hom comparison uses the actual localization iso.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def affineHomRepresentativeComparison (P M : CochainComplex X.SmallModules ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
      (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf) P) :
    (affineDerivedSections A Y e X f).obj
      (X.derivedHom.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M)) ≅
    DerivedCategory.Q.obj (affineHomSectionsComplex A Y e X f P
      ((coefficientHomResolution.{u, u, u} X.smallEtaleModelTopology
        X.smallStructureSheaf).obj M)) :=
  letI := affineHomResolution_isKInjective X P M hP
  (affineDerivedSections A Y e X f).mapIso
    (coefficientHomResolutionIso.{u, u, u, w} X.smallEtaleModelTopology
      X.smallStructureSheaf P M) ≪≫
      (asIso (affineSectionsComplexUnit A Y e X f
        (homComplex (R := X.smallStructureSheaf) P
          ((coefficientHomResolution.{u, u, u} X.smallEtaleModelTopology
            X.smallStructureSheaf).obj M)))).symm


/-- The actual fixed coefficient resolution has a K-injective target.
Source: Stacks 079V (blueprint: def-sfb-space-affine-global-hom-cohomology).
Proof: unfold the fixed functorial replacement and apply its K-injectivity theorem. -/
@[instance] theorem affineCoefficientHomResolution_isKInjective
    (M : CochainComplex X.SmallModules ℤ) :
    ((coefficientHomResolution.{u, u, u} X.smallEtaleModelTopology
      X.smallStructureSheaf).obj M).IsKInjective := by
  sorry

/-- All-degree Hom identification, specified on every K-flat source representative.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def AffineGlobalHomCohomologyNormalization
    (c : ∀ (L M : X.DerivedModules) (n : ℤ),
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((affineDerivedSections A Y e X f).obj (X.derivedHom.obj (op L, M)))) ≃+
          (L ⟶ M⟦n⟧)) : Prop :=
  (∀ (L M L' M' : X.DerivedModules) (g : L' ⟶ L) (h : M ⟶ M')
    (n : ℤ) (x : _),
    c L' M' n
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((affineDerivedSections A Y e X f).map (X.derivedHom.map (g.op, h))) x) =
      g ≫ c L M n x ≫ h⟦n⟧') ∧
  ∀ (P M : CochainComplex X.SmallModules ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
      (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf) P) (n : ℤ) (x : _),
    c (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M) n x =
      affineExternalDerivedEquiv X P _ n
        (affineHomSectionsCohomology A Y e X f P _ n
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
            (affineHomRepresentativeComparison A Y e X f P M hP)).hom x)) ≫
        (coefficientHomResolutionInverse.{u, u, u, w} X.smallEtaleModelTopology
          X.smallStructureSheaf M)⟦n⟧'

/-- The canonical cohomology identification exists uniquely with the representative formula.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-hom-cohomology).
Proof: compute on a K-flat source and the fixed K-injective target. The localized Hom
factorization and derived-sections unit identify the object with the global Hom
cochain complex. Its product projections give ordinary cochains. Cycles are shifted
chain maps and boundaries are homotopies; K-injectivity identifies homotopy classes
with derived maps. The augmentation inverse gives the specified target M. Common
resolutions and naturality descend the additive equivalences; every derived object
has a K-flat representative, proving uniqueness of the normalized family. -/
theorem affineGlobalHomCohomology_existsUnique :
    ∃! c, AffineGlobalHomCohomologyNormalization A Y e X f c := by
  sorry

/-- The fixed normalized identification in every integer degree.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def affineGlobalHomCohomology :=
  Classical.choose (affineGlobalHomCohomology_existsUnique A Y e X f)


/-- A cohomology class determines a map from A in degree n by projectivity of A.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def moduleCohomologyClass (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A) ⟶ K :=
  (DerivedCategory.homSingleEquivOfProjective (ModuleCat.of A A) n K).symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton A _ x))

/-- Transport the degree-n free generator to the shifted tensor unit.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def moduleShiftedUnitIso (n : ℤ) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A) ≅
      (MonoidalCategory.tensorUnit (DerivedCategory (ModuleCat.{u} A)))⟦-n⟧ :=
  (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
    (-n) n 0 (neg_add_cancel n)).app _).symm ≪≫
      (shiftFunctor _ (-n)).mapIso
        (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} A))

/-- The canonical all-degree cohomology-to-Hom map for ordinary module derived Hom.
The symmetry places evaluation in the same order as the sheaf-side pairing.
Source: Stacks 08JA (blueprint: def-sfb-space-affine-global-hom-cohomology). -/
def moduleDerivedHomClass (K M : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((ordinaryModuleDerivedInternalHom A).obj (op K, M))) : K ⟶ M⟦n⟧ :=
  let j := (moduleShiftedUnitIso A n).inv ≫
    moduleCohomologyClass A ((ordinaryModuleDerivedInternalHom A).obj (op K, M)) n x
  (shiftEquiv' (DerivedCategory (ModuleCat.{u} A)) (-n) n
    (neg_add_cancel n)).toAdjunction.homEquiv K M
    (((MonoidalCategory.leftUnitor K).inv)⟦-n⟧' ≫
      ((MonoidalCategory.tensorRight K).commShiftIso (-n)).inv.app _ ≫
      MonoidalCategory.tensorHom j (𝟙 K) ≫
      ((DerivedMonoidal.braidedCategory' DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))).braiding _ _).hom ≫
      (ihom.ev K).app M)

end
end AlgebraicGeometry.AlgebraicSpace
