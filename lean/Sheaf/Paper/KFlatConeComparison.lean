/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
/-!
# The two-resolution tensor augmentation square

Source: Stacks Project, Cohomology on Sites, Tags 06YP, 06YS, 06YT and 06YU
(blueprint: lem-pur-kflat-cone-comparison).

The tensor model is supplied with its natural representative comparison, as in
`wf_site_derived_tensor_descent`. No choice of a bare derived tensor object is made.
All auxiliary names below package the objects and maps of this one comparison square.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Prod MonoidalCategory

namespace SheafOfModules.KFlatConeComparison

variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  (R : Sheaf J CommRingCat.{max u v})

/-- The existing module-sheaf category. Source: Stacks 06YP
(blueprint: lem-pur-kflat-cone-comparison). -/
abbrev Modules := CategoryTheory.ringedSiteModules.{max u v, max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

/-- Degree-zero embedding. Source: Stacks 06YU
(blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable abbrev single := HomologicalComplex.single (Modules R) (.up ℤ) (0 : ℤ)

/-- The existing sheaf tensor bifunctor. Source: Stacks 06YM
(blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def tensor : Modules R ⥤ Modules R ⥤ Modules R :=
  letI := SheafOfModules.monoidalCategory R
  curriedTensor _

/-- The existing total tensor bifunctor. Source: Stacks 06YM
(blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def total : CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ :=
  letI := SheafOfModules.monoidalCategory R
  Functor.uncurry.obj ((curriedTensor (Modules R)).map₂CochainComplex)

/-- The resolving class of the cited descent theorem, on complexes.
Source: Stacks 06YS, 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
def resolving : ObjectProperty (CochainComplex (Modules R) ℤ) := fun P =>
  CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, v, max u v, max u v}
      (J := J) (R := R) (P.X n)

/-- The two augmented bounded-above flat K-flat resolutions, with all hypotheses.
Source: Stacks 06YP, 06YS, 06YT (blueprint: lem-pur-kflat-cone-comparison). -/
structure Pair where
  L : Modules R
  M : Modules R
  P : CochainComplex (Modules R) ℤ
  K : CochainComplex (Modules R) ℤ
  q : P ⟶ (single R).obj L
  ε : K ⟶ (single R).obj M
  q_quasiIso : QuasiIso q
  ε_quasiIso : QuasiIso ε
  P_bounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)
  K_bounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)
  P_resolving : resolving R P
  K_resolving : resolving R K

variable {R}

/-- Morphisms of both augmented resolutions, allowing maps of L and M as well.
Source: Stacks 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
structure Hom (r s : Pair R) where
  l : r.L ⟶ s.L
  m : r.M ⟶ s.M
  p : r.P ⟶ s.P
  k : r.K ⟶ s.K
  q_comm : p ≫ s.q = r.q ≫ (single R).map l
  ε_comm : k ≫ s.ε = r.ε ≫ (single R).map m

variable (R)

/-- Canonical identification of the lower-right vertex with (L tensor M)[0].
Source: Stacks 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def ordinaryIso (L M : Modules R) :
    (total R).obj ((single R).obj L, (single R).obj M) ≅
      (single R).obj (((tensor R).obj L).obj M) :=
  letI := SheafOfModules.monoidalCategory R
  CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) L ((single R).obj M) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex ((curriedTensor _).obj L) (.up ℤ) 0).app M

/-- Koszul symmetry, induced by sheaf braiding and signed total-complex transposition.
Source: Stacks 06YM (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def swap (K L : CochainComplex (Modules R) ℤ) :
    (total R).obj (K, L) ≅ (total R).obj (L, K) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  let T := curriedTensor (Modules R)
  let A := ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let B := ((T.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let e : A ≅ B := HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => β_ (K.X p) (L.X q)) (by
        intro q q' _
        exact (BraidedCategory.braiding_naturality_right (K.X p) (L.d q q')).symm))
    (by
      intro p p' _
      ext q : 1
      exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm)
  exact HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)

/-- Canonical map of cones from a commuting square, for the stated Y plus X[1] convention.
Source: Stacks 05RU (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def coneMap {A B A' B' : CochainComplex (Modules R) ℤ}
    {f : A ⟶ B} {g : A' ⟶ B'} (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ g = f ≫ b) : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone g :=
  HomologicalComplex.homotopyCofiber.mapArrowHom f g
    (fun j : ℤ => ⟨j - 1, by change j - 1 + 1 = j; omega⟩) (Arrow.homMk a b h)

/-- Restriction of Q times Q to the resolving complexes of tensor descent.
Source: Stacks 06YS, 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def localizationPair [HasDerivedCategory.{w} (Modules R)] :=
  ((resolving R).ι ⋙ DerivedCategory.Q).prod ((resolving R).ι ⋙ DerivedCategory.Q)

/-- Total tensor followed by Q on the same resolving class.
Source: Stacks 06YS, 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def resolvedTensor [HasDerivedCategory.{w} (Modules R)] :=
  ((resolving R).ι.prod (resolving R).ι) ⋙ total R ⋙ DerivedCategory.Q

/-- The resolved pair as an object of the resolving product category.
Source: Stacks 06YS (blueprint: lem-pur-kflat-cone-comparison). -/
abbrev resolvedPair (r : Pair R) : (resolving R).FullSubcategory ×
    (resolving R).FullSubcategory :=
  (⟨r.P, r.P_resolving⟩, ⟨r.K, r.K_resolving⟩)

variable [HasDerivedCategory.{w} (Modules R)]

/-- The canonical derived-to-ordinary map in a model with its natural representative iso.
This is the tensor augmentation roof, not an arbitrary morphism or a choice from existence.
Source: Stacks 06YU (blueprint: lem-pur-kflat-cone-comparison). -/
noncomputable def comparison
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    T.obj (DerivedCategory.Q.obj ((single R).obj r.L),
      DerivedCategory.Q.obj ((single R).obj r.M)) ⟶
        DerivedCategory.Q.obj ((single R).obj (((tensor R).obj r.L).obj r.M)) :=
  letI := r.q_quasiIso
  letI := r.ε_quasiIso
  (T.mapIso ((asIso (DerivedCategory.Q.map r.q)).prod
    (asIso (DerivedCategory.Q.map r.ε)))).inv ≫
    ρ.inv.app (resolvedPair R r) ≫ DerivedCategory.Q.map ((total R).map (r.q ×ₘ r.ε)) ≫
      DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom

/-- The complete two-resolution augmentation comparison, including natural cone isomorphisms
and the normalization identifying the right arrow with the canonical tensor augmentation roof.
The parameter ρ is the natural representative comparison of the derived tensor model supplied
by `lem-weil-pbc-site-derived-tensor-descent`; thus the assertion applies to any such model.

Source: Stacks Project, Tags 06YM, 06YP, 06YS, 06YT, 06YU and Definition 05RU
(blueprint: lem-pur-kflat-cone-comparison).

Proof: bifunctoriality gives the square. The cones of q and ε are acyclic by
`lem-pur-quasi-iso-cone-acyclic`. K-flatness makes Cone(ε) tensor P and Cone(q) tensor K
acyclic. The signed tensor-cone isomorphisms of `lem-pc-tensor-mapping-cone-iso`, followed
in the top case by Koszul symmetry, identify these with the top and left cones; the
cone criterion proves both quasi-isomorphisms. Their inclusions and naturality follow
from the same signed formulas. Tensor descent identifies Q(P tensor K) with the derived
tensor; composing ρ with T(Qq,Qε) identifies it with L derived-tensor M. Invert the top
arrow to obtain e. Bifunctoriality then cancels the top arrow in the augmentation roof,
so the right arrow is precisely the canonical comparison. If the bottom arrow is a
quasi-isomorphism, cohomology and two-out-of-three make the right arrow invertible.
Naturality of tensor, cones and ρ gives all morphism-of-resolution compatibilities. -/
theorem augmentation_square
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) :
    ∃ (topCone : ∀ r : Pair R,
        CochainComplex.mappingCone ((total R).map (𝟙 r.P ×ₘ r.ε)) ≅
          (total R).obj (CochainComplex.mappingCone r.ε, r.P))
      (leftCone : ∀ r : Pair R,
        CochainComplex.mappingCone ((total R).map (r.q ×ₘ 𝟙 r.K)) ≅
          (total R).obj (CochainComplex.mappingCone r.q, r.K))
      (e : ∀ r : Pair R,
        DerivedCategory.Q.obj ((total R).obj (r.P, (single R).obj r.M)) ≅
          T.obj (DerivedCategory.Q.obj ((single R).obj r.L),
            DerivedCategory.Q.obj ((single R).obj r.M))),
      ∀ r : Pair R,
        (total R).map (r.q ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 _ ×ₘ r.ε) =
          (total R).map (𝟙 r.P ×ₘ r.ε) ≫ (total R).map (r.q ×ₘ 𝟙 _) ∧
        QuasiIso ((total R).map (𝟙 r.P ×ₘ r.ε)) ∧
        QuasiIso ((total R).map (r.q ×ₘ 𝟙 r.K)) ∧
        CochainComplex.mappingCone.inr ((total R).map (𝟙 r.P ×ₘ r.ε)) ≫ (topCone r).hom =
          (total R).map (𝟙 r.P ×ₘ CochainComplex.mappingCone.inr r.ε) ≫
            (swap R r.P (CochainComplex.mappingCone r.ε)).hom ∧
        CochainComplex.mappingCone.inr ((total R).map (r.q ×ₘ 𝟙 r.K)) ≫ (leftCone r).hom =
          (total R).map (CochainComplex.mappingCone.inr r.q ×ₘ 𝟙 r.K) ∧
        DerivedCategory.Q.map ((total R).map (𝟙 r.P ×ₘ r.ε)) ≫ (e r).hom =
          ρ.hom.app (resolvedPair R r) ≫
            T.map (DerivedCategory.Q.map r.q ×ₘ DerivedCategory.Q.map r.ε) ∧
        (e r).hom ≫ comparison R T ρ r =
          DerivedCategory.Q.map ((total R).map (r.q ×ₘ 𝟙 _)) ≫
            DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom ∧
        (QuasiIso ((total R).map (𝟙 ((single R).obj r.L) ×ₘ r.ε)) →
          IsIso (comparison R T ρ r)) ∧
        ∀ (s : Pair R) (f : Hom r s),
          (∃ (ht : (total R).map (f.p ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 s.P ×ₘ f.k) ≫
                (total R).map (𝟙 s.P ×ₘ s.ε) =
              (total R).map (𝟙 r.P ×ₘ r.ε) ≫
                (total R).map (f.p ×ₘ (single R).map f.m))
            (hl : (total R).map (f.p ×ₘ f.k) ≫ (total R).map (s.q ×ₘ 𝟙 s.K) =
              (total R).map (r.q ×ₘ 𝟙 r.K) ≫
                (total R).map ((single R).map f.l ×ₘ f.k)),
            coneMap R ((total R).map (f.p ×ₘ 𝟙 r.K) ≫ (total R).map (𝟙 s.P ×ₘ f.k))
                ((total R).map (f.p ×ₘ (single R).map f.m)) ht ≫ (topCone s).hom =
              (topCone r).hom ≫
                (total R).map (coneMap R f.k ((single R).map f.m) f.ε_comm ×ₘ f.p) ∧
            coneMap R ((total R).map (f.p ×ₘ f.k))
                ((total R).map ((single R).map f.l ×ₘ f.k)) hl ≫ (leftCone s).hom =
              (leftCone r).hom ≫
                (total R).map (coneMap R f.p ((single R).map f.l) f.q_comm ×ₘ f.k)) ∧
          DerivedCategory.Q.map ((total R).map (f.p ×ₘ (single R).map f.m)) ≫ (e s).hom =
            (e r).hom ≫ T.map (DerivedCategory.Q.map ((single R).map f.l) ×ₘ
              DerivedCategory.Q.map ((single R).map f.m)) ∧
          T.map (DerivedCategory.Q.map ((single R).map f.l) ×ₘ
              DerivedCategory.Q.map ((single R).map f.m)) ≫ comparison R T ρ s =
            comparison R T ρ r ≫ DerivedCategory.Q.map ((single R).map
              (((tensor R).map f.l).app r.M ≫ ((tensor R).obj s.L).map f.m)) := by
  sorry

end SheafOfModules.KFlatConeComparison
