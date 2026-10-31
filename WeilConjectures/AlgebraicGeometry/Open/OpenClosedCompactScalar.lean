/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectImageScalarComposition
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientDualizingOpenTensor
import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence

/-! # The compact-support coefficient square for two factorizations

Source: the finite dualizing proof, paragraphs 2--3
(blueprint: open-closed-compact-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  upperStar lowerStar openImmersionLowerShriek

private theorem scalar_identity_direct
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (M : DerivedCategoryModule A T) :
    (scalarMate φ (𝟙 T)).app M ≫
        (rightDerivedLowerStarIdIso B T).hom.app ((scalarExtension φ T).obj M) =
      (scalarExtension φ T).map ((rightDerivedLowerStarIdIso A T).hom.app M) := by
  have h := scalarMate_directImage_identity φ T M
  rw [derived_identity_comparison, derived_identity_comparison] at h
  exact h

private theorem special_open_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategoryModule A V) :
    (scalarExtension φ X).map
        ((rightDerivedLowerStarIdIso A X).hom.app ((derivedExtension j).obj M)) ≫
        (ExceptionalCoefficients.openIso φ j).hom.app M =
      (compactScalarMap φ (Compactification.ofIsOpenImmersion j)).app M ≫
        (rightDerivedLowerStarIdIso B X).hom.app
          ((derivedExtension (A := B) j).obj ((scalarExtension φ V).obj M)) := by
  have hn := (rightDerivedLowerStarIdIso B X).hom.naturality
    ((ExceptionalCoefficients.openIso φ j).hom.app M)
  dsimp only [Functor.id_map, Functor.comp_obj] at hn
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    Compactification.ofIsOpenImmersion]
  rw [Category.assoc, hn, ← Category.assoc, scalar_identity_direct]

private theorem special_proper_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V P : Scheme.{u}} (i : V ⟶ P) [IsProper i]
    (M : DerivedCategoryModule A V) :
    (scalarExtension φ P).map
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) i).map
          ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) V).hom.app M)) ≫
        (scalarMate φ i).app M =
      (compactScalarMap φ (Compactification.ofIsProper i)).app M ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} B) i).map
          ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) V).hom.app
            ((scalarExtension φ V).obj M)) := by
  have hn := (scalarMate φ i).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) V).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  have ho := ProEtale.OpenScalarSite.etale_scalar_id φ V M
  rw [← compactScalarOpen_eq] at ho
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    Compactification.ofIsProper, rightDerivedLowerStar]
  rw [Category.assoc, ← Functor.map_comp, ho]
  exact hn

private theorem inverse_scalar_square
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {X Y : C} {X' Y' : D} (a : X ≅ Y) (b : X' ≅ Y')
    (c : Q.obj X ⟶ X') (d : Q.obj Y ⟶ Y')
    (h : Q.map a.hom ≫ d = c ≫ b.hom) :
    Q.map a.inv ≫ c = d ≫ b.inv := by
  apply (cancel_epi (Q.map a.hom)).1
  rw [← Q.map_comp_assoc, a.hom_inv_id, Q.map_id, Category.id_comp]
  rw [← Category.assoc, h, Category.assoc, b.hom_inv_id, Category.comp_id]

private theorem chosen_special_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V X : Scheme.{u}} [IsNoetherian V] [IsNoetherian X]
    (j : V ⟶ X) [QuasiCompact j] [HasCompactification j] (c : Compactification j)
    (M : _root_.DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ V).obj M.obj)) :
    (scalarExtension φ X).map ((rightDerivedLowerShriekIso A c).inv.app M.obj) ≫
        (compactScalarMap φ c).app M.obj =
      (compactScalarChosenMap φ j).app M.obj ≫
        (rightDerivedLowerShriekIso B c).inv.app ((scalarExtension φ V).obj M.obj) := by
  exact inverse_scalar_square (scalarExtension φ X)
    ((rightDerivedLowerShriekIso A c).app M.obj)
    ((rightDerivedLowerShriekIso B c).app ((scalarExtension φ V).obj M.obj))
    _ _ (compactScalar_compactification_comparison φ c
      (HasCompactification.compactification j) M hQ)

private def open_normalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification j] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} R) j ≅ derivedExtension (A := R) j :=
  (rightDerivedLowerShriekIso R (Compactification.ofIsOpenImmersion j)).symm ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarIdIso R X) ≪≫ Functor.rightUnitor _

private def proper_normalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {V P : Scheme.{u}} (i : V ⟶ P) [IsProper i] [HasCompactification i] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} R) i ≅
      rightDerivedLowerStar (ModuleCat.{u + 1} R) i :=
  (rightDerivedLowerShriekIso R (Compactification.ofIsProper i)).symm ≪≫
    Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} R) V) _ ≪≫
    Functor.leftUnitor _

private theorem chosen_open_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V X : Scheme.{u}} [IsNoetherian V] [IsNoetherian X]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [HasCompactification j]
    (M : _root_.DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ V).obj M.obj)) :
    (scalarExtension φ X).map ((open_normalization A j).hom.app M.obj) ≫
        (ExceptionalCoefficients.openIso φ j).hom.app M.obj =
      (compactScalarChosenMap φ j).app M.obj ≫
        (open_normalization B j).hom.app ((scalarExtension φ V).obj M.obj) := by
  change (scalarExtension φ X).map
      ((rightDerivedLowerShriekIso A (Compactification.ofIsOpenImmersion j)).inv.app M.obj ≫
        (rightDerivedLowerStarIdIso A X).hom.app ((derivedExtension j).obj M.obj) ≫
        𝟙 _) ≫
      (ExceptionalCoefficients.openIso φ j).hom.app M.obj =
    (compactScalarChosenMap φ j).app M.obj ≫
      (rightDerivedLowerShriekIso B (Compactification.ofIsOpenImmersion j)).inv.app
        ((scalarExtension φ V).obj M.obj) ≫
      (rightDerivedLowerStarIdIso B X).hom.app
        ((derivedExtension (A := B) j).obj ((scalarExtension φ V).obj M.obj)) ≫ 𝟙 _
  simp only [Category.comp_id]
  rw [Functor.map_comp, Category.assoc, special_open_scalar,
    ← Category.assoc, chosen_special_scalar φ j _ M hQ, Category.assoc]

private theorem chosen_proper_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V P : Scheme.{u}} [IsNoetherian V] [IsNoetherian P]
    (i : V ⟶ P) [IsProper i] [HasCompactification i]
    (M : _root_.DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ V).obj M.obj)) :
    (scalarExtension φ P).map ((proper_normalization A i).hom.app M.obj) ≫
        (scalarMate φ i).app M.obj =
      (compactScalarChosenMap φ i).app M.obj ≫
        (proper_normalization B i).hom.app ((scalarExtension φ V).obj M.obj) := by
  change (scalarExtension φ P).map
      ((rightDerivedLowerShriekIso A (Compactification.ofIsProper i)).inv.app M.obj ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) i).map
          ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) V).hom.app
            M.obj) ≫ 𝟙 _) ≫ (scalarMate φ i).app M.obj =
    (compactScalarChosenMap φ i).app M.obj ≫
      (rightDerivedLowerShriekIso B (Compactification.ofIsProper i)).inv.app
        ((scalarExtension φ V).obj M.obj) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) i).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) V).hom.app
          ((scalarExtension φ V).obj M.obj)) ≫ 𝟙 _
  simp only [Category.comp_id]
  rw [Functor.map_comp, Category.assoc, special_proper_scalar,
    ← Category.assoc, chosen_special_scalar φ i _ M hQ, Category.assoc]

private theorem normalized_composition_scalar
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (Q₀ : C ⥤ C') (Q₁ : D ⥤ D') (Q₂ : E ⥤ E')
    (F F₀ : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (F' F₀' : C' ⥤ D') (G' : D' ⥤ E') (H' : C' ⥤ E')
    (n : F ≅ F₀) (n' : F' ≅ F₀') (t : F ⋙ G ≅ H) (t' : F' ⋙ G' ≅ H')
    (cF : F ⋙ Q₁ ⟶ Q₀ ⋙ F') (cG : G ⋙ Q₂ ⟶ Q₁ ⋙ G')
    (cH : H ⋙ Q₂ ⟶ Q₀ ⋙ H') (c₀ : F₀ ⋙ Q₁ ⟶ Q₀ ⋙ F₀') (M : C)
    (hn : Q₁.map (n.hom.app M) ≫ c₀.app M = cF.app M ≫ n'.hom.app (Q₀.obj M))
    (ht : Q₂.map (t.hom.app M) ≫ cH.app M =
      cG.app (F.obj M) ≫ G'.map (cF.app M) ≫ t'.hom.app (Q₀.obj M)) :
    Q₂.map ((Functor.isoWhiskerRight n.symm G ≪≫ t).hom.app M) ≫ cH.app M =
      cG.app (F₀.obj M) ≫ G'.map (c₀.app M) ≫
        (Functor.isoWhiskerRight n'.symm G' ≪≫ t').hom.app (Q₀.obj M) := by
  have hi := inverse_scalar_square Q₁ (n.app M) (n'.app (Q₀.obj M))
    (cF.app M) (c₀.app M) hn
  simp only [Iso.app_inv] at hi
  have hnat := cG.naturality (n.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnat
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [ht, reassoc_of% hnat, ← G'.map_comp_assoc, hi, G'.map_comp, Category.assoc]

private def shriek_congr
    (R : Type (u + 1)) [CommRing R]
    {V S : Scheme.{u}} (a b : V ⟶ S) [HasCompactification a] [HasCompactification b]
    (h : a = b) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} R) a ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} R) b := by
  subst b
  exact Iso.refl _

private theorem shriek_congr_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V S : Scheme.{u}} (a b : V ⟶ S)
    [HasCompactification a] [HasCompactification b] (h : a = b)
    (M : DerivedCategoryModule A V) :
    (scalarExtension φ S).map ((shriek_congr A a b h).hom.app M) ≫
        (compactScalarChosenMap φ b).app M =
      (compactScalarChosenMap φ a).app M ≫
        (shriek_congr B a b h).hom.app ((scalarExtension φ V).obj M) := by
  subst b
  dsimp only [shriek_congr, Iso.refl_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

attribute [local irreducible] unboundedEtaleLowerShriekCompIso
  open_normalization proper_normalization shriek_congr

/-- The left-adjoint coefficient square for an open and a closed factorization.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 3, counit sentence
(blueprint: open-closed-compact-scalar-coherence).

Proof: compare the chosen compactification of j with (j,identity) and that of i
with (identity,i). Remove the identity proper or open functor, respectively.
Compose each normalization with the unbounded compact-support compositor for
j followed by f and i followed by p. The equality j f = i p then gives tA and tB.
The finite-Tor interval of W is preserved by exact open restriction and scalar
extension. Hence the input and its scalar extension are bounded below. Apply
etaleCompactScalarComposition to the two composites on that input and
etaleCompactScalarCoherence to the changes of compactification. The open
normalization is openIso, because its scalar comparison is the same exact
extension-by-zero comparison. The proper normalization is scalarMate, because
its identity-open comparison is the unit comparison. Pasting these four squares
and cancelling the common structural compactification comparison gives the
stated equation. No assertion about exceptional coefficient maps is used. The
identity and empty-open cases use the same identity/zero normalizations. -/
theorem openClosedCompactScalar_coherence
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X V P S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian V] [IsNoetherian P] [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (j : V ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : V ⟶ P) [IsClosedImmersion i]
    (p : P ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] (h : j ≫ f = i ≫ p)
    (W : DerivedCategoryModule A X)
    (hW : DerivedCategory.isBoundedConstructible A X W ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b W) :
    ∃ (tA : derivedExtension (A := A) j ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
        rightDerivedLowerStar (ModuleCat.{u + 1} A) i ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A) p)
      (tB : derivedExtension (A := B) j ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} B) f ≅
        rightDerivedLowerStar (ModuleCat.{u + 1} B) i ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} B) p),
      let L := (derivedRestriction (A := A) j).obj W
      (scalarExtension φ S).map (tA.hom.app L) ≫
          (compactScalarChosenMap φ p).app
            ((rightDerivedLowerStar (ModuleCat.{u + 1} A) i).obj L) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} B) p).map
            ((scalarMate φ i).app L) =
        (compactScalarChosenMap φ f).app ((derivedExtension (A := A) j).obj L) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
            ((ExceptionalCoefficients.openIso φ j).hom.app L) ≫
          tB.hom.app ((scalarExtension φ V).obj L) := by
  let : HasCompactification j := (Compactification.ofIsOpenImmersion j).hasCompactification
  let : HasCompactification (j ≫ f) := HasCompactification.comp_of_isOpenImmersion f j
  let : HasCompactification (i ≫ p) := HasCompactification.of_eq h
  let L := (derivedRestriction (A := A) j).obj W
  have hL : DerivedCategory.isBoundedConstructible A V L :=
    finiteValueBoundedConstructible
      ((sourceBoundedConstructible hW.1).mapDerivedCategory_upperStar j)
  obtain ⟨a, b, hab, ht⟩ := hW.2
  have htL : DerivedCategory.hasTorAmplitudeIn A V a b L :=
    exactFlatFunctor_tor (upperStar (ModuleCat.{u + 1} A) j)
      (fun _ hflat ↦ Functor.PreservesFlat.flat_obj hflat) ht
  have hQL := scalarBoundedConstructibleTor φ V L hL a b hab htL
  let M : _root_.DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨L, (sourceBoundedConstructible hL).1.1⟩
  have hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ V).obj L) :=
    (sourceBoundedConstructible hQL.1).1.1
  have hQM : ∃ N : _root_.DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)),
      N.obj = (scalarExtension φ V).obj M.obj := ⟨⟨_, hQ⟩, rfl⟩
  let oA := Functor.isoWhiskerRight (open_normalization A j).symm
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
      unboundedEtaleLowerShriekCompIso A j f
  let oB := Functor.isoWhiskerRight (open_normalization B j).symm
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f) ≪≫
      unboundedEtaleLowerShriekCompIso B j f
  let cA := Functor.isoWhiskerRight (proper_normalization A i).symm
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p) ≪≫
      unboundedEtaleLowerShriekCompIso A i p
  let cB := Functor.isoWhiskerRight (proper_normalization B i).symm
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) p) ≪≫
      unboundedEtaleLowerShriekCompIso B i p
  let eA := shriek_congr A (j ≫ f) (i ≫ p) h
  let eB := shriek_congr B (j ≫ f) (i ≫ p) h
  have hno := chosen_open_scalar φ j M hQ
  have hnp := chosen_proper_scalar φ i M hQ
  have hco := etaleCompactScalarComposition φ j f M hQM
  have hcp := etaleCompactScalarComposition φ i p M hQM
  have ho := normalized_composition_scalar
    (scalarExtension φ V) (scalarExtension φ X) (scalarExtension φ S)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) j) (derivedExtension (A := A) j)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (j ≫ f))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) j) (derivedExtension (A := B) j)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (j ≫ f))
    (open_normalization A j) (open_normalization B j)
    (unboundedEtaleLowerShriekCompIso A j f) (unboundedEtaleLowerShriekCompIso B j f)
    (compactScalarChosenMap φ j) (compactScalarChosenMap φ f)
    (compactScalarChosenMap φ (j ≫ f)) (ExceptionalCoefficients.openIso φ j).hom M.obj
    hno hco
  have hc := normalized_composition_scalar
    (scalarExtension φ V) (scalarExtension φ P) (scalarExtension φ S)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) i)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) i)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (i ≫ p))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) i)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) i)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) p)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (i ≫ p))
    (proper_normalization A i) (proper_normalization B i)
    (unboundedEtaleLowerShriekCompIso A i p) (unboundedEtaleLowerShriekCompIso B i p)
    (compactScalarChosenMap φ i) (compactScalarChosenMap φ p)
    (compactScalarChosenMap φ (i ≫ p)) (scalarMate φ i) M.obj
    hnp hcp
  have hi := inverse_scalar_square (scalarExtension φ S)
    (cA.app M.obj) (cB.app ((scalarExtension φ V).obj M.obj))
    ((compactScalarChosenMap φ p).app
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) i).obj M.obj) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) p).map ((scalarMate φ i).app M.obj))
    ((compactScalarChosenMap φ (i ≫ p)).app M.obj)
    (by simpa only [Iso.app_hom, Category.assoc] using hc)
  simp only [Iso.app_inv] at hi
  have he := shriek_congr_scalar φ (j ≫ f) (i ≫ p) h L
  refine ⟨oA ≪≫ eA ≪≫ cA.symm, oB ≪≫ eB ≪≫ cB.symm, ?_⟩
  dsimp only
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [hi, reassoc_of% he, reassoc_of% ho]

end AlgebraicGeometry.Etale
