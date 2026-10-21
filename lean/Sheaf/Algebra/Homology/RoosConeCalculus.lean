/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Strict Roos cone calculus

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-lem-pe-derived-nakayama-first-reduction, Cones paragraph; Stacks Tags 08TC,
07KC, 014E and 011G (blueprint: lem-pe-roos-cone-calculus).

The construction is `CategoryTheory.roosF`, without a second Roos model.
The helper predicates specify its comparisons by their actual component maps.
Natural-number level n means the positive level n+1 of the blueprint.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex

universe a b t u w

namespace CategoryTheory.RoosConeCalculus

section Coordinates
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The product projection in a specified degree. Source: Stacks 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :=
  (Pi.π (fun n : ℕ => N.asFunctor.obj (op n)) n).f q

/-- The coordinate v of the existing Roos fibre. Source: Stacks 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :=
  (roosProj N).f q

/-- The coordinate u of the existing Roos fibre. Source: Stacks 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev ucoord (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q p : ℤ) (h : q - 1 = p) : (roosF.obj N).X q ⟶ (roosP N).X p :=
  (mappingCocone.snd (roosU N)).v q p (by omega)

/-- The target coordinate of a cone. Source: Stacks 014E
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev coneTarget {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q : ℤ) :=
  (mappingCone.snd f).v q q (add_zero q)

/-- The source coordinate of a cone. Source: Stacks 014E
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev coneSource {B : Type a} [Category.{b} B] [Abelian B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) (q p : ℤ) (h : q + 1 = p) :=
  (mappingCone.fst f).1.v q p h

/-- Four projection equations for (b,a,b',a') ↦ (b,b',a,-a').
Source: Stacks 014E and blueprint Cones paragraph
(blueprint: lem-pe-roos-cone-calculus). -/
def ConeFormula {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (e : roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f)) : Prop :=
  ∀ (q : ℤ) (n : ℕ),
    (e.hom.f q ≫ coneTarget (roosF.map f) q ≫ v N' q ≫ π N' q n =
      v (mappingCone f) q ≫ π (mappingCone f) q n ≫ (coneTarget f q).app (op n)) ∧
    (e.hom.f q ≫ coneTarget (roosF.map f) q ≫ ucoord N' q (q - 1) rfl ≫
        π N' (q - 1) n =
      ucoord (mappingCone f) q (q - 1) rfl ≫ π (mappingCone f) (q - 1) n ≫
        (coneTarget f (q - 1)).app (op n)) ∧
    (e.hom.f q ≫ coneSource (roosF.map f) q (q + 1) rfl ≫
        v N (q + 1) ≫ π N (q + 1) n =
      v (mappingCone f) q ≫ π (mappingCone f) q n ≫
        (coneSource f q (q + 1) rfl).app (op n)) ∧
    (e.hom.f q ≫ coneSource (roosF.map f) q (q + 1) rfl ≫
        ucoord N (q + 1) q (by omega) ≫ π N q n =
      -(ucoord (mappingCone f) q (q - 1) rfl ≫ π (mappingCone f) (q - 1) n ≫
        (coneSource f (q - 1) q (by omega)).app (op n)))

/-- The component equations for the signed coherent shift comparison.
Source: Stacks 011G and blueprint Cones paragraph
(blueprint: lem-pe-roos-cone-calculus). -/
def ShiftFormula (cs : (roosF (A := A)).CommShift ℤ) : Prop :=
  ∀ (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) (n : ℕ),
    (((Functor.commShiftIso roosF (self := cs) r).hom.app N).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        v N (q + r) ≫ π N (q + r) n =
      v (N⟦r⟧) q ≫ π (N⟦r⟧) q n ≫
        ((shiftFunctorObjXIso N r q (q + r) rfl).hom).app (op n)) ∧
    (((Functor.commShiftIso roosF (self := cs) r).hom.app N).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        ucoord N (q + r) ((q - 1) + r) (by omega) ≫ π N ((q - 1) + r) n =
      r.negOnePow • (ucoord (N⟦r⟧) q (q - 1) rfl ≫ π (N⟦r⟧) (q - 1) n ≫
        ((shiftFunctorObjXIso N r (q - 1) ((q - 1) + r) rfl).hom).app (op n)))

/-- A cone over the evaluated tower has its already defined strict augmentation.
Source: blueprint Cones paragraph; Stacks 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
noncomputable abbrev augmentation {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (j : Cone N.asFunctor) : j.pt ⟶ roosF.obj N :=
  roosAugment (fun n => j.π.app (op n)) (fun n => by
    exact j.w (homOfLE (Nat.le_succ n)).op)

/-- Compatibility of maps between augmented towers, before taking fibres.
Source: blueprint Cones paragraph (blueprint: lem-pe-roos-cone-calculus). -/
def AugmentedSquare {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (j : Cone N.asFunctor) (j' : Cone N'.asFunctor) (g : j.pt ⟶ j'.pt) : Prop :=
  ∀ n : ℕ, j.π.app (op n) ≫
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n) =
      g ≫ j'.π.app (op n)

/-- Naturality of zero-second-coordinate augmentations.
Source: blueprint Cones paragraph (blueprint: lem-pe-roos-cone-calculus). -/
def AugmentationNaturality (A : Type a) [Category.{b} A] [Abelian A]
    [HasCountableProducts A] : Prop :=
  ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (j : Cone N.asFunctor) (j' : Cone N'.asFunctor) (g : j.pt ⟶ j'.pt),
    AugmentedSquare f j j' g →
      augmentation j ≫ roosF.map f = g ≫ augmentation j'

/-- Naturality and preservation of inclusion and the signed cone boundary.
Source: blueprint Cones paragraph and Stacks 014E
(blueprint: lem-pe-roos-cone-calculus). -/
def ConeCompatibility (cs : (roosF (A := A)).CommShift ℤ)
    (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
      roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f)) : Prop :=
  (∀ {N N' M M' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N ⟶ N') (g : M ⟶ M') (α : N ⟶ M) (β : N' ⟶ M')
    (h : f ≫ β = α ≫ g),
    roosF.map (mappingCone.map f g α β h) ≫ (e g).hom =
      (e f).hom ≫ mappingCone.map (roosF.map f) (roosF.map g)
        (roosF.map α) (roosF.map β)
        (by rw [← Functor.map_comp, ← Functor.map_comp, h])) ∧
  (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
    (roosF.map (mappingCone.inr f) ≫ (e f).hom = mappingCone.inr (roosF.map f)) ∧
    (roosF.map (mappingCone.triangle f).mor₃ ≫
        (Functor.commShiftIso roosF (self := cs) (1 : ℤ)).hom.app N =
      (e f).hom ≫ (mappingCone.triangle (roosF.map f)).mor₃))

/-- Cone augmentations are the induced cone maps of the two strict augmentations.
The hypotheses specify exactly the two levelwise cone coordinates.
Source: blueprint Cones paragraph (blueprint: lem-pe-roos-cone-calculus). -/
def ConeAugmentation
    (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N'),
      roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
    (hnat : AugmentationNaturality A) : Prop :=
  ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (j : Cone N.asFunctor) (j' : Cone N'.asFunctor) (g : j.pt ⟶ j'.pt)
    (h : AugmentedSquare f j j' g)
    (jc : Cone (mappingCone f).asFunctor) (c : mappingCone g ⟶ jc.pt),
    (∀ (q : ℤ) (n : ℕ),
      ((c ≫ jc.π.app (op n)).f q ≫ (coneTarget f q).app (op n) =
        coneTarget g q ≫ (j'.π.app (op n)).f q) ∧
      ((c ≫ jc.π.app (op n)).f q ≫ (coneSource f q (q + 1) rfl).app (op n) =
        coneSource g q (q + 1) rfl ≫ (j.π.app (op n)).f (q + 1))) →
    c ≫ augmentation jc ≫ (e f).hom =
      mappingCone.map g (roosF.map f) (augmentation j) (augmentation j')
        (hnat f j j' g h).symm

/-- Induced shifted augmentations commute with the coherent comparison.
Source: blueprint Cones paragraph and Stacks 011G
(blueprint: lem-pe-roos-cone-calculus). -/
def ShiftAugmentation (cs : (roosF (A := A)).CommShift ℤ) : Prop :=
  ∀ (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : Cone N.asFunctor) (r : ℤ)
    (js : Cone (N⟦r⟧).asFunctor) (c : js.pt ⟶ j.pt⟦r⟧),
    (∀ (q : ℤ) (n : ℕ),
      (js.π.app (op n)).f q ≫
          ((shiftFunctorObjXIso N r q (q + r) rfl).hom).app (op n) =
        c.f q ≫ (shiftFunctorObjXIso j.pt r q (q + r) rfl).hom ≫
          (j.π.app (op n)).f (q + r)) →
    augmentation js ≫ (Functor.commShiftIso roosF (self := cs) r).hom.app N =
      c ≫ (augmentation j)⟦r⟧'

/-- The actual differential, diagonal maps and zero-second-coordinate augmentation.
Source: blueprint Cones paragraph; Stacks 014E, 011G and 08TC
(blueprint: lem-pe-roos-cone-calculus). -/
def CoordinateCalculus (A : Type a) [Category.{b} A] [Abelian A]
    [HasCountableProducts A] : Prop :=
  (∀ (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ),
    ((roosF.obj N).d q (q + 1) ≫ v N (q + 1) =
      v N q ≫ (roosP N).d q (q + 1)) ∧
    ((roosF.obj N).d q (q + 1) ≫ ucoord N (q + 1) q (by omega) =
      -(ucoord N q (q - 1) rfl ≫ (roosP N).d (q - 1) q) -
        v N q ≫ (roosU N).f q)) ∧
  (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') (q : ℤ),
    ((roosF.map f).f q ≫ v N' q = v N q ≫ (roosPmap f).f q) ∧
    ((roosF.map f).f q ≫ ucoord N' q (q - 1) rfl =
      ucoord N q (q - 1) rfl ≫ (roosPmap f).f (q - 1))) ∧
  (∀ {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (j : Cone N.asFunctor) (q : ℤ),
    ((augmentation j).f q ≫ v N q = (Pi.lift (fun n => j.π.app (op n))).f q) ∧
    ((augmentation j).f q ≫ ucoord N q (q - 1) rfl = 0))

/-- The localized triangle uses the actual localized termwise product projections.
It is a Roos triangle for the tower, with its product identified by those projections.
Source: Stacks 08TC and 07KC (blueprint: lem-pe-roos-cone-calculus). -/
def DerivedRoos [HasDerivedCategory.{w} A]
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Prop :=
  Nonempty (IsLimit (DerivedCategory.Q.mapCone
    (limit.cone (Discrete.functor (fun n : ℕ => N.asFunctor.obj (op n)))))) ∧
  DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle (roosU N)) ∈
    distTriang (DerivedCategory A) ∧
  ∀ (_h : HasProduct (fun n : ℕ => DerivedCategory.Q.obj (N.asFunctor.obj (op n)))),
    IsDerivedLimit (K := fun n : ℕ => DerivedCategory.Q.obj (N.asFunctor.obj (op n)))
      (fun n : ℕ => DerivedCategory.Q.map
        (N.asFunctor.map (homOfLE (Nat.le_succ n)).op))
      (DerivedCategory.Q.obj (roosF.obj N))

end Coordinates

/-- The strict Roos fibre is additive, preserves levelwise quasi-isomorphisms, computes
Roos derived limits, and has the specified natural cone and coherent shift comparisons,
including compatibility with the actual zero-second-coordinate augmentations.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-lem-pe-derived-nakayama-first-reduction, Cones paragraph; Stacks 08TC, 07KC,
014E and 011G (blueprint: lem-pe-roos-cone-calculus).

Proof plan:
1. Use the product universal property (def-weil-category-product) to define the transition
   shift and verify it commutes with d and strict product maps (def-weil-inverse-system).
   The existing roosF of def-weil-strict-roos-model is Cone(1-T)[-1]; expanding its
   coordinates gives (dv,-du-(1-T)v). Projectionwise verification gives additivity,
   the diagonal map formula and naturality of the zero-second-coordinate augmentation.
2. By det-pe-products-derived, the product of levelwise quasi-isomorphisms is a
   quasi-isomorphism. Apply lem-pe-roos-coordinates-quasi-iso with endomorphism -(1-T)
   to get the same result for the diagonal Roos map; no boundedness is required.
3. The actual localized product cone is limiting by det-pe-products-derived. Thus Q(1-T)
   is the derived transition endomorphism. Inverse rotation of the cone triangle using
   def-weil-triangulated-category gives the localized mapping-cocone triangle, with
   projection v and last map w↦(0,w). This is def-weil-derived-limit's Roos triangle;
   transport along the unique projection-preserving product isomorphism.
4. For epsilon=(-1)^r the shift comparison (v,u)↦(v,epsilon u) commutes with d, is
   natural, and is involutive in these coordinates. The identities epsilon(0)=1 and
   epsilon(r+s)=epsilon(r)epsilon(s) give coherent shifts. This is the existing signed
   comparison of lem-weil-roos-comm-shift transported to the strict-tower presentation.
5. Expand both double cones: the source differential on (b,a,b',a') is
   (db+Fa,-da,-db'-Fa'-(1-T')b,da'-(1-T)a). The permutation with sign
   (b,a,b',a')↦(b,b',a,-a') intertwines it with the target differential, and has
   inverse (b,b',a,c)↦(b,a,b',-c). The four projection equations uniquely specify it.
6. Every strict square acts by the four diagonal product maps, which commute with
   this permutation and sign. The inclusion sends (b,b') to (b,0,b',0).
   The boundary -p followed by the shift comparison is (-a,a'), also -p after
   the cone comparison. These establish naturality, inclusion and boundary identities.
7. For a compatible family j, (1-T)J=0 after every product projection. Therefore
   (J,0) is the existing chain map roosAugment; diagonal product maps give naturality.
8. Shifts multiply its zero coordinate by a sign and preserve it. The induced cone
   augmentation ((J'm',Jm),(0,0)) goes to ((J'm',0),(Jm,0)), the cone map of the
   two augmentations. Checking the two levelwise coordinates proves the stated
   conditional compatibility for every induced cone and shifted augmentation. -/
theorem roos_cone_calculus
    (X : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)] :
    (roosF (A := ringedSiteModules.{max u (t + 1)} R)).Additive ∧
    CoordinateCalculus (ringedSiteModules.{max u (t + 1)} R) ∧
    (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
      (f : N ⟶ N'),
      (∀ n : ℕ, QuasiIso
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))) →
      QuasiIso (roosF.map f)) ∧
    (∀ N : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ,
      DerivedRoos N) ∧
    ∃ (cs : (roosF (A := ringedSiteModules.{max u (t + 1)} R)).CommShift ℤ)
      (e : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
        (f : N ⟶ N'), roosF.obj (mappingCone f) ≅ mappingCone (roosF.map f))
      (hnat : AugmentationNaturality (ringedSiteModules.{max u (t + 1)} R)),
      ShiftFormula cs ∧
      (∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R) ℤ}
        (f : N ⟶ N'), ConeFormula f (e f)) ∧
      ConeCompatibility cs e ∧ ConeAugmentation e hnat ∧ ShiftAugmentation cs := by
  sorry

end CategoryTheory.RoosConeCalculus
