/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.OrdinaryScalarSiteComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finite coefficient compact-support comparison

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md` (det-sp-reduction-exceptional), Charts and Locality;
Stacks 0GL6, 0F7I, 0F7J.
(blueprint: lem-sp-et-proet-coefficient-compatibility).

All constructions use ordinary constant-coefficient module sheaves on the small sites.
The field is finite or algebraically closed, including characteristic zero. All theorem
statements below concern smooth maps of a specified pure relative dimension. Scalar extension
is the published left adjoint to actual exact scalar restriction. Proper coefficient
maps are its geometric counit mates; open and etale sum comparisons are the unique
comparisons of the specified composite adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility
open OrdinaryScalarSite

/-- The recorded ordinary etale compact-support candidate.
Source: Stacks 0F7I (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev et (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c

/-- The recorded ordinary pro-etale compact-support candidate.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Charts (blueprint:
lem-sp-et-proet-coefficient-compatibility). -/
abbrev pro (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c

/-- Exact comparison pullback, localized termwise.
Source: Stacks 099R (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev nu (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory

/-- The open scalar comparison fixed by its actual scalar and open adjunction units.
Source: Stacks 03S2, 06YY (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def etOpen {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalar Z.smallEtaleTopology a ≅
      scalar X.smallEtaleTopology a ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((Adjunction.mapDerivedCategoryAdjunction
      (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).comp
        (CoefficientScalarRepresentatives.adjunction Z.smallEtaleTopology a)).ofNatIsoRight
    (Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf a j))
    |>.leftAdjointUniq
      ((CoefficientScalarRepresentatives.adjunction X.smallEtaleTopology a).comp
        (Adjunction.mapDerivedCategoryAdjunction
          (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)))

/-- The same unit-normalized open scalar comparison on the pro-etale site.
Source: Stacks 03S2, 06YY (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def proOpen {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalar (Scheme.ProEt.topology Z) a ≅
      scalar (Scheme.ProEt.topology X) a ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((Adjunction.mapDerivedCategoryAdjunction
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).comp
        (CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology Z) a)).ofNatIsoRight
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso a j))
    |>.leftAdjointUniq
      ((CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology X) a).comp
        (Adjunction.mapDerivedCategoryAdjunction
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)))

/-- Proper counit mate followed by extension by zero's tensor identification: beta.
Source: Stacks 0GL6 (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def beta {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    et A c ⋙ scalar Y.smallEtaleTopology a ⟶ scalar X.smallEtaleTopology a ⋙ et B c :=
  Functor.whiskerLeft
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
      (etaleGamma a c.g) ≫
    Functor.whiskerRight (etOpen a c.i).hom
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor

/-- The intrinsic pro-etale coefficient map b, using the geometric B-linear counit mate.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Charts (blueprint:
lem-sp-et-proet-coefficient-compatibility). -/
def b {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    pro A c ⋙ scalar (Scheme.ProEt.topology Y) a ⟶
      scalar (Scheme.ProEt.topology X) a ⋙ pro B c :=
  Functor.whiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
      (proEtaleGamma a c.g) ≫
    Functor.whiskerRight (proOpen a c.i).hom
      (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor

/-- The specified compact-support site comparison c: proper counit mate, then open mate.
It is defined before asserting that it is invertible.
Source: Stacks 099R, 09AF (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def site (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    et R c ⋙ nu R Y ⟶ nu R X ⋙ pro R c :=
  Functor.whiskerLeft
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory
      (ambientEtaleProEtaleDirectImageComparison R c.g) ≫
    Functor.whiskerRight
      (Functor.mapDerivedCategorySquareIso
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) c.i)).hom
      (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor

/-- The summandwise derived tensor identification, specified by the exact sum adjunction.
On K-flat representatives it sends each sheet tensor to that same sheet tensor.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Charts, integral summation
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def sumScalar {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Y : Scheme.{u}} (e : X ⟶ Y) [Etale e] [IsSeparated e] :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        scalar Y.smallEtaleTopology a ≅
      scalar X.smallEtaleTopology a ⋙
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory :=
  ((Adjunction.mapDerivedCategoryAdjunction
      (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)).comp
        (CoefficientScalarRepresentatives.adjunction Y.smallEtaleTopology a)).ofNatIsoRight
    (Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf a e))
    |>.leftAdjointUniq
      ((CoefficientScalarRepresentatives.adjunction X.smallEtaleTopology a).comp
        (Adjunction.mapDerivedCategoryAdjunction
          (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) e inferInstance)))

/-- The recorded bounded-below compact-support functor.
Source: Stacks 0F7I (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev plusEt (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c

/-- The recorded compatibility of the bounded-below candidate with the ambient candidate.
Source: Stacks 0F7I (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev plusCompatibility (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} R) c

/-- The ambient candidate's output as a bounded-below object, with the identical
underlying object. Its bound is transported by the recorded compatibility isomorphism.
Source: Stacks 0F7I (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def plusOut (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  ⟨(et R c).obj L.obj, DerivedCategory.TStructure.t.plus.prop_of_iso
    ((plusCompatibility R c).app L) ((plusEt R c).obj L).property⟩

/-- The node's canonical D+ common-refinement map, included in the ambient category
by the recorded PlusιIso. No unbounded comparison is substituted for this map.
Source: Stacks 0F7I (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev phi (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :=
  (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso R c d).app L

/-- The recorded D+ composition, expressed at specified compactifications by its
recorded D+ common-refinement comparisons. The central map is PlusCompIso itself.
Source: Stacks 0F7J (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def alphaPlus (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    plusEt R c ⋙ plusEt R d ≅ plusEt R e :=
  letI : HasCompactification f := ⟨⟨c⟩⟩
  letI : HasCompactification g := ⟨⟨d⟩⟩
  letI : HasCompactification (f ≫ g) := ⟨⟨e⟩⟩
  Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusIso R c
        (HasCompactification.compactification f)) _ ≪≫
    Functor.isoWhiskerLeft _
      (Etale.rightDerivedLowerShriekOfCompactificationPlusIso R d
        (HasCompactification.compactification g)) ≪≫
    Etale.rightDerivedLowerShriekPlusCompIso R f g ≪≫
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso R
      (HasCompactification.compactification (f ≫ g)) e

/-- Include precisely the D+ composition through the recorded compatibility maps.
Source: Stacks 0F7J (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def alpha (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (et R d).obj ((et R c).obj L.obj) ≅ (et R e).obj L.obj :=
  (et R d).mapIso ((plusCompatibility R c).app L).symm ≪≫
    ((plusCompatibility R d).app ((plusEt R c).obj L)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso ((alphaPlus R c d e).app L) ≪≫
    (plusCompatibility R e).app L

/-- Transport the recorded D+ refinement through the specified site comparison.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Locality (blueprint:
lem-sp-et-proet-coefficient-compatibility). -/
def proPhi (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    [IsIso ((site R c).app L.obj)] :
    (pro R c).obj ((nu R X).obj L.obj) ⟶ (pro R d).obj ((nu R X).obj L.obj) :=
  inv ((site R c).app L.obj) ≫ (nu R Y).map (phi R c d L).hom ≫
    (site R d).app L.obj

/-- Transport the recorded D+ composition through all three site components.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Locality (blueprint:
lem-sp-et-proet-coefficient-compatibility). -/
def proAlpha (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    [IsIso ((site R c).app L.obj)] [IsIso ((site R d).app ((et R c).obj L.obj))] :
    (pro R d).obj ((pro R c).obj ((nu R X).obj L.obj)) ⟶
      (pro R e).obj ((nu R X).obj L.obj) :=
  (pro R d).map (inv ((site R c).app L.obj)) ≫
    inv ((site R d).app ((et R c).obj L.obj)) ≫
      (nu R Z).map (alpha R c d e L).hom ≫ (site R e).app L.obj

/-- Bounded constructibility and the uniform degree-zero-sheaf tensor bound in the node.
This abbreviates the recorded predicates; no flatness condition is imposed on B/A.
Source: finite coefficient paragraph (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev Input (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule R X) : Prop :=
  Etale.DerivedCategory.isBoundedConstructible R X L ∧
    ∃ m n : ℤ, m ≤ n ∧ Etale.DerivedCategory.hasTorAmplitudeIn R X m n L

/-- The recorded D+ identity comparison, at the identity compactification and
included into the ambient category. Its middle comparison is PlusId, not a new unit map.
Source: Stacks 0F7J (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def identityEt (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (et R (Compactification.ofIsProper (𝟙 T))).obj L.obj ≅ L.obj :=
  ((plusCompatibility R (Compactification.ofIsProper (𝟙 T))).app L).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso R
        (Compactification.ofIsProper (𝟙 T))
        (HasCompactification.compactification (𝟙 T)) ≪≫
          Etale.rightDerivedLowerShriekPlusId R T).app L)

section Setting
variable (ℓ : ℕ) [hℓprime : Fact ℓ.Prime] (k : Type u) [Field k]
  (hk : Finite k ∨ IsAlgClosed k) (hchar : ringChar k ≠ ℓ)
  {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
  (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
  (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
  (a : A →+* B)
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [hXft : LocallyOfFiniteType (X ↘ Spec (.of k))]
  [hXqc : QuasiCompact (X ↘ Spec (.of k))]
  [hXs : IsSeparated (X ↘ Spec (.of k))]
  [hYft : LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [hYqc : QuasiCompact (Y ↘ Spec (.of k))]
  [hYs : IsSeparated (Y ↘ Spec (.of k))]
  {f : X ⟶ Y} [hfov : f.IsOver (Spec (.of k))]
  [hfs : IsSeparated f] [hfft : LocallyOfFiniteType f] [hfqc : QuasiCompact f]
  (dim : ℕ) [hsmooth : SmoothOfRelativeDimension dim f]
include hℓprime hk hchar dim hsmooth hA hB hXft hXqc hXs hYft hYqc hYs hfov hfs hfft hfqc

/-- The site/coefficient square for the actual proper/open coefficient maps, including
invertibility on the specified input class.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Charts (blueprint:
lem-sp-et-proet-coefficient-compatibility).

Proof: finite type over k implies Noetherianity. Resolve L by a bounded flat
constructible complex. Apply the proper scalar-mate square at j!L and paste the
open scalar/site square. Naturality moves the proper coefficient arrow past the
open comparison, and the proper counit normalization identifies the composite
with site. The etale coefficient arrow is invertible by the compact scalar
coherence theorem; the proper/open site maps are invertible on these bounded
inputs. Cancel the site and delta isomorphisms to obtain invertibility of the
specified intrinsic b. Every construction is natural on the ambient derived category. -/
theorem etaleProEtaleCoefficientCompatibilitySmooth
    (c : Compactification f) (L : Etale.DerivedCategoryModule A X) (hL : Input A X L) :
    IsIso ((beta a c).app L) ∧
    IsIso ((b a c).app ((nu A X).obj L)) ∧
    IsIso ((site A c).app L) ∧
    IsIso ((site B c).app ((scalar X.smallEtaleTopology a).obj L)) ∧
    ((scalar (Scheme.ProEt.topology Y) a).map ((site A c).app L) ≫
        (b a c).app ((nu A X).obj L) ≫
        (pro B c).map ((delta a X).hom.app L) =
      (delta a Y).hom.app ((et A c).obj L) ≫
        (nu B Y).map ((beta a c).app L) ≫
        (site B c).app ((scalar X.smallEtaleTopology a).obj L)) := by
  sorry

/-- Coefficients commute with the recorded D+ refinement and its pro-etale transport.
Scalar boundedness is part of the conclusion; its proof only packages the same object
as an object of D+. No coefficient flatness or additional input bound is assumed.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Locality (blueprint:
lem-sp-et-proet-coefficient-compatibility).

Proof: finite compact-support domains gives the scalar lower bound. Apply etale
scalar coherence and identify its restriction with the recorded D+ map by the
unbounded/D+ comparison theorem. Substitute the site square at c and d, cancel
site inverses and commute delta by naturality. For an arbitrary common refinement,
use the dependency's PlusIso_eq_refinementIso and PlusIso_trans, not a new comparison. -/
theorem finiteCoefficientCompactSupport_refinement
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : Input A X L.obj) :
    DerivedCategory.TStructure.t.plus ((scalar X.smallEtaleTopology a).obj L.obj) ∧
    ∀ hLB : DerivedCategory.TStructure.t.plus ((scalar X.smallEtaleTopology a).obj L.obj),
    let LB : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
      ⟨(scalar X.smallEtaleTopology a).obj L.obj, hLB⟩
    ((scalar Y.smallEtaleTopology a).map (phi A c d L).hom ≫
        (beta a d).app L.obj =
      (beta a c).app L.obj ≫ (phi B c d LB).hom) ∧
    (∀ (hc : IsIso ((site A c).app L.obj))
        (hbc : IsIso ((site B c).app LB.obj)),
      IsIso (@proPhi A _ _ X Y f _ c d L hc) ∧
      IsIso (@proPhi B _ _ X Y f _ c d LB hbc) ∧
      ((scalar (Scheme.ProEt.topology Y) a).map (@proPhi A _ _ X Y f _ c d L hc) ≫
          (b a d).app ((nu A X).obj L.obj) ≫
          (pro B d).map ((delta a X).hom.app L.obj) =
        (b a c).app ((nu A X).obj L.obj) ≫
          (pro B c).map ((delta a X).hom.app L.obj) ≫
          @proPhi B _ _ X Y f _ c d LB hbc)) := by
  sorry

/-- Coefficients commute with PlusCompIso, expressed at the specified compactifications,
and with its pro-etale transport. The scalar and intermediate site bounds are conclusions.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Locality (blueprint:
lem-sp-et-proet-coefficient-compatibility).

Proof: use finite compact-support domains for scalar and intermediate bounds.
Etale scalar coherence, identified with the recorded PlusCompIso by its _hom_eq and
the unbounded/D+ comparison theorem, gives the etale square. Substitute the site
square at L, at F_f(L), and for gf. Naturality and cancellation of the adjacent
site inverses give precisely the stated intrinsic b equation. -/
theorem finiteCoefficientCompactSupport_composition
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : Input A X L.obj) :
    DerivedCategory.TStructure.t.plus ((scalar X.smallEtaleTopology a).obj L.obj) ∧
    ∀ hLB : DerivedCategory.TStructure.t.plus ((scalar X.smallEtaleTopology a).obj L.obj),
    let LB : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
      ⟨(scalar X.smallEtaleTopology a).obj L.obj, hLB⟩
    IsIso ((site A d).app ((et A c).obj L.obj)) ∧
    IsIso ((site B d).app ((et B c).obj LB.obj)) ∧
    ((scalar Z.smallEtaleTopology a).map (alpha A c d e L).hom ≫
        (beta a e).app L.obj =
      (beta a d).app ((et A c).obj L.obj) ≫ (et B d).map ((beta a c).app L.obj) ≫
        (alpha B c d e LB).hom) ∧
    (∀ (hc : IsIso ((site A c).app L.obj))
        (hd : IsIso ((site A d).app ((et A c).obj L.obj)))
        (hbc : IsIso ((site B c).app LB.obj))
        (hbd : IsIso ((site B d).app ((et B c).obj LB.obj))),
      IsIso (@proAlpha A _ _ X Y Z f g _ _ _ c d e L hc hd) ∧
      IsIso (@proAlpha B _ _ X Y Z f g _ _ _ c d e LB hbc hbd) ∧
      ((scalar (Scheme.ProEt.topology Z) a).map
          (@proAlpha A _ _ X Y Z f g _ _ _ c d e L hc hd) ≫
          (b a e).app ((nu A X).obj L.obj) ≫
          (pro B e).map ((delta a X).hom.app L.obj) =
        (b a d).app ((pro A c).obj ((nu A X).obj L.obj)) ≫
          (pro B d).map ((b a c).app ((nu A X).obj L.obj)) ≫
          (pro B d).map ((pro B c).map ((delta a X).hom.app L.obj)) ≫
          @proAlpha B _ _ X Y Z f g _ _ _ c d e LB hbc hbd)) := by
  sorry

/-- Only the transported refinement's identity and cocycle laws are stated here.
The etale laws and the arbitrary-common-refinement formula are the existing
PlusIso_refl, PlusIso_trans and PlusIso_eq_refinementIso of the dependency.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Locality (blueprint:
lem-sp-et-proet-coefficient-compatibility).

Proof: substitute proPhi and apply the dependency's D+ identity and cocycle laws
through PlusιIso. Functoriality and cancellation of the middle site-inverse pairs
give the two pro-etale equations. This also transports the dependency's formula
through every common refinement, without a Cartesian or density hypothesis. -/
theorem finiteCoefficientCompactSupport_refinement_coherence
    (c d e : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : Input A X L.obj) :
    (∀ (hc : IsIso ((site A c).app L.obj)),
      @proPhi A _ _ X Y f _ c c L hc = 𝟙 ((pro A c).obj ((nu A X).obj L.obj))) ∧
    (∀ (hc : IsIso ((site A c).app L.obj)) (hd : IsIso ((site A d).app L.obj)),
      @proPhi A _ _ X Y f _ c d L hc ≫ @proPhi A _ _ X Y f _ d e L hd =
        @proPhi A _ _ X Y f _ c e L hc) := by
  sorry

/-- The identity laws for proAlpha transported from the recorded D+ unit laws.
There is no second assertion of the dependency's etale identity laws.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Locality (blueprint:
lem-sp-et-proet-coefficient-compatibility).

Proof: use PlusCompIso_id_left and _id_right with PlusId, conjugating by the D+
compactification comparisons. Include via plusCompatibility and substitute
proAlpha. Cancel the adjacent site inverses; naturality of site gives the second
unit's shorter expression. This preserves the dependency's ordinary unit normalization. -/
theorem finiteCoefficientCompactSupport_composition_units
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : Input A X L.obj) :
    (∀ (hc : IsIso ((site A c).app L.obj))
        (hi : IsIso ((site A (Compactification.ofIsProper (𝟙 Y))).app ((et A c).obj L.obj))),
      @proAlpha A _ _ X Y Y f (𝟙 Y) _ _ _ c (Compactification.ofIsProper (𝟙 Y))
          (c.copy (Category.comp_id f)) L hc hi =
        (pro A (Compactification.ofIsProper (𝟙 Y))).map (inv ((site A c).app L.obj)) ≫
          inv ((site A (Compactification.ofIsProper (𝟙 Y))).app ((et A c).obj L.obj)) ≫
          (nu A Y).map (identityEt A Y (plusOut A c L)).hom ≫
          (site A c).app L.obj) ∧
    (∀ (hi : IsIso ((site A (Compactification.ofIsProper (𝟙 X))).app L.obj))
        (hc : IsIso ((site A c).app
          ((et A (Compactification.ofIsProper (𝟙 X))).obj L.obj))),
      @proAlpha A _ _ X X Y (𝟙 X) f _ _ _ (Compactification.ofIsProper (𝟙 X)) c
          (c.copy (Category.id_comp f)) L hi hc =
        (pro A c).map (inv ((site A (Compactification.ofIsProper (𝟙 X))).app L.obj) ≫
          (nu A X).map (identityEt A X L).hom)) := by
  sorry

/-- Associativity only for proAlpha, transported from the recorded PlusCompIso_assoc.
The final compactification's copy changes only its factorization proof.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Locality (blueprint:
lem-sp-et-proet-coefficient-compatibility).

Proof: the dependency's PlusCompIso_assoc gives etale associativity. Its _hom_eq
and PlusIso_trans express it at these specified compactifications. Include through
plusCompatibility and substitute proAlpha. Naturality commutes the intermediate
component, and adjacent site-inverse pairs cancel, including the component at F_f L.
The two pro-etale routes are therefore equal. -/
theorem finiteCoefficientCompactSupport_associativity
    {Z W : Scheme.{u}} [Z.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    (g : Y ⟶ Z) (h : Z ⟶ W) [g.IsOver (Spec (.of k))] [h.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dg dh : ℕ) [SmoothOfRelativeDimension dg g] [SmoothOfRelativeDimension dh h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h)
    (cd : Compactification (f ≫ g)) (de : Compactification (g ≫ h))
    (t : Compactification ((f ≫ g) ≫ h))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : Input A X L.obj) :
    ∀ (hc : IsIso ((site A c).app L.obj))
        (hd : IsIso ((site A d).app ((et A c).obj L.obj)))
        (hcd : IsIso ((site A cd).app L.obj))
        (hecd : IsIso ((site A e).app ((et A cd).obj L.obj)))
        (hedc : IsIso ((site A e).app ((et A d).obj ((et A c).obj L.obj))))
        (hde : IsIso ((site A de).app ((et A c).obj L.obj))),
      (pro A e).map (@proAlpha A _ _ X Y Z f g _ _ _ c d cd L hc hd) ≫
          @proAlpha A _ _ X Z W (f ≫ g) h _ _ _ cd e t L hcd hecd =
        (pro A e).map ((pro A d).map (inv ((site A c).app L.obj))) ≫
          @proAlpha A _ _ Y Z W g h _ _ _ d e de (plusOut A c L) hd hedc ≫
          (pro A de).map ((site A c).app L.obj) ≫
          @proAlpha A _ _ X Y W f (g ≫ h) _ _ _ c de
            (t.copy (Category.assoc f g h).symm) L hc hde := by
  sorry

/-- The canonical etale compact-support-to-sum comparison in the standing setting.
No local Noetherian or compactness assumption is added: both follow from finite type.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Charts (blueprint:
lem-sp-et-proet-coefficient-compatibility). -/
def sumNormalization (R : Type (u + 1)) [CommRing R] [Finite R]
    [Etale f] (c : Compactification f) :
    et R c ≅ (Etale.etaleLowerShriek (ModuleCat.{u + 1} R) f inferInstance).mapDerivedCategory := by
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  exact (Etale.canonicalEtaleCompactSupportNormalization R).comparison f c

/-- The etale coefficient arrow is summandwise scalar extension under the canonical
compact-support normalization. This is an equality of the named maps.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Charts, integral summation
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: compute on a bounded flat K-flat representative P of L. The compactification
acyclic comparison is the canonical graph-normalized sum comparison, including
its sheet component. Each sheet sends x tensor b to that same sheet's x tensor b.
Thus proper mate followed by open scalar is exactly sumScalar under sumNormalization.
Naturality transports the equality from QP to L. No flatness of B/A is used. -/
theorem finiteCoefficientCompactSupport_sum [Etale f]
    (c : Compactification f) (L : Etale.DerivedCategoryModule A X) (hL : Input A X L) :
    (beta a c).app L ≫ (sumNormalization k B c).hom.app
        ((scalar X.smallEtaleTopology a).obj L) =
      (scalar Y.smallEtaleTopology a).map ((sumNormalization k A c).hom.app L) ≫
        (sumScalar a f).hom.app L := by
  sorry

/-- Coefficient-counit identities transport through this exact compact-support c.
The forward form is equivalent to the inverse-beta/inverse-b counit formula,
since both coefficient arrows are isomorphisms on the specified input class.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Charts, transferred counit formula
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: substitute the site/coefficient square in the scalar extension of the
transferred A counit. Move delta past the counit by naturality, use the assumed
etale coefficient-counit identity, and move the B site comparison past t by
naturality. Cancel its inverse. This is precisely the counit formula of adjunction
transfer, evaluated at the image object; the equivalence unit restores arbitrary
isomorphic realizations. -/
theorem finiteCoefficientCompactSupport_counit
    (c : Compactification f)
    (L : Etale.DerivedCategoryModule A X) (hL : Input A X L)
    (N : Etale.DerivedCategoryModule B X) (hN : Input B X N)
    (K : Etale.DerivedCategoryModule A Y)
    (t : (scalar X.smallEtaleTopology a).obj L ⟶ N)
    (epsA : (et A c).obj L ⟶ K)
    (epsB : (et B c).obj N ⟶ (scalar Y.smallEtaleTopology a).obj K)
    (heps : (beta a c).app L ≫ (et B c).map t ≫ epsB =
      (scalar Y.smallEtaleTopology a).map epsA) :
    ∀ (hc : IsIso ((site A c).app L)) (hn : IsIso ((site B c).app N)),
      (b a c).app ((nu A X).obj L) ≫
          (pro B c).map ((delta a X).hom.app L ≫ (nu B X).map t) ≫
          inv ((site B c).app N) ≫ (nu B Y).map epsB =
        (scalar (Scheme.ProEt.topology Y) a).map
          (inv ((site A c).app L) ≫ (nu A Y).map epsA) ≫ (delta a Y).hom.app K := by
  sorry

/-- The transported refinement is natural in every morphism of D+ etale inputs.
Beta, b, site, delta and sumScalar are ambient natural transformations/isomorphisms;
phi is the recorded PlusιIso, and alpha is the included recorded D+ compositor.
Source: latest blueprint `sk-lem-sp-reduction-exceptional.md`, Charts and Locality (blueprint:
lem-sp-et-proet-coefficient-compatibility).

Proof: expand proPhi. Naturality of site and PlusιIso, and naturality of the inverse
of an invertible component, commute the three factors past the input morphism.
The site-inverse pairs cancel. The same argument applied to the four factors
of proAlpha gives naturality of composition; its etale middle factor is natural
by the recorded PlusCompIso and the compatibility isomorphisms. -/
theorem finiteCoefficientCompactSupport_refinement_naturality
    (c d : Compactification f)
    (L M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : Input A X L.obj) (hM : Input A X M.obj) (v : L ⟶ M) :
    ∀ (hcL : IsIso ((site A c).app L.obj)) (hcM : IsIso ((site A c).app M.obj)),
      (pro A c).map ((nu A X).map (DerivedCategory.Plus.ι.map v)) ≫
          @proPhi A _ _ X Y f _ c d M hcM =
        @proPhi A _ _ X Y f _ c d L hcL ≫
          (pro A d).map ((nu A X).map (DerivedCategory.Plus.ι.map v)) := by
  sorry


end Setting
end AlgebraicGeometry.ProEtale.CoefficientCompatibility
