module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Homology.TotalComplex

/-! # Strict models for punctual dg Hom and principal localization

Source: Stacks Project, dga.tex, Tags 09KY and 09LN; perfect.tex, Tag 08D2,
with the explicit left-dg refinement in the proof of finite principal Hom descent
(blueprint: def-sfb-dg-principal-hom-models).

All structures below specify constructions by their coordinates or universal properties.
They assert no existence and make no choices of objects from mere existence statements.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SheafDg.PrincipalHom

variable (S : Type u) [CommRing S]

/-- Punctual dg algebras, using the recorded sheaf-dg notion, not a second dg algebra.
Source: Stacks, 0FRF, on a point (blueprint: def-sfb-dg-principal-hom-models). -/
abbrev Algebra := SheafDg.Algebra (singletonRingSheaf S)

variable {S}

/-- Degreewise evaluation of the underlying coefficient complex on the point.
Source: Stacks, 00X9 and 09LN (blueprint: def-sfb-dg-principal-hom-models). -/
abbrev evaluate := (singletonEvaluation S).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordinary S-complex underlying a left dg module.
Source: Stacks, 00X9 and 09LN (blueprint: def-sfb-dg-principal-hom-models). -/
abbrev underlying (A : Algebra S) (M : LeftModule A) := (evaluate (S := S)).obj M.X

/-- Evaluate a module map on its actual complex.
Source: Stacks, 00X9 (blueprint: def-sfb-dg-principal-hom-models). -/
abbrev underlyingMap {A : Algebra S} {M N : LeftModule A} (g : M ⟶ N) :=
  (evaluate (S := S)).map g.hom

/-- A pair of dg modules, contravariant in the first variable.
Source: Stacks, 09LN (blueprint: def-sfb-dg-principal-hom-models). -/
abbrev Pairs (A : Algebra S) := (LeftModule A)ᵒᵖ × LeftModule A

/-- All signed dg-linear cochains, with their S-linear differential and functoriality.
The range condition uses the recorded Koszul linearity predicate. In particular,
there are neither extra summands nor missing homogeneous maps.
Source: Stacks, 09LN, left convention (blueprint: def-sfb-dg-principal-hom-models). -/
structure HomModel (A : Algebra S) where
  functor : Pairs A ⥤ CochainComplex (ModuleCat.{u} S) ℤ
  coordinate (P N : LeftModule A) (q : ℤ) :
    (functor.obj (op P, N)).X q →ₗ[S]
      CochainComplex.HomComplex.Cochain (underlying A P) (underlying A N) q
  injective (P N : LeftModule A) (q : ℤ) : Function.Injective (coordinate P N q)
  range (P N : LeftModule A) (q : ℤ)
      (h : CochainComplex.HomComplex.Cochain (underlying A P) (underlying A N) q) :
    (∃ z, coordinate P N q z = h) ↔
      ∃ g : GradedMap A P N q, g.val.map (singletonEvaluation S) = h
  differential (P N : LeftModule A) (q : ℤ) (z : (functor.obj (op P, N)).X q) :
    coordinate P N (q + 1) ((functor.obj (op P, N)).d q (q + 1) z) =
      CochainComplex.HomComplex.δ q (q + 1) (coordinate P N q z)
  naturality {P P' N N' : LeftModule A} (a : P' ⟶ P) (b : N ⟶ N')
      (q i : ℤ) (z : (functor.obj (op P, N)).X q) :
    (coordinate P' N' q ((functor.map (a.op, b)).f q z)).v i (i + q) rfl =
      (underlyingMap a).f i ≫ (coordinate P N q z).v i (i + q) rfl ≫
        (underlyingMap b).f (i + q)

/-- Homotopical projectivity: Hom into every acyclic dg module is acyclic.
No boundedness or termwise projectivity is included.
Source: Stacks, 09KM (blueprint: def-sfb-dg-principal-hom-models). -/
def IsHomotopicallyProjective {A : Algebra S} (H : HomModel A) (P : LeftModule A) : Prop :=
  ∀ L : LeftModule A, (underlying A L).Acyclic → (H.functor.obj (op P, L)).Acyclic

/-- Principal localization as an S-dg algebra and its actual balanced extension.
The termwise localization universal property fixes C_f and x ↦ x/1. Keeping
coefficients S expresses restriction of scalars from S_f. Every C_f-linear map
is then S_f-linear automatically, since the powers of f act invertibly.
The counit is the recorded action map b tensor n ↦ bn; this fixes the unit.
The adjunction and exact derived lifts are conclusions when this structure exists.
Source: Stacks, 00CS and 0FTR (blueprint: def-sfb-dg-principal-hom-models). -/
structure LocalizationModel (A : Algebra S) (f : S) where
  algebra : Algebra S
  map : A ⟶ algebra
  algebra_localized (n : ℤ) : IsLocalizedModule (Submonoid.powers f)
    (((singletonEvaluation S).map (map.hom.f n)).hom)
  adjunction : extension map ⊣ restrictScalars map
  counit_normalization (N : LeftModule algebra) :
    adjunction.counit.app N = actionCounit map N
  module_localized (M : LeftModule A) (n : ℤ) : IsLocalizedModule (Submonoid.powers f)
    ((underlyingMap (adjunction.unit.app M)).f n).hom
  exact_extension {M N : LeftModule A} (g : M ⟶ N) :
    QuasiIso (underlyingMap g) → QuasiIso (underlyingMap ((extension map).map g))
  exact_restriction {M N : LeftModule algebra} (g : M ⟶ N) :
    QuasiIso (underlyingMap g) → QuasiIso (underlyingMap ((restrictScalars map).map g))
  derivedExtension : Derived A ⥤ Derived algebra
  derivedRestriction : Derived algebra ⥤ Derived A
  extensionComparison : moduleQ A ⋙ derivedExtension ≅ extension map ⋙ moduleQ algebra
  restrictionComparison :
    moduleQ algebra ⋙ derivedRestriction ≅ restrictScalars map ⋙ moduleQ A
  derivedAdjunction : derivedExtension ⊣ derivedRestriction
  unit_normalization (M : LeftModule A) :
    derivedAdjunction.unit.app ((moduleQ A).obj M) =
      (moduleQ A).map (adjunction.unit.app M) ≫
        (restrictionComparison.inv.app ((extension map).obj M)) ≫
          derivedRestriction.map (extensionComparison.inv.app M)

/-- The nonempty intersections in Cech degree p=card(J)-1. This also makes
negative and out-of-range columns empty, without a boundedness assumption on modules.
Source: Stacks, 08D2 (blueprint: def-sfb-dg-principal-hom-models). -/
abbrev Index (r : ℕ) (p : ℤ) :=
  { J : Finset (Fin r) // J.Nonempty ∧ (J.card : ℤ) = p + 1 }

/-- The nonempty subsets indexing all intersections.
Source: Stacks, 08D2 (blueprint: def-sfb-dg-principal-hom-models). -/
abbrev Intersections (r : ℕ) := { J : Finset (Fin r) // J.Nonempty }

/-- Forget the degree of an intersection.
Source: Stacks, 08D2 (blueprint: def-sfb-dg-principal-hom-models). -/
def intersection {r : ℕ} {p : ℤ} (J : Index r p) : Intersections r := ⟨J.val, J.property.1⟩

/-- Product of the covering elements in an intersection.
Source: Stacks, 08D2 (blueprint: def-sfb-dg-principal-hom-models). -/
def product {r : ℕ} (f : Fin r → S) (J : Intersections r) : S := ∏ j ∈ J.val, f j

/-- Exact localized dg modules, their Hom complexes, and all further-localization maps.
The unit compatibility and fraction equation determine the transition on every
homogeneous Hom map, since the localized source is generated by fractions of x/1.
Source: Stacks, 08D2, dg refinement (blueprint: def-sfb-dg-principal-hom-models). -/
structure LocalDiagram (A : Algebra S) (H : HomModel A) (r : ℕ) (f : Fin r → S) where
  localization (J : Intersections r) : LocalizationModel A (product f J)
  hom (J : Intersections r) : HomModel (localization J).algebra
  change (J K : Intersections r) (h : J.val ⊆ K.val) :
    extension (localization J).map ⋙ restrictScalars (localization J).map ⟶
      extension (localization K).map ⋙ restrictScalars (localization K).map
  change_unit (J K : Intersections r) (h : J.val ⊆ K.val) (N : LeftModule A) :
    (localization J).adjunction.unit.app N ≫ (change J K h).app N =
      (localization K).adjunction.unit.app N
  toLocal (J : Intersections r) : H.functor ⟶
    ((extension (localization J).map).op.prod (extension (localization J).map)) ⋙
      (hom J).functor
  toLocal_fraction (J : Intersections r) (P N : LeftModule A) (q i : ℤ)
      (z : (H.functor.obj (op P, N)).X q) (x : (underlying A P).X i) :
    ((hom J).coordinate _ _ q (((toLocal J).app (op P, N)).f q z)).v i (i + q) rfl
        (((underlyingMap ((localization J).adjunction.unit.app P)).f i) x) =
      ((underlyingMap ((localization J).adjunction.unit.app N)).f (i + q))
        (((H.coordinate P N q z).v i (i + q) rfl) x)
  transition (J K : Intersections r) (h : J.val ⊆ K.val) :
    ((extension (localization J).map).op.prod (extension (localization J).map)) ⋙
      (hom J).functor ⟶
    ((extension (localization K).map).op.prod (extension (localization K).map)) ⋙
      (hom K).functor
  transition_fraction (J K : Intersections r) (h : J.val ⊆ K.val)
      (P N : LeftModule A) (q i : ℤ)
      (z : ((hom J).functor.obj
        (op ((extension (localization J).map).obj P),
          (extension (localization J).map).obj N)).X q) (x : (underlying A P).X i) :
    ((hom K).coordinate _ _ q (((transition J K h).app (op P, N)).f q z)).v
        i (i + q) rfl (((underlyingMap ((localization K).adjunction.unit.app P)).f i) x) =
      ((underlyingMap ((change J K h).app N)).f (i + q))
        ((((hom J).coordinate _ _ q z).v i (i + q) rfl)
          (((underlyingMap ((localization J).adjunction.unit.app P)).f i) x))

/-- The local Hom complex on a fixed intersection, as an S-complex.
Source: Stacks, 08D2 (blueprint: def-sfb-dg-principal-hom-models). -/
abbrev localHom {A : Algebra S} {H : HomModel A} {r : ℕ} {f : Fin r → S}
    (L : LocalDiagram A H r f) (J : Intersections r) :=
  ((extension (L.localization J).map).op.prod (extension (L.localization J).map)) ⋙
    (L.hom J).functor

/-- The actual finite alternating double complex and its singleton augmentation.
Coordinates fix each column, its internal differential, every alternating face,
and the augmentation. Mathlib's up/up total has differential delta+(-1)^p d.
Source: Stacks, 08D2, explicit dg refinement
(blueprint: def-sfb-dg-principal-hom-models). -/
structure CechModel {A : Algebra S} {H : HomModel A} {r : ℕ} {f : Fin r → S}
    (L : LocalDiagram A H r f) where
  diagram : Pairs A ⥤
    HomologicalComplex₂ (ModuleCat.{u} S) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  coordinate (Z : Pairs A) (p q : ℤ) :
    ((diagram.obj Z).X p).X q ≃ₗ[S]
      ∀ J : Index r p, ((localHom L (intersection J)).obj Z).X q
  vertical (Z : Pairs A) (p q : ℤ) (z : ((diagram.obj Z).X p).X q) (J : Index r p) :
    coordinate Z p (q + 1) (((diagram.obj Z).X p).d q (q + 1) z) J =
      ((localHom L (intersection J)).obj Z).d q (q + 1) (coordinate Z p q z J)
  horizontal (Z : Pairs A) (p q : ℤ) (J : Index r p) (K : Index r (p + 1))
      (z : ((localHom L (intersection J)).obj Z).X q) :
    coordinate Z (p + 1) q (((diagram.obj Z).d p (p + 1)).f q
        ((coordinate Z p q).symm (Pi.single J z))) K =
      ∑ j ∈ K.val, if h : K.val.erase j = J.val then
        (-1 : S) ^ (K.val.filter (fun k ↦ k < j)).card •
          (((L.transition (intersection J) (intersection K)
            (h ▸ Finset.erase_subset j K.val)).app Z).f q z)
        else 0
  naturality {Z Z' : Pairs A} (g : Z ⟶ Z') (p q : ℤ)
      (z : ((diagram.obj Z).X p).X q) (J : Index r p) :
    coordinate Z' p q (((diagram.map g).f p).f q z) J =
      ((localHom L (intersection J)).map g).f q (coordinate Z p q z J)
  augmentation : H.functor ⟶ diagram ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} S) (.up ℤ) (.up ℤ) (.up ℤ)
  augmentation_formula (Z : Pairs A) (q : ℤ) (z : (H.functor.obj Z).X q) :
    (augmentation.app Z).f q z =
      ((diagram.obj Z).ιTotal (.up ℤ) 0 q q (Int.zero_add q))
        ((coordinate Z 0 q).symm (fun J ↦
          ((L.toLocal (intersection J)).app Z).f q z))

end CategoryTheory.SheafDg.PrincipalHom
