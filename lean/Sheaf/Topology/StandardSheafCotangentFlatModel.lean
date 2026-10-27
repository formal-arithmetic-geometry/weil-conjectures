/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Topology.SheafCotangentComparison
public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.Sites.InverseImageDifferentials
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Flat standard cotangent models for sheaves of rings

Source: Stacks Project, cotangent.tex, Tags 08SR, 08SS, 08SV and 08T4;
sites-cohomology.tex, Tags 06YQ, 06YT and 06YY
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model).

We use the recorded standard sheaf model, not a new cotangent complex. Polynomial
maps and linearizations below are specified on all local standard generators.
The derived arrow is the canonical derived-extension counit followed by the
localization of that linearization. No object is selected from an existence proof.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Simplicial
open Algebra.CotangentResolution
open scoped ChangeOfRings

namespace TopCat.SheafCotangent

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- Labels of the polynomial variables, with no finiteness restriction.
Source: Stacks 08SR, 08T0
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
def standardVariables (f : Arrow CommRingCat.{u}) : ℕ → Type u
  | 0 => f.right
  | n + 1 => standardTerm f n

/-- The polynomial variable with the specified label.
Source: Stacks 08SR
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
def standardVariable (f : Arrow CommRingCat.{u}) :
    (n : ℕ) → standardVariables f n → standardTerm f n
  | 0, b => MvPolynomial.X b
  | _ + 1, p => MvPolynomial.X p

/-- The standard differential generator `1 ⊗ dx_e` in degree `-n`.
Source: Stacks 08SS, 00RX
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
def variableDifferential (C : Coherence.{u}) (f : Arrow CommRingCat.{u})
    (n : ℕ) (e : standardVariables f n) : (standardComplex C f).X (-(n : ℤ)) :=
  complexGenerator (C.differentials (C.standard f)) n 1
    (eqToHom ((C.standard_spec f).1 n).symm (standardVariable f n e))

/-- The actual standard sheaf complex from the comparison dependency.
Source: Stacks 08SS
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
abbrev standardSheafComplex (C : Coherence.{u}) (S : Comparison C)
    {T : TopCat.{u}} (f : Arrow (T.Sheaf CommRingCat.{u})) :=
  sheafComplex (S.sheaves T f).sections

/-- Canonical sheafification of a local scalar-extension tensor, with the coefficient
factor first. Source: Stacks 06YY
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
def scalarExtensionSection {T : TopCat.{u}} {B B' : T.Sheaf CommRingCat.{u}}
    (φ : B ⟶ B') (M : ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring B))
    (V : (Opens T)ᵒᵖ) (c : B'.obj.obj V) (x : M.val.obj V) :
    (SheafOfModules.changeOfRings.{u, u, u} (C := Opens T)
      (J := Opens.grothendieckTopology T) (R₁ := B) (R₂ := B') φ M).val.obj V :=
  @SMul.smul (B'.obj.obj V)
    ((SheafOfModules.changeOfRings.{u, u, u} (C := Opens T)
      (J := Opens.grothendieckTopology T) (R₁ := B) (R₂ := B') φ M).val.obj V)
    inferInstance c (WeilConjectures.SemilinearSections.extensionUnit.{u, u, u} φ M V x)

/-- Polynomial maps on sheaf standard resolutions, specified on all sectionwise
polynomials. Naturality in the simplex variable is exactly commutation with all
faces and degeneracies. Source: Stacks 08SS, 08SV
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
structure StandardPolynomialMap (C : Coherence.{u}) (S : Comparison C)
    {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g) where
  map : (S.sheaves T f).standard.algebra ⟶
    (S.sheaves T' g).standard.algebra ⋙ TopCat.Sheaf.pushforward CommRingCat.{u} v
  section_formula : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ)
    (p : standardTerm (sectionArrow f V) n),
    (map.app (op ⦋n⦌)).hom.app V
      (polynomialSection ((S.sheaves T f).standard.polynomial n)
        ((S.sheaves T f).standard.algebraIso n) V p) =
      polynomialSection ((S.sheaves T' g).standard.polynomial n)
        ((S.sheaves T' g).standard.algebraIso n) ((Opens.map v).op.obj V)
          (standardSquareMap (sectionSquare q V) n p)
  base : ∀ n : ℕ,
    (S.sheaves T f).standard.base.app (op ⦋n⦌) ≫ map.app (op ⦋n⦌) =
      q.left ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} v).map
        ((S.sheaves T' g).standard.base.app (op ⦋n⦌))
  augmentation : ∀ n : ℕ,
    map.app (op ⦋n⦌) ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} v).map
        ((S.sheaves T' g).standard.augmentation.app (op ⦋n⦌)) =
      (S.sheaves T f).standard.augmentation.app (op ⦋n⦌) ≫ q.right

/-- The linearized map on ordinary scalar extension, characterized on every local
pure tensor. This fixes the map uniquely, including its action on `dp ⊗ r`.
Source: Stacks 08SS and 06YY
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
structure StandardLinearization (C : Coherence.{u}) (S : Comparison C)
    {T : TopCat.{u}} {f g : Arrow (T.Sheaf CommRingCat.{u})} (q : f ⟶ g)
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring f.right))]
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring g.right))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
      q.right) where
  map : (D.E.mapHomologicalComplex (.up ℤ)).obj (standardSheafComplex C S f) ⟶
    standardSheafComplex C S g
  formula : ∀ (V : (Opens T)ᵒᵖ) (i : ℤ) (c : g.right.obj.obj V)
    (x : ((standardSheafComplex C S f).X i).val.obj V),
    (map.f i).val.app V
      ((eqToHom (D.obj_eq ((standardSheafComplex C S f).X i)).symm).val.app V
        (scalarExtensionSection q.right ((standardSheafComplex C S f).X i) V c x)) =
      @SMul.smul (g.right.obj.obj V) (((standardSheafComplex C S g).X i).val.obj V)
        inferInstance c (((S.maps (v := 𝟙 T) q).map.f i).hom.app V x)

/-- The canonical derived functoriality arrow: the canonical counit comparison
followed by the image of the uniquely normalized standard linearization. The
source is derived scalar extension of `L[B/A]`.
Source: Stacks 08SS, 06YY
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
def standardDerivedArrow (C : Coherence.{u}) (S : Comparison C)
    {T : TopCat.{u}} {f g : Arrow (T.Sheaf CommRingCat.{u})} (q : f ⟶ g)
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring f.right))]
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring g.right))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
      q.right)
    (m : StandardLinearization C S q D) :=
  D.ε.app (standardSheafComplex C S f) ≫ DerivedCategory.Q.map m.map

/-- The normalized comparison from continuous inverse image of the standard complex.
Its underlying arrow is the adjoint fixed in the comparison dependency.
Source: Stacks 08SV
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
def inverseStandardMap (C : Coherence.{u}) (S : Comparison C)
    {T T' : TopCat.{u}} (v : T' ⟶ T) (f : Arrow (T.Sheaf CommRingCat.{u})) :=
  ((inverseAdjunction v).homEquiv _ _).symm (S.maps (inverseImageSquare v f)).map

/-- Strict polynomial and differential functoriality, with continuous inverse-image
naturality. All maps are normalized by the prescribed standard coordinates.
Source: Stacks 08SS and 08SV
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
structure StandardSheafFunctoriality (C : Coherence.{u}) (S : Comparison C) where
  polynomial : ∀ {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g), StandardPolynomialMap C S q
  polynomial_id : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u})),
    (polynomial (identitySquare f)).map = 𝟙 _
  polynomial_comp : ∀ {T T' T'' : TopCat.{u}} {v : T' ⟶ T} {w : T'' ⟶ T'}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    {h : Arrow (T''.Sheaf CommRingCat.{u})} (q : RingSquare v f g) (r : RingSquare w g h),
    (polynomial (composeSquare q r)).map = (polynomial q).map ≫
      Functor.whiskerRight (polynomial r).map (TopCat.Sheaf.pushforward CommRingCat.{u} v)
  polynomial_inverse : ∀ {T T' : TopCat.{u}} (v : T' ⟶ T)
    (f : Arrow (T.Sheaf CommRingCat.{u})) (n : ℕ),
    IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} v).homEquiv _ _).symm
      ((polynomial (inverseImageSquare v f)).map.app (op ⦋n⦌)))
  chain_generator : ∀ {T T' : TopCat.{u}} {v : T' ⟶ T}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    (q : RingSquare v f g) (n : ℕ) (V : (Opens T)ᵒᵖ) (b : f.right.obj.obj V)
    (p : (C.standard (sectionArrow f V)).algebra.obj (op ⦋n⦌)),
    (((S.maps q).map.f (-(n : ℤ))).hom.app V)
      (sectionElement (S.sheaves T f).sections V (-(n : ℤ))
        (complexGenerator (C.differentials (C.standard (sectionArrow f V))) n b p)) =
      sectionElement (S.sheaves T' g).sections ((Opens.map v).op.obj V) (-(n : ℤ))
        (complexGenerator
          (C.differentials (C.standard (sectionArrow g ((Opens.map v).op.obj V)))) n
          (q.right.hom.app V b) ((C.standardMap (sectionSquare q V)).map.app (op ⦋n⦌) p))
  chain_id : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u})),
    (S.maps (identitySquare f)).map = 𝟙 _
  chain_comp : ∀ {T T' T'' : TopCat.{u}} {v : T' ⟶ T} {w : T'' ⟶ T'}
    {f : Arrow (T.Sheaf CommRingCat.{u})} {g : Arrow (T'.Sheaf CommRingCat.{u})}
    {h : Arrow (T''.Sheaf CommRingCat.{u})} (q : RingSquare v f g) (r : RingSquare w g h),
    (S.maps (composeSquare q r)).map =
      (S.maps q).map ≫ (pushforwardComplex v).map (S.maps r).map
  inverse_naturality : ∀ {T T' : TopCat.{u}} (v : T' ⟶ T)
    {f g : Arrow (T.Sheaf CommRingCat.{u})} (q : f ⟶ g),
    (pullbackComplex v).map (S.maps (v := 𝟙 T) q).map ≫ inverseStandardMap C S v g =
      inverseStandardMap C S v f ≫
        (S.maps (v := 𝟙 T')
          ((TopCat.Sheaf.pullback CommRingCat.{u} v).mapArrow.map q)).map

/-- Canonical scalar extensions of the standard model and their linearizations,
including the prescribed tensor-composition equation. This groups the scalar
clauses without changing the maps or introducing a choice of comparison.
Source: Stacks 08SS and 06YY
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
structure StandardScalarFunctoriality (C : Coherence.{u}) (S : Comparison C) where
  represents : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u}))
    (B' : T.Sheaf CommRingCat.{u}) (φ : f.right ⟶ B')
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring f.right))]
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring B'))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
      φ),
    IsIso (D.ε.app (standardSheafComplex C S f))
  linearization : ∀ {T : TopCat.{u}} {f g : Arrow (T.Sheaf CommRingCat.{u})} (q : f ⟶ g)
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring f.right))]
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring g.right))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
      q.right),
    StandardLinearization C S q D
  successive_tensor : ∀ {T : TopCat.{u}}
    {f g h : Arrow (T.Sheaf CommRingCat.{u})} (q : f ⟶ g) (r : g ⟶ h)
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring f.right))]
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring g.right))]
    [HasDerivedCategory.{u + 1}
      (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring h.right))]
    (Dq : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
      q.right)
    (Dr : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
      r.right)
    (Dqr : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
      (q ≫ r).right)
    (V : (Opens T)ᵒᵖ) (i : ℤ) (x : ((standardSheafComplex C S f).X i).val.obj V)
    (c : g.right.obj.obj V) (d : h.right.obj.obj V),
    ((linearization r Dr).map.f i).val.app V
      ((eqToHom (Dr.obj_eq ((standardSheafComplex C S g).X i)).symm).val.app V
        (scalarExtensionSection r.right ((standardSheafComplex C S g).X i) V d
          (((linearization q Dq).map.f i).val.app V
            ((eqToHom (Dq.obj_eq ((standardSheafComplex C S f).X i)).symm).val.app V
              (scalarExtensionSection q.right ((standardSheafComplex C S f).X i) V c x))))) =
      ((linearization (q ≫ r) Dqr).map.f i).val.app V
        ((eqToHom (Dqr.obj_eq ((standardSheafComplex C S f).X i)).symm).val.app V
          (scalarExtensionSection (q ≫ r).right ((standardSheafComplex C S f).X i) V
            (d * r.right.hom.app V c) x))

/-- Flatness and strict functoriality of the already specified standard models.
The supplied `C` and `S` are presentations of canonical constructions, not
flatness assumptions. Stalk bases have the specified polynomial-variable vectors.
The last equation is tensor reassociation, in coefficient-first convention:
`d ⊗ (c ⊗ x) ↦ (d * β(c)) ⊗ x`. Continuous maps are included in polynomial
and semilinear functoriality; open inclusions are particular continuous maps.
Source: Stacks 08SR, 08SS, 08SV, 08T4, 06YQ and 06YY
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model). -/
structure FlatFunctorialModel (C : Coherence.{u}) (S : Comparison C) where
  stalk_basis : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u}))
    (t : T) (n : ℕ), ∃ b : Module.Basis (standardVariables (stalkArrow f t) n)
      (stalkArrow f t).right ((S.stalks T f t).complex.X (-(n : ℤ))),
      ∀ e : standardVariables (stalkArrow f t) n,
        b e = (S.stalks T f t).comparison.inv.f (-(n : ℤ))
          (variableDifferential C (stalkArrow f t) n e)
  positive_zero : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u}))
    (i : ℤ), 0 < i → IsZero ((standardSheafComplex C S f).X i)
  flat : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u})) (i : ℤ),
    SheafOfModules.IsFlatOnSite (C := Opens T) (R := f.right) ((standardSheafComplex C S f).X i)
  kflat : ∀ (T : TopCat.{u}) (f : Arrow (T.Sheaf CommRingCat.{u})),
    CochainComplex.IsKFlatIndependentCoefficients (C := Opens T) (R := f.right)
      (standardSheafComplex C S f)
  functoriality : StandardSheafFunctoriality C S
  scalar : StandardScalarFunctoriality C S

/-- The standard sheaf cotangent model has free stalks, flat terms and is K-flat;
its prescribed polynomial and differential maps are strictly functorial and their
linearizations represent the canonical derived arrows, compatibly with restriction,
continuous inverse image and successive scalar extension.
Source: Stacks 08SR, 08SS, 08SV, 08T4, 00RX, 06YQ, 06YT and 06YY
(blueprint: lem-sfb-standard-sheaf-cotangent-flat-functorial-model).

Proof:
1. Use the sectionwise standard polynomial resolution and sheafification from
   lem-trf-cotangent-resolution-coherence and lem-trf-affine-cotangent-comparison.
   The differential is the alternating sum of faces; simplicial identities cancel
   consecutive differentials. Its derived image is the defined cotangent complex.
2. At a point, finite polynomial expressions descend to one common neighbourhood.
   Equality likewise holds after shrinking. Iterating identifies the polynomial
   stalks, including labels, with the ring standard resolution. Apply
   lem-trf-topos-inverse-image-differentials and lem-pc-ringed-space-module-stalk-tensor
   to identify the actual degreewise differential tensor modules.
3. Apply lem-weil-pbc-polynomial-ring-kahler-basis-any-variables at the stalk.
   Swap the two tensor factors; the vectors dx_e tensor 1 give the stated basis,
   including infinite sets of variables.
4. Free stalks are flat: tensor is the direct sum of the original module, and a
   finite-support family lifts coordinatewise through a surjection. Use
   lem-weil-pbc-module-stalk-exact and lem-pc-ringed-space-module-stalk-tensor
   to deduce sheaf tensor exactness, hence def-pc-flat-sheaf-modules. Positive
   terms are zero and flat.
5. The upper bound is zero. Apply lem-pc-bounded-above-flat-kflat-site to obtain
   def-pc-kflat-complex. No lower bound is needed.
6. Apply lem-pur-derived-change-of-rings to the identity resolution of this
   K-flat complex. Its canonical counit is invertible, and identifies the ordinary
   extension with derived extension. No flatness of the new ring is required.
7. Use standardSquareMap recursively: coefficients follow the base map and
   [p] maps to [t(p)]. It respects evaluation, unit, augmentation and restrictions.
   Polynomial uniqueness gives strict identity and composition after sheafification.
8. Send dp tensor r to d(t(p)) tensor beta(r). The Kahler relations and balancing
   are preserved by the augmented square. It commutes with every face, hence the
   alternating differential. Identity and composition agree on these generators.
9. Linearize this map by dp tensor r tensor c mapping to d(t(p)) tensor beta(r)c.
   Its derived image composed with the canonical extension counit is precisely
   the canonical arrow, by the definition in Stacks 08SS and step 6.
10. Inverse image preserves free algebras, differentials and tensors, by
    lem-trf-affine-cotangent-comparison, lem-trf-topos-inverse-image-differentials
    and lem-weil-pbc-ringed-topoi-module-pullback-tensor. Both orders send [p]
    to [u^-1(t(p))] and dp tensor r to d(u^-1(t(p))) tensor u^-1(beta(r)).
    The comparisons commute as chain maps. Open restriction is the special case
    of an open inclusion; the recorded S.inverse_comp fixes their comparisons.
11. Tensor reassociation sends d tensor (c tensor x) to d beta(c) tensor x.
    The inverse inserts 1. Both composite maps have the same values on these
    generators by strict composition in step 8. The same computation applies
    after continuous inverse image, using step 10. -/
theorem exists_flatFunctorialModel (C : Coherence.{u}) (S : Comparison C) :
    Nonempty (FlatFunctorialModel C S) := by
  sorry

end TopCat.SheafCotangent
