/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Data.ZMod.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Derived reduction of an extension by a divisible sheaf

Source: the Cartier unit proof, paragraphs 4 and 5, in blueprint main-20261015;
Stacks Tags 06YU, 06YV, 06YY, 0152, 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Kernel and quotient objects are specified by their short exact sequences, including
existence of their residue-coefficient structures. The normalized identifications are
unique, so the definition of the reduced boundary makes no arbitrary choice of map.
The normalized sheaf scalar adjunction is an item helper; the general internal-module
derived extension of scalars remains the recorded dependency interface.
-/

@[expose] public section
set_option autoImplicit false
universe u v r wZ wR u' v' wZ' wR'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {Z R : Sheaf J CommRingCat.{r}} (q : Z ⟶ R)

/-- Restriction is exact: it retains the underlying abelian sheaf.
Source: Stacks 03D7 and 015F (blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: kernels are sectionwise kernels with restricted action. Cokernels are the
sheafifications of the same abelian presheaf quotients on both sides. Restriction
therefore preserves kernels and cokernels, hence all finite limits and colimits. -/
theorem sheafScalarRestriction_exact :
    PreservesFiniteLimits (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)) ∧
    PreservesFiniteColimits (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)) := by
  sorry

/-- Exact restriction preserves finite limits.
Source: Stacks 015F (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable instance sheafScalarRestrictionLimits :
    PreservesFiniteLimits (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)) :=
  (sheafScalarRestriction_exact q).1

/-- Exact restriction preserves finite colimits.
Source: Stacks 015F (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable instance sheafScalarRestrictionColimits :
    PreservesFiniteColimits (restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)) :=
  (sheafScalarRestriction_exact q).2

variable [HasDerivedCategory.{wZ} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J Z))]
  [HasDerivedCategory.{wR} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J R))]
  (D : DerivedChangeOfRingsCochainModel q)

/-- The ordinary and derived adjunctions, including both unit normalizations.
Source: Stacks 03D7, 015F, 09T5, 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: the sectionwise tensor/restriction adjunction sends m to 1 tensor m;
sheafification extends it uniquely and gives the first equation. Exactness of
restriction identifies its right derived functor with termwise restriction.
Apply the derived-adjoint-functors theorem to the universal pair D. On a K-flat
complex the ordinary unit has ordinary adjunct the identity. The pre-derived
adjunction formula therefore has derived adjunct the identity as well. This is
exactly the second equation, using D's universal counit and the localization
comparison for restriction. K-flat resolutions extend this formula to every
object, independently of its representative. -/
theorem sheafDerivedScalarAdjunction_exists :
    ∃ a : D.E ⊣ restrictScalars.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q),
      (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J Z))
        (U : Cᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x =
          (eqToHom (D.obj_eq M).symm).val.app U
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).unit.app
                (changeOfRingsPresheaf q M)).app U
                  ((ModuleCat.extendRestrictScalarsAdj (q.hom.app U).hom).unit.app
                    (M.val.obj U) x))) ∧
      ∃ ad : D.T ⊣ (restrictScalars.{r}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map q)).mapDerivedCategory,
        ∀ P : CochainComplex
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J Z)) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := Z) P →
          ad.unit.app (DerivedCategory.Q.obj P) ≫
            (restrictScalars.{r} ((sheafCompose J
              (forget₂ CommRingCat.{r} RingCat.{r})).map q)).mapDerivedCategory.map
                (D.ε.app P) ≫
            (restrictScalars.{r} ((sheafCompose J
              (forget₂ CommRingCat.{r} RingCat.{r})).map q)).mapDerivedCategoryFactors.hom.app
                ((D.E.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  sorry

/-- The ordinary adjunction determined by its sectionwise unit.
Source: Stacks 03D7 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def sheafScalarOrdinaryAdjunction :=
  Classical.choose (sheafDerivedScalarAdjunction_exists q D)

/-- The derived adjunction determined by its K-flat unit normalization.
Source: Stacks 09T5 and 0FND (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def sheafScalarDerivedAdjunction :=
  Classical.choose (Classical.choose_spec (sheafDerivedScalarAdjunction_exists q D)).2

/-- The canonical shift comparison, induced from exact restriction by the normalized
adjunction. This fixes compatibility with its unit, instead of choosing an unrelated
triangulated shift structure. Source: Stacks 06YY and 09T5
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable instance sheafScalarModelCommShift : D.T.CommShift ℤ :=
  (sheafScalarDerivedAdjunction q D).leftAdjointCommShift ℤ

end SheafOfModules

namespace SheafOfModules
namespace DivisibleReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The constant integer ring sheaf. Source: Stacks 06YU and the Cartier proof,
paragraph 4 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev integers :=
  (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of (ULift.{r} ℤ))

/-- The constant residue ring sheaf. Source: Stacks 06YU and the Cartier proof,
paragraph 4 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev residues (n : ℕ) :=
  (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of (ULift.{r} (ZMod n)))

/-- The actual constant coefficient projection, induced by integer reduction.
Source: Stacks 06YU (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def projection (n : ℕ) : integers J ⟶ residues J n :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Int.castRingHom (ZMod n)).comp ULift.ringEquiv.toRingHom)))

/-- Integer module sheaves, using the recorded general ringed-site category.
Source: Stacks 06YU (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev Integral :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J (integers J))

/-- Residue module sheaves, using the recorded general ringed-site category.
Source: Stacks 06YU (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev Residue (n : ℕ) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J (residues J n))

/-- Ordinary restriction along the actual coefficient projection.
Source: Stacks 06YY (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev restriction (n : ℕ) : Residue J n ⥤ Integral J :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
    (projection J n))

/-- The unit integer sheaf, as a module over itself.
Source: Cartier proof, paragraph 5 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev integerUnit : Integral J :=
  unit (derivedChangeRingIndependentCoefficients J (integers J))

/-- The unit residue sheaf, as a module over itself.
Source: Cartier proof, paragraph 5 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev residueUnit (n : ℕ) : Residue J n :=
  unit (derivedChangeRingIndependentCoefficients J (residues J n))

/-- The ordinary coefficient unit sends 1 to 1 and is induced by the constant ring map.
Source: Stacks 06YU (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def coefficientUnit (n : ℕ) :
    integerUnit J ⟶ (restriction J n).obj (residueUnit J n) :=
  ((restriction J n).obj (residueUnit J n)).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : (residues J n).obj.obj U))
      (fun {_ _} f ↦ ((residues J n).obj.map f).hom.map_one))

variable {J} (n : ℕ)

/-- An extension and presentations of its torsion and quotient sheaves.
The two additional short exact sequences specify precisely ker(n on B), its natural
residue action, and coker(n on F); they also express epimorphy on B and monicity on F.
Source: Cartier proof, paragraph 4
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
structure Presentation where
  S : ShortComplex (Integral J)
  exact : S.ShortExact
  H : Residue J n
  Q : Residue J n
  i : (restriction J n).obj H ⟶ S.X₁
  p : S.X₃ ⟶ (restriction J n).obj Q
  wi : i ≫ (n • 𝟙 S.X₁) = 0
  wp : (n • 𝟙 S.X₃) ≫ p = 0
  kummer : (ShortComplex.mk i (n • 𝟙 S.X₁) wi).ShortExact
  quotient : (ShortComplex.mk (n • 𝟙 S.X₃) p wp).ShortExact

/-- Every extension under the node's hypotheses has these coefficient presentations.
Source: Cartier proof, paragraph 4; Stacks 06YU
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: take the kernel of n on B and the sheaf cokernel of n on F. Multiplication
by n vanishes on each; locally integer scalar multiplication therefore factors
uniquely through Z/n, and these actions glue through constant sheafification.
The kernel inclusion and quotient projection are integer-linear. Epi on B and
mono on F give the two displayed short exact sequences. The universal properties
of kernel and cokernel identify any two presentations uniquely. -/
theorem presentation_exists [HasTerminal C] (hn : 1 ≤ n)
    (S : ShortComplex (Integral J)) (hS : S.ShortExact)
    (hB : Epi (n • 𝟙 S.X₁)) (hF : Mono (n • 𝟙 S.X₃)) :
    ∃ P : Presentation (J := J) n, P.S = S := by
  sorry

variable [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wR} (Residue J n)]
  (D : DerivedChangeOfRingsCochainModel (projection J n))

/-- Termwise derived restriction.
Source: Stacks 015F (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable abbrev derivedRestriction := (restriction J n).mapDerivedCategory

/-- The normalized derived scalar unit on an integer module sheaf.
Source: Stacks 09T5, 0FND (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def eta (A : Integral J) :=
  (sheafScalarDerivedAdjunction (projection J n) D).unit.app
    ((DerivedCategory.singleFunctor (Integral J) 0).obj A)

/-- The canonical Kummer boundary, with termwise restriction and single comparison.
Source: Stacks 0152 (blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def kappa (P : Presentation (J := J) n) :=
  P.kummer.singleδ ≫
    (((restriction J n).mapDerivedCategorySingleFunctor 0).inv.app P.H)⟦(1 : ℤ)⟧' ≫
    ((derivedRestriction n).commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)

/-- Normalized reduction identifications. The quotient isomorphism induces the actual
quotient projection on units; the torsion isomorphism induces the Kummer boundary.
Source: Cartier proof, paragraphs 4 and 5; Stacks 06YY and 0152
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
structure Identifications (P : Presentation (J := J) n) where
  alphaF : D.T.obj ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₃) ≅
    (DerivedCategory.singleFunctor (Residue J n) 0).obj P.Q
  alphaB : D.T.obj ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₁) ≅
    ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)⟦(1 : ℤ)⟧
  quotient_unit : eta n D P.S.X₃ ≫ (derivedRestriction n).map alphaF.hom ≫
    ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app P.Q =
      (DerivedCategory.singleFunctor (Integral J) 0).map P.p
  kummer_unit : eta n D P.S.X₁ ≫ (derivedRestriction n).map alphaB.hom = kappa n P

/-- The two reduction isomorphisms, with their canonical unit normalization.
Source: Cartier proof, paragraphs 4 and 5; Stacks 06YU, 06YY, 0152, 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof:
1. Use the normalized scalar adjunction (sk-def-sfb-derived-extension-of-scalars).
   Exact restriction is termwise, and its derived unit on a K-flat representative
   is the ordinary coefficient unit; this formula commutes with shifts.
2. The constant sequence Z --n--> Z --> R is exact, and A tensor R = coker(n on A).
   Both assertions follow locally from integers and their residue classes.
3. Resolve A by a flat-term K-flat complex P (lem-pc-kflat-resolution).
   The termwise multiplication sequence gives the distinguished triangle
   A --n--> A --eta--> Res Lq(A) --> A[1]
   (lem-pur-derived-change-of-rings; lem-weil-pbc-complex-ses-triangle).
4. Its long exact cohomology sequence gives only degrees -1 and 0, the kernel
   and cokernel of n (lem-sf-derived-homology-long-exact). Use the rotated triangle
   to fix the map to A, rather than an unspecified cohomology boundary.
5. Canonical truncation in residue modules identifies a complex with its sole
   cohomology sheaf in the appropriate degree (def-sbc-standard-tstructure-derived-category).
6. Compare the multiplication triangle for B with the rotated Kummer triangle
   B --n--> B --kappa--> H[1] ---i[1]--> B[1]. TR3 fixes the identification by
   (-i) H^-1(alphaB) = H^-1(delta). Monicity of i fixes its sign uniquely.
   Shifted single-object full faithfulness identifies its restriction with that
   triangle map (lem-weil-pbc-derived-single-fully-faithful).
7. The quotient unit fixes alphaF uniquely because p is epi. The Kummer unit
   fixes alphaB uniquely: Hom(B,H)=0 by n-divisibility, and the Kummer exact
   Hom sequence makes precomposition with kappa injective on End(H[1]).
   Residue-linearity is automatic for integer-linear maps of n-annihilated sheaves.
   These facts give uniqueness, not an unspecified choice of either isomorphism. -/
theorem divisible_extension_derived_reduction [HasTerminal C] (hn : 1 ≤ n)
    (P : Presentation (J := J) n) : Nonempty (Unique (Identifications n D P)) := by
  sorry

/-- The unique normalized identifications; their data is determined by the unit equations.
Source: Cartier proof, paragraph 4
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def identifications [HasTerminal C] (hn : 1 ≤ n)
    (P : Presentation (J := J) n) : Identifications n D P :=
  (Classical.choice (divisible_extension_derived_reduction n D hn P)).default

/-- The reduced extension boundary, with the canonical comparison [1][1] = [2].
Source: Cartier proof, paragraph 4
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def boundary [HasTerminal C] (hn : 1 ≤ n) (P : Presentation (J := J) n) :
    (DerivedCategory.singleFunctor (Residue J n) 0).obj P.Q ⟶
      ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)⟦(2 : ℤ)⟧ :=
  (identifications n D hn P).alphaF.inv ≫ D.T.map P.exact.singleδ ≫
    (D.T.commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₁) ≫
    (identifications n D hn P).alphaB.hom⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd (DerivedCategory (Residue J n)) (1 : ℤ) 1).inv.app
      ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)

/-- The unit object reduces canonically to the residue unit.
Source: Cartier proof, paragraph 5; Stacks 06YU, 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: Z[0] is K-flat since tensoring with it is the identity. Apply the K-flat
counit to identify its scalar extension with R[0]. The normalized derived unit
is the ordinary coefficient map. Conversely this unit equation determines the
isomorphism, by the scalar adjunction and the fact that a map of residue unit
sheaves is fixed on 1. -/
theorem coefficientIso_existsUnique [HasTerminal C] (hn : 1 ≤ n) :
    ∃! e : D.T.obj ((DerivedCategory.singleFunctor (Integral J) 0).obj (integerUnit J)) ≅
        (DerivedCategory.singleFunctor (Residue J n) 0).obj (residueUnit J n),
      eta n D (integerUnit J) ≫ (derivedRestriction n).map e.hom ≫
        ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app (residueUnit J n) =
      (DerivedCategory.singleFunctor (Integral J) 0).map (coefficientUnit J n) := by
  sorry

/-- The unit reduction fixed by the actual coefficient map.
Source: Cartier proof, paragraph 5
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable def coefficientIso [HasTerminal C] (hn : 1 ≤ n) :=
  Classical.choose (coefficientIso_existsUnique n D hn)

/-- Reduction of a section and the precise derived adjunct formula.
Source: Cartier proof, paragraph 5; Stacks 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: reduce the map s using the quotient universal property; the local formula
sends the residue of k to p(s(k)). Single-object full faithfulness identifies
its derived map with alphaF Lq(s) coefficientIso^-1. Apply the scalar adjunction:
the adjunct is Res(d sbar) eta_Z. Naturality of eta for s and for the extension
boundary, followed by shift compatibility and the Kummer unit equation, gives
s followed by partial_S followed by kappa[1]. The final two comparison maps
identify restriction of H[1][1] with restriction of H[2]. This is exactly the
Kummer connecting image of the extension boundary; it fixes the sign. -/
theorem boundary_adjunct [HasTerminal C] (hn : 1 ≤ n) (P : Presentation (J := J) n)
    (s : integerUnit J ⟶ P.S.X₃) :
    ∃! sbar : residueUnit J n ⟶ P.Q,
      (coefficientUnit J n ≫ (restriction J n).map sbar = s ≫ P.p) ∧
      (DerivedCategory.singleFunctor (Residue J n) 0).map sbar =
        (coefficientIso n D hn).inv ≫
          D.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map s) ≫
          (identifications n D hn P).alphaF.hom ∧
      (sheafScalarDerivedAdjunction (projection J n) D).homEquiv _ _
        ((coefficientIso n D hn).hom ≫
          (DerivedCategory.singleFunctor (Residue J n) 0).map sbar ≫ boundary n D hn P) =
        (DerivedCategory.singleFunctor (Integral J) 0).map s ≫ P.exact.singleδ ≫
          (kappa n P)⟦(1 : ℤ)⟧' ≫
          ((derivedRestriction n).commShiftIso (1 : ℤ)).inv.app
            (((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)⟦(1 : ℤ)⟧) ≫
          (derivedRestriction n).map
            ((shiftFunctorAdd (DerivedCategory (Residue J n)) (1 : ℤ) 1).inv.app
              ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H)) := by
  sorry

/-- Naturality for every morphism of the short exact extensions, with the maps
on torsion and quotient specified by their kernel and cokernel squares.
Source: Cartier proof, paragraphs 4 and 5
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: replace the arrow diagram by a simultaneous flat-term K-flat diagram
(lem-weil-pbc-diagram-kflat-replacements). Its multiplication triangles commute
by the functorial complex short-exact-sequence triangle. Kernels, cokernels and
truncations are functorial, and monicity of the target kernel inclusion fixes
the normalized torsion identification. The extension boundary is functorial by
singleTriangle.map. Applying Lq and composing the resulting squares gives the
last equation. Thus this includes both identification squares and the square
for the reduced boundary, rather than only naturality of its cohomology class. -/
theorem boundary_natural [HasTerminal C] (hn : 1 ≤ n)
    (P P' : Presentation (J := J) n) (f : P.S ⟶ P'.S)
    (h : P.H ⟶ P'.H) (q : P.Q ⟶ P'.Q)
    (hi : (restriction J n).map h ≫ P'.i = P.i ≫ f.τ₁)
    (hp : f.τ₃ ≫ P'.p = P.p ≫ (restriction J n).map q) :
    D.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map f.τ₃) ≫
        (identifications n D hn P').alphaF.hom =
      (identifications n D hn P).alphaF.hom ≫
        (DerivedCategory.singleFunctor (Residue J n) 0).map q ∧
    D.T.map ((DerivedCategory.singleFunctor (Integral J) 0).map f.τ₁) ≫
        (identifications n D hn P').alphaB.hom =
      (identifications n D hn P).alphaB.hom ≫
        ((DerivedCategory.singleFunctor (Residue J n) 0).map h)⟦(1 : ℤ)⟧' ∧
    (DerivedCategory.singleFunctor (Residue J n) 0).map q ≫ boundary n D hn P' =
      boundary n D hn P ≫
        ((DerivedCategory.singleFunctor (Residue J n) 0).map h)⟦(2 : ℤ)⟧' := by
  sorry

section InverseImage

variable {C' : Type u'} [Category.{v'} C'] [EssentiallySmall.{r} C']
  {K : GrothendieckTopology C'}
  [HasSheafify K CommRingCat.{r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
  [HasDerivedCategory.{wZ'} (Integral K)] [HasDerivedCategory.{wR'} (Residue K n)]
  (D' : DerivedChangeOfRingsCochainModel (projection K n))
  (UZ : Integral J ⥤ Integral K) (UR : Residue J n ⥤ Residue K n)
  [UZ.Additive] [PreservesFiniteLimits UZ] [PreservesFiniteColimits UZ]
  [UR.Additive] [PreservesFiniteLimits UR] [PreservesFiniteColimits UR]

/-- Compatibility with every exact inverse image of a geometric morphism.
The natural isomorphisms eZ and eR say that UZ and UR are its lifts to the two
constant-coefficient module categories. The comparison rho identifies their
restrictions, hence includes the induced constant-ring identification. Neither
a tensor comparison nor a derived comparison is assumed: both are conclusions.
Source: Cartier proof, paragraphs 4 and 5; Stacks 06YY, 0G7E, 07A4 and 0152
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Proof: inverse image preserves coproducts and the terminal object, hence constant
rings. Transporting addition and the constant scalar action gives UZ and UR.
Their ordinary scalar comparison e is fixed by the ordinary unit equation below.
Pullback preserves flat-term K-flat resolutions by the ringed-topoi derived
tensor-pullback theorem. The K-flat universal counits therefore induce theta,
with exactly the displayed representative formula. This formula commutes with
shifts, since the ordinary functors and their units do so degree by degree.
Exactness preserves kernels, cokernels and the two multiplication sequences.
It preserves the canonical boundary -p q^-1: it sends the cone differential,
projection p and quasi-isomorphism q to those of the pulled-back sequence.
It also preserves the truncation zigzags and the equation fixing the sign of
alphaB. Thus both normalized identifications commute with theta. Applying this
to the extension boundary gives the last square. The unit formula and naturality
of the scalar adjunction then transport boundary_adjunct as well, including the
identity inverse image and arbitrary coefficient presentations. -/
theorem inverse_image_natural [HasTerminal C] [HasTerminal C'] (hn : 1 ≤ n)
    (U : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (V : Sheaf K (Type r) ⥤ Sheaf J (Type r))
    (adj : U ⊣ V) [PreservesFiniteLimits U]
    (eZ : UZ ⋙ (toSheaf (derivedChangeRingIndependentCoefficients K (integers K)) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{r})) ≅
      (toSheaf (derivedChangeRingIndependentCoefficients J (integers J)) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})) ⋙ U)
    (eR : UR ⋙ (toSheaf (derivedChangeRingIndependentCoefficients K (residues K n)) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{r})) ≅
      (toSheaf (derivedChangeRingIndependentCoefficients J (residues J n)) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})) ⋙ U)
    (rho : restriction J n ⋙ UZ ≅ UR ⋙ restriction K n) :
    ∃ e : D.E ⋙ UR ≅ UZ ⋙ D'.E,
      (∀ A : Integral J,
        UZ.map ((sheafScalarOrdinaryAdjunction (projection J n) D).unit.app A) ≫
          rho.hom.app (D.E.obj A) ≫ (restriction K n).map (e.hom.app A) =
        (sheafScalarOrdinaryAdjunction (projection K n) D').unit.app (UZ.obj A)) ∧
      ∃ theta : D.T ⋙ UR.mapDerivedCategory ≅ UZ.mapDerivedCategory ⋙ D'.T,
        NatTrans.CommShift theta.hom ℤ ∧
        (∀ P : CochainComplex (Integral J) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := integers J) P →
          theta.hom.app (DerivedCategory.Q.obj P) ≫
            D'.T.map (UZ.mapDerivedCategoryFactors.hom.app P) ≫
            D'.ε.app ((UZ.mapHomologicalComplex (.up ℤ)).obj P) =
          UR.mapDerivedCategory.map (D.ε.app P) ≫
            UR.mapDerivedCategoryFactors.hom.app ((D.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) ∧
        ∀ (P : Presentation (J := J) n) (P' : Presentation (J := K) n)
          (f : P'.S ≅ UZ.mapShortComplex.obj P.S)
          (h : P'.H ≅ UR.obj P.H) (q : P'.Q ≅ UR.obj P.Q),
          P'.i ≫ f.hom.τ₁ = (restriction K n).map h.hom ≫
            rho.inv.app P.H ≫ UZ.map P.i →
          f.hom.τ₃ ≫ UZ.map P.p = P'.p ≫ (restriction K n).map q.hom ≫
            rho.inv.app P.Q →
          (UR.mapDerivedCategory.map (identifications n D hn P).alphaF.hom ≫
            (UR.mapDerivedCategorySingleFunctor 0).hom.app P.Q =
          theta.hom.app ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₃) ≫
            D'.T.map ((UZ.mapDerivedCategorySingleFunctor 0).hom.app P.S.X₃) ≫
            D'.T.map ((DerivedCategory.singleFunctor (Integral K) 0).map f.inv.τ₃) ≫
            (identifications n D' hn P').alphaF.hom ≫
            (DerivedCategory.singleFunctor (Residue K n) 0).map q.hom) ∧
          (UR.mapDerivedCategory.map (identifications n D hn P).alphaB.hom ≫
            (UR.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
              ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H) ≫
            ((UR.mapDerivedCategorySingleFunctor 0).hom.app P.H)⟦(1 : ℤ)⟧' =
          theta.hom.app ((DerivedCategory.singleFunctor (Integral J) 0).obj P.S.X₁) ≫
            D'.T.map ((UZ.mapDerivedCategorySingleFunctor 0).hom.app P.S.X₁) ≫
            D'.T.map ((DerivedCategory.singleFunctor (Integral K) 0).map f.inv.τ₁) ≫
            (identifications n D' hn P').alphaB.hom ≫
            ((DerivedCategory.singleFunctor (Residue K n) 0).map h.hom)⟦(1 : ℤ)⟧') ∧
          (UR.mapDerivedCategory.map (boundary n D hn P) ≫
            (UR.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
              ((DerivedCategory.singleFunctor (Residue J n) 0).obj P.H) ≫
            ((UR.mapDerivedCategorySingleFunctor 0).hom.app P.H)⟦(2 : ℤ)⟧' =
          (UR.mapDerivedCategorySingleFunctor 0).hom.app P.Q ≫
            (DerivedCategory.singleFunctor (Residue K n) 0).map q.inv ≫
            boundary n D' hn P' ≫
            ((DerivedCategory.singleFunctor (Residue K n) 0).map h.hom)⟦(2 : ℤ)⟧') := by
  sorry

end InverseImage

end DivisibleReduction
end SheafOfModules
