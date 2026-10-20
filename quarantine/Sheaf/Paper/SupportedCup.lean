/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.SupportedCohomologyHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Cup product with closed supports

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
def-pur-supported-cup, and its coefficient calculation in the DAG
(blueprint: def-pur-supported-cup).

The ordinary coefficient map is uniquely specified by restriction and multiplication of
constants. Its derived comparison uses the actual localization tensor comparison. The cup
product acts on the supported-Hom representatives from lem-pur-supported-hom. Its target is
a Hom group in the unbounded derived category, including when tensoring two bounded-below
inputs produces an unbounded complex.

## Main definitions

- `cupCoefficientRestriction`, `cupCoefficientMultiplication`, `cupCoefficientMap`: the
  normalized underived coefficient maps.
- `cupSingleTensorMap`, `cupDerivedCoefficientMap`: their canonical localization comparison.
- `cupTensorShiftIso`: the right-shift-first sign convention.
- `cupHasDerivedCategory`, `CupDerivedCategory`, `CupPlus`, `cupSingle`: shared references
  to the existing localization, bounded-below category, and degree-zero embedding.
- `cupMonoidal`, `cupTensorObject`: shared references to the upstream derived tensor.
- `cupSupportedHom`, `cupComposite`, `supportedCup`: the unbounded output group and cup composite.

## Main statements

- `cupCoefficientMap_existsUnique`, `cupCoefficientMap_isIso`, `cupCoefficient_flat`:
  the quotient and idempotent coefficient calculation attached to the node.
- `cupDerivedCoefficientMap_isIso`: degree-zero flatness identifies the derived coefficients.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u c v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- A named reference to the existing canonical localization structure, shared by all
occurrences below. This is the upstream instance, not a new localization.
Source: def-pur-supported-cup and def-weil-pbc-proetale-site
(blueprint: def-pur-supported-cup). -/
@[instance_reducible]
noncomputable def cupHasDerivedCategory (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  inferInstance

/-- The existing fixed-scalar derived category with its canonical structure explicitly
shared. Source: def-pur-supported-cup (blueprint: def-pur-supported-cup). -/
abbrev CupDerivedCategory (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  @DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    _ _ (cupHasDerivedCategory P X)

/-- The upstream derived monoidal structure, named once for this coefficient datum.
Source: def-pur-supported-cup, derived tensor (blueprint: def-pur-supported-cup). -/
@[instance_reducible]
noncomputable def cupMonoidal (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    MonoidalCategory (CupDerivedCategory P X) := inferInstance

/-- The object part of the existing derived tensor using the shared instance.
Source: def-pur-supported-cup (blueprint: def-pur-supported-cup). -/
noncomputable abbrev cupTensorObject (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (F G : CupDerivedCategory P X) : CupDerivedCategory P X :=
  ((@curriedTensor (CupDerivedCategory P X) _ (cupMonoidal P X)).obj F).obj G

/-- The existing bounded-below subcategory with that same shared localization.
Source: def-pur-supported-cup (blueprint: def-pur-supported-cup). -/
abbrev CupPlus (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  @DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    _ _ (cupHasDerivedCategory P X)

/-- The actual degree-zero embedding with the shared canonical localization structure.
Source: def-pur-supported-cup (blueprint: def-pur-supported-cup). -/
noncomputable def cupSingle (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) ⥤ CupDerivedCategory P X :=
  @DerivedCategory.singleFunctor _ _ _ (cupHasDerivedCategory P X) 0

/-- Compare the specified finite coefficient sheaf with the constant pro-etale sheaf.
Source: def-pur-supported-cup, coefficient calculation, and the constant-sheaf adjunction.
Both functors are left adjoint to evaluation at the terminal pro-etale object; uniqueness
of left adjoints gives the comparison preserving constant sections.
(blueprint: def-pur-supported-cup). -/
noncomputable def cupConstantIso (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) :
    P.constant X ≅ (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)).obj (ModuleCat.of P.Coefficient P.Coefficient) :=
  (comparisonUpperStarConstantSheafIso P.Coefficient X).app
    (ModuleCat.of P.Coefficient P.Coefficient)

/-- Restriction of the actual finite coefficient unit to a closed support. The map is
adjoint to the constant-presheaf sheafification unit at the base change of the terminal
object, so on local constants it restricts the same scalar.
Source: def-pur-supported-cup, the map q_D in the coefficient calculation
(blueprint: def-pur-supported-cup). -/
noncomputable def cupCoefficientRestriction (P : WeilConjectures.PurityFiniteSetting.{u})
    {D X : Scheme.{u}} (c : D ⟶ X) :
    P.constant X ⟶ (lowerStar (ModuleCat.{u + 1} P.Coefficient) c).obj (P.constant D) :=
  (cupConstantIso P X).hom ≫
    ((constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.ProEt.isTerminalMkId X)).homEquiv
      (ModuleCat.of P.Coefficient P.Coefficient)
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) c).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} P.Coefficient)).obj
          (ModuleCat.of P.Coefficient P.Coefficient)))).symm
        ((toSheafify (Scheme.ProEt.topology D)
          ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of P.Coefficient P.Coefficient))).app
            (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ c).obj
              (Scheme.ProEt.mk (𝟙 X))))) ≫
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) c).map (cupConstantIso P D).inv

/-- Multiplication on the specified coefficient sheaf, transported from the tensor unit.
Source: def-pur-supported-cup, multiplication of local constant functions
(blueprint: def-pur-supported-cup). -/
noncomputable def cupCoefficientMultiplication (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) : P.constant X ⊗ P.constant X ⟶ P.constant X :=
  (tensorIso (cupConstantIso P X) (cupConstantIso P X)).hom ≫
    (λ_ (𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)))).hom ≫ (cupConstantIso P X).inv

/-- The intersection immersion, with its scheme-theoretic pullback structure.
Source: def-pur-supported-cup, V=Z times_X W and h:V into X
(blueprint: def-pur-supported-cup). -/
noncomputable abbrev cupIntersection {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X) :
    pullback i j ⟶ X := pullback.fst i j ≫ i

/-- The coefficient multiplication map is uniquely determined by multiplying restrictions
of local constants. Source: def-pur-supported-cup, coefficient calculation
(blueprint: def-pur-supported-cup).

Proof: identify constant coefficients with locally constant functions, using the coproduct
of copies of X and fpqc representable descent. For a closed D, restriction q_D is locally
surjective: near each point of D a locally constant function is a constant, and on the open
complement it lifts by zero. Its kernel J_D consists of functions vanishing on D. Hence the
closed direct image is A_X/J_D. On V=Z times_X W one has J_V=J_Z+J_W: for t vanishing on V,
use the cover by X minus Z, X minus W, and the complement of the clopen nonzero locus of t.
The balanced tensor formulas give (A/J_Z) tensor (A/J_W)=A/(J_Z+J_W), sending a tensor b to ab.
They give the required map and the displayed equation. The tensor of the two epic quotient
maps is epic by right exactness, so that equation determines the map uniquely. -/
theorem cupCoefficientMap_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃! μ : (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ⊗
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W) ⟶
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
          (P.constant (pullback i j)),
      (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j) ≫ μ =
        cupCoefficientMultiplication P X ≫ cupCoefficientRestriction P (cupIntersection i j) := by
  sorry

/-- The specified underived map mu: restrict both factors to the intersection and multiply.
The unique characterization uses the quotient maps, so this selects no arbitrary map.
Source: def-pur-supported-cup, displayed coefficient map mu
(blueprint: def-pur-supported-cup). -/
noncomputable def cupCoefficientMap (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ⊗
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
        (P.constant (pullback i j)) :=
  (cupCoefficientMap_existsUnique P i j).exists.choose

/-- The coefficient map is invertible. Source: def-pur-supported-cup, coefficient calculation
(blueprint: def-pur-supported-cup).
Proof: the inverse of (A/J_Z) tensor (A/J_W) to A/(J_Z+J_W) sends the class of c to
c tensor 1. The balanced relations verify both inverse identities. Since J_V=J_Z+J_W,
the map so inverted is precisely the uniquely specified cupCoefficientMap. -/
theorem cupCoefficientMap_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] : IsIso (cupCoefficientMap P i j) := by
  sorry

/-- Flatness of each closed direct image of constants, without a geometric-stalk assumption.
Source: def-pur-supported-cup, idempotent argument for flatness
(blueprint: def-pur-supported-cup).
Proof: write the sheaf as A/J_D. For a finite list t_l in J_D the characteristic function e
of the union of their clopen nonzero loci belongs to J_D and satisfies e t_l=t_l. Tensoring
M with A/J_D is M/J_D M. If M injects into N and m dies in N/J_D N, locally m=sum t_l n_l.
Then (1-e)m=0 already in M, so m=e m belongs to J_D M. Thus quotient tensor preserves
monomorphisms; it is right exact by local lifting in quotient modules, hence exact. -/
theorem cupCoefficient_flat (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ObjectProperty.flat ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constant Z)) := by
  sorry

/-- The canonical degree-zero comparison, constructed before specializing the category.
Source: def-pur-supported-cup, the localization tensor comparison followed by the ordinary
single-complex comparison (blueprint: def-pur-supported-cup). -/
noncomputable def cupSingleTensorMap {C : Type c} [Category.{v} C] [Abelian C]
    [hD : HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    (L M : C) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
        (DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.singleFunctor C 0).obj (L ⊗ M) :=
  (tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app L)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M)).hom ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) L).app
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≪≫
        ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app M)).hom) ≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (L ⊗ M)).inv

/-- Apply a sheaf coefficient map after the canonical degree-zero tensor comparison.
The construction is made in a general category to keep the localization structure shared.
Source: def-pur-supported-cup, theta induced by mu (blueprint: def-pur-supported-cup). -/
noncomputable def cupDerivedCoefficientMap {C : Type c} [Category.{v} C] [Abelian C]
    [hD : HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    {L M N : C} (μ : L ⊗ M ⟶ N) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
        (DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.singleFunctor C 0).obj N :=
  cupSingleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map μ

/-- The derived coefficient comparison is invertible. Source: def-pur-supported-cup,
K-flat tensor descent (blueprint: def-pur-supported-cup).
Proof: cupCoefficient_flat makes each degree-zero supported coefficient K-flat: tensoring
an acyclic complex by an exact tensor functor preserves its kernels, images and cohomology.
Thus the localization tensor comparison in cupSingleTensorMap is invertible by
isIso_mu_Qh_of_kFlat and the quotient monoidal comparison. The single-complex comparison
is an isomorphism. Finally cupCoefficientMap_isIso inverts the remaining factor. -/
theorem cupDerivedCoefficientMap_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsIso (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
      (hDM := cupMonoidal P X) (cupCoefficientMap P i j)) := by
  sorry

/-- The right-shift-first comparison in a monoidal category with both tensor-shift
structures. On K-flat cochain representatives, its sign on P[a]^r tensor Q[b]^s is
(-1)^(b r). Source: def-pur-supported-cup, the sign-normalized shift comparison
(blueprint: def-pur-supported-cup). -/
noncomputable def cupTensorShiftIso {C : Type c} [Category.{v} C]
    [hM : MonoidalCategory C] [HasShift C ℤ]
    [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    (F G : C) (a b : ℤ) : F⟦a⟧ ⊗ G⟦b⟧ ≅ (F ⊗ G)⟦a + b⟧ :=
  (((curriedTensor C).obj (F⟦a⟧)).commShiftIso b).app G ≪≫
    (shiftFunctor C b).mapIso
      ((((curriedTensor C).flip.obj G).commShiftIso a).app F) ≪≫
    (shiftFunctorAdd C a b).symm.app _

/-- Supported groups for an arbitrary unbounded target, by the node's Hom convention.
For bounded-below targets supported_cohomology_hom identifies this with derived supported
sections. Source: def-pur-supported-cup, unbounded output convention
(blueprint: def-pur-supported-cup). -/
abbrev cupSupportedHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) (K : CupDerivedCategory P X) (r : ℤ) :=
  (cupSingle P X).obj
    ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ K⟦r⟧

/-- Compose the inverse coefficient comparison, tensor of representatives, and the
right-shift-first comparison. Source: def-pur-supported-cup, the displayed cup composite
(blueprint: def-pur-supported-cup). -/
noncomputable def cupComposite {C : Type c} [Category.{v} C]
    [hM : MonoidalCategory C] [HasShift C ℤ]
    [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    {L M N F G : C} (θ : L ⊗ M ⟶ N) (hθ : IsIso θ)
    (a b : ℤ) (α : L ⟶ F⟦a⟧) (β : M ⟶ G⟦b⟧) : N ⟶ (F ⊗ G)⟦a + b⟧ :=
  @inv _ _ _ _ θ hθ ≫ (α ⊗ₘ β) ≫ (cupTensorShiftIso F G a b).hom

/-- The supported cup product, on the supported-Hom representatives supplied by
supported_cohomology_hom. The inputs are bounded below, the integers a,b are arbitrary,
and the output uses the ambient unbounded derived category.
Source: blueprint main-20261015, def-pur-supported-cup, displayed composite
(blueprint: def-pur-supported-cup). -/
noncomputable def supportedCup (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
    (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (a b : ℤ) (α : cupSupportedHom P i F.obj a) (β : cupSupportedHom P j G.obj b) :
    cupSupportedHom P (cupIntersection i j)
      (cupTensorObject P X F.obj G.obj) (a + b) :=
  cupComposite (hM := cupMonoidal P X) (F := F.obj) (G := G.obj)
    (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
      (hDM := cupMonoidal P X) (cupCoefficientMap P i j))
    (cupDerivedCoefficientMap_isIso P i j) a b α β

end AlgebraicGeometry.ProEtale
