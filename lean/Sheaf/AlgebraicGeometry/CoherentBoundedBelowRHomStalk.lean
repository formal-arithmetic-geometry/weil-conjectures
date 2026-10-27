module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Homology.StalkTensorComplexDegrees
public import WeilConjectures.Algebra.Homology.StalkTensorComplexDifferential
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.AlgebraicGeometry.CoherentAffineFreeResolution
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import WeilConjectures.Algebra.Homology.DerivedHomFiniteFreeModel
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Homology.HomComplex

/-! # Derived stalk comparison for coherent sheaves and bounded-below complexes

Source: Stacks Project, cohomology.tex, Tag 0GM8 (lemma-stalk-internal-hom), case (2),
and perfect.tex, Tag 08E8 (lemma-identify-pseudo-coherent-noetherian).
(blueprint: lem-sfb-coherent-bounded-below-rhom-stalk).

The comparison is the adjunction transpose of stalked evaluation. The tensor
comparison is fixed by the pure-tensor germ formula on K-flat representatives.
The main theorem states its invertibility; the naturality theorem includes
precomposition by every endomorphism of the coherent first argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.SingleComplexBaseChange

namespace AlgebraicGeometry

/-- Canonical tensor map on module stalks, fixed by its pure-tensor germ formula.
Source: Stacks 01CB and 0GM8 (blueprint: lem-sfb-coherent-bounded-below-rhom-stalk). -/
def rhomStalkTensorSheafIso (X : Scheme.{u}) (x : X) :=
  Classical.choose (SheafOfModules.stalkTensorIso X.toRingedSpace x)

/-- The coproduct comparison in each total-tensor degree, with the canonical
pure-tensor comparison on every summand. The injection equations uniquely fix it.
Source: Stacks 06YB and 0GM8 (blueprint: lem-sfb-coherent-bounded-below-rhom-stalk). -/
def rhomStalkTensorDegreeIso (X : Scheme.{u}) (x : X) :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  Classical.choose (CochainComplex.exists_stalk_tensor_degree_iso X.toRingedSpace x
    (rhomStalkTensorSheafIso X x))

/-- Assembly of the existing degree comparisons using their differential compatibility.
No chain-map data are chosen from an unconstrained existence assertion.
Source: Stacks 06YB and 0GM8 (blueprint: lem-sfb-coherent-bounded-below-rhom-stalk). -/
def rhomStalkTensorComplexIso (X : Scheme.{u}) (x : X)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  HomologicalComplex.Hom.isoOfComponents (rhomStalkTensorDegreeIso X x P N)
    (fun n m _ ↦ CochainComplex.stalk_tensor_degree_differential X.toRingedSpace x
      (rhomStalkTensorSheafIso X x)
      (Classical.choose_spec (SheafOfModules.stalkTensorIso X.toRingedSpace x)).2
      (rhomStalkTensorDegreeIso X x)
      (Classical.choose_spec (CochainComplex.exists_stalk_tensor_degree_iso X.toRingedSpace x
        (rhomStalkTensorSheafIso X x))) P N n m)

/-- The unique derived tensor comparison for the exact stalk functor. Its normalization
uses the actual localization tensor map and the termwise pure-tensor germ comparison.
Source: Stacks 06YB, 0GM8 and the flat-point case of lemma-pullback-internal-hom
(blueprint: lem-sfb-coherent-bounded-below-rhom-stalk).
Proof: Stalks are exact by lem-weil-pbc-module-stalk-exact and preserve K-flatness
by the stalk criterion. On K-flat representatives apply the canonical tensor-complex
comparison, whose summand equations take the germ of a pure tensor to the tensor of
germs. The localization tensor map is invertible on those representatives. Conjugate
by mapDerivedCategoryFactors to obtain the displayed normalized family. Naturality
of the summand maps and localization gives naturality on derived objects. Every
object has a K-flat representative, so the normalization and naturality determine
the family uniquely, including on all morphisms. -/
theorem exists_rhomStalkTensorComparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] (x : X) :
    ∃! μ : ∀ K L : schemeDerivedCategory X,
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.obj K ⊗
        (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.obj L ⟶
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.obj (K ⊗ L),
      (∀ (K L K' L' : schemeDerivedCategory X) (f : K ⟶ K') (g : L ⟶ L'),
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.map f ⊗ₘ
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.map g) ≫
            μ K' L' = μ K L ≫
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.map (f ⊗ₘ g)) ∧
      (∀ (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        μ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.map
            (pullbackTensorModelMap X P N) ≫
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategoryFactors.hom.app
            (pullbackTensorTotal X P N) ≫
          DerivedCategory.Q.map (rhomStalkTensorComplexIso X x P N).hom =
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategoryFactors.hom.app P ⊗ₘ
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategoryFactors.hom.app N) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
            (.up ℤ)).obj P)
          (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
            (.up ℤ)).obj N)) := by
  sorry

/-- The derived tensor comparison determined uniquely by its representative equation.
Source: Stacks 06YB and 0GM8 (blueprint: lem-sfb-coherent-bounded-below-rhom-stalk). -/
def rhomStalkTensorComparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] (x : X) :=
  Classical.choose (exists_rhomStalkTensorComparison X x)

/-- The canonical derived stalk-Hom comparison: transpose the stalk of evaluation,
using the canonical derived tensor comparison. The symmetry places the Hom argument
on the left, as required by the ordinary-module closed adjunction.
Source: Stacks 0GM8, via lemma-pullback-internal-hom
(blueprint: lem-sfb-coherent-bounded-below-rhom-stalk). -/
def derivedInternalHomStalkComparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (x : X) (K L : schemeDerivedCategory X) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.obj
      ((derivedInternalHom (Opens.grothendieckTopology X)
        X.sheaf).obj (op K, L)) ⟶
    (ordinaryModuleDerivedInternalHom (X.presheaf.stalk x)).obj
      (op ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.obj K),
        (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.obj L) :=
  letI := DerivedCategory.braidedCategory' (ModuleCat.{u} (X.presheaf.stalk x))
  MonoidalClosed.curry ((β_ _ _).hom ≫
    rhomStalkTensorComparison X x
      ((derivedInternalHom (Opens.grothendieckTopology X)
        X.sheaf).obj (op K, L)) K ≫
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.map
      (schemeDerivedTensorHomEquiv X
        ((derivedInternalHom (Opens.grothendieckTopology X)
          X.sheaf).obj (op K, L)) K L (𝟙 _)))

/-- Naturality of the canonical comparison, contravariantly in the first derived
argument and covariantly in the second. Taking f to be a degree-zero endomorphism
is exactly the precomposition compatibility required by the node.
Source: Stacks 0GM8 and lemma-pullback-internal-hom
(blueprint: lem-sfb-coherent-bounded-below-rhom-stalk).
Proof: Uncurry both sides. Naturality of the canonical tensor comparison and of
schemeDerivedTensorHomEquiv reduces the square to evaluation after precomposition
and postcomposition. On representatives both sides send v, h, u to v(h(u(-))).
The stalk functor preserves composition and localization preserves the square.
The tensor-Hom bijection then gives the claimed equality. -/
theorem derivedInternalHomStalkComparison_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (x : X) (K K' L L' : schemeDerivedCategory X) (f : K' ⟶ K) (g : L ⟶ L') :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.map
      ((derivedInternalHom (Opens.grothendieckTopology X)
        X.sheaf).map (f.op, g)) ≫ derivedInternalHomStalkComparison X x K' L' =
    derivedInternalHomStalkComparison X x K L ≫
      (ordinaryModuleDerivedInternalHom (X.presheaf.stalk x)).map
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.map f).op,
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory.map g) := by
  sorry

/-- The derived stalk comparison is invertible for a coherent sheaf and any
cohomologically bounded-below target, without quasi-coherence of that target.
Source: Stacks 0GM8(2), lemma-stalk-internal-hom; perfect.tex 08E8
(blueprint: lem-sfb-coherent-bounded-below-rhom-stalk).
Proof:
1. Choose a lower cohomology bound a and good-truncate a representative of E at a
(def-kun-truncations). This gives a termwise bounded-below representative.
2. Choose an affine neighbourhood of x and a bounded-above finite-free resolution
P of F (lem-sc-coherent-affine-free-resolution). Restriction commutes with RHom
(lem-sc-derived-internal-hom-restrict-open); opens containing x inside this
neighbourhood are cofinal among all neighbourhoods of x.
3. Compute RHom by Hom(P,G) on this neighbourhood and by Hom(P_x,G_x) on the
one-point ringed space (lem-sc-derived-hom-finite-free-model). Exactness of stalks
preserves both quasi-isomorphisms (lem-weil-pbc-module-stalk-exact).
4. In degree n, only a-n ≤ p ≤ b contribute to the Hom product. Finite freeness
identifies each stalk of sheaf Hom with module Hom, and stalks commute with this
finite product. Germ evaluation commutes with d_G f - (-1)^n f d_P, so these
comparisons give an isomorphism of complexes (def-pur-hom-complex).
5. The transpose definition of the comparison has precisely this germ-evaluation
formula on these models. Replacement maps are inverted by the existing derived
Hom functor (def-pur-derived-internal-hom). Thus the canonical comparison itself
is invertible. Its naturality theorem includes precomposition by every
endomorphism of F. -/
theorem isIso_derivedInternalHomStalkComparison_of_coherent_boundedBelow
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (_hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (E : schemeDerivedCategory X) (_hE : ∃ a : ℤ, E.IsGE a) (x : X) :
    IsIso (derivedInternalHomStalkComparison X x
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) E) := by
  sorry

end AlgebraicGeometry
