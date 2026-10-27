module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.TraceFormula.OnePointDerivedRingIdentification
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import WeilConjectures.AlgebraicGeometry.FreeComplexMapsToResolution
import Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal

/-!
# Derived module tensor exchange over a flat algebra

Source: Stacks Project, `more-algebra.tex`, Tag 0661, and
`examples-defos.tex`, Tag 0DZ2 (blueprint: lem-sfb-flat-algebra-derived-module-tensor-exchange).
-/

@[expose] public section

set_option autoImplicit false

universe u wR wS

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- Derived tensor exchange over a flat algebra, including the canonical normalization,
naturality, augmentation compatibility, and restriction of scalars.

Source: Stacks Project, `more-algebra.tex`, Tag 0661 (lemma-base-change-comparison),
and `examples-defos.tex`, Tag 0DZ2 (lemma-lift-equivalence-module), its free-resolution
footnote (blueprint: lem-sfb-flat-algebra-derived-module-tensor-exchange).

Proof:
1. Put G = S tensor_R F and M = S tensor_R N[0]. Flat tensor exactness
   (lem-weil-pbc-flat-tensor-exact) makes the extended augmentation G -> M a
   quasi-isomorphism. Extend a basis degreewise by 1 tensor f_i. Free modules are
   flat because their tensor functors are direct sums of copies of the identity.
   Thus F and G are bounded above with flat terms, so both are K-flat by
   lem-pc-module-bounded-flat-kflat. No condition on K is needed.
2. Balancing sends x tensor f to x tensor (1 tensor f), with inverse
   x tensor (s tensor f) mapping to sx tensor f. These maps are S-linear, commute
   with each differential, and preserve bidegrees. They therefore induce b on
   direct-sum total complexes, characterized by the displayed summand equation.
3. Use lem-trf-one-point-derived-ring-identification and the localization
   tensorator of lem-sf-ringed-derived-native-tensor. Its component at (K,G) is
   invertible because G is K-flat. Define alpha as Q(b), followed by its inverse
   tensorator, followed by 1 tensor Q(G -> M). The first equation specifies this
   canonical construction without an arbitrary choice of an isomorphism.
   Restriction is exact on underlying abelian groups and commutes with Q. The
   same comparison over R with F identifies the restricted source with
   Res(QK) tensor-derived_R N[0].
4. Balancing and the tensorator are natural. For augmented maps t over v, the
   square for alpha follows from t followed by epsilon' = epsilon followed by v.
   Lifts of every v exist by lem-weil-pbc-free-complex-maps-to-resolution and are
   unique up to homotopy by new-t4-augmented-resolution-lift-homotopy, since free
   modules are projective. Total tensor preserves these homotopies by
   lem-sfb-total-tensor-homotopy. Taking v to be the identity proves independence
   of resolution; arbitrary v gives naturality in N.
5. Tensorator naturality for G -> M cancels the inverse tensorator in alpha.
   The remaining chain composite is x tensor f mapping to x tensor epsilon(f).
   This is the displayed augmentation equation, written after the balancing
   isomorphism b. Its inverse yields the orientation in the node. All sums use
   finite-support elements, even for unbounded K and infinite free bases.
-/
theorem flat_algebra_derived_module_tensor_exchange
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (_hf : RingHom.Flat f)
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{u} S)] :
    ∃ b : ∀ (K : CochainComplex (ModuleCat.{u} S) ℤ)
        (F : CochainComplex (ModuleCat.{u} R) ℤ),
      ((ModuleCat.mixedTotalTensor f).obj K).obj F ≅
        K ⊗ (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj F),
      (∀ (K : CochainComplex (ModuleCat.{u} S) ℤ)
          (F : CochainComplex (ModuleCat.{u} R) ℤ) (p q n : ℤ) (h : p + q = n),
        CochainComplex.ιMapBifunctor K F (ModuleCat.mixedTensor f) p q n h ≫
            (b K F).hom.f n =
          CochainComplex.ιMapBifunctor K
            (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj F)
            (curriedTensor (ModuleCat.{u} S)) p q n h) ∧
      ∃ α : ∀ (K : CochainComplex (ModuleCat.{u} S) ℤ) (N : ModuleCat.{u} R)
          (F : CochainComplex (ModuleCat.{u} R) ℤ)
          (ε : F ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N),
          (∀ i : ℤ, Module.Free R (F.X i)) →
          (∀ i : ℤ, 0 < i → IsZero (F.X i)) → QuasiIso ε →
        (DerivedCategory.Q.obj (((ModuleCat.mixedTotalTensor f).obj K).obj F) ≅
          DerivedCategory.Q.obj K ⊗
            DerivedCategory.Q.obj
              (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj
                ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N))),
        (∀ (K : CochainComplex (ModuleCat.{u} S) ℤ) (N : ModuleCat.{u} R)
            (F : CochainComplex (ModuleCat.{u} R) ℤ)
            (ε : F ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N)
            (hfree : ∀ i : ℤ, Module.Free R (F.X i))
            (hbound : ∀ i : ℤ, 0 < i → IsZero (F.X i)) (hres : QuasiIso ε),
          Functor.LaxMonoidal.μ (DerivedCategory.Q (C := ModuleCat.{u} S)) K
              (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj F) ≫
              DerivedCategory.Q.map (b K F).inv ≫
              (α K N F ε hfree hbound hres).hom =
            𝟙 (DerivedCategory.Q.obj K) ⊗ₘ
              DerivedCategory.Q.map
                (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map ε)) ∧
        (∀ (K K' : CochainComplex (ModuleCat.{u} S) ℤ) (N N' : ModuleCat.{u} R)
            (F F' : CochainComplex (ModuleCat.{u} R) ℤ)
            (ε : F ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N)
            (ε' : F' ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N')
            (hfree : ∀ i : ℤ, Module.Free R (F.X i))
            (hfree' : ∀ i : ℤ, Module.Free R (F'.X i))
            (hbound : ∀ i : ℤ, 0 < i → IsZero (F.X i))
            (hbound' : ∀ i : ℤ, 0 < i → IsZero (F'.X i))
            (hres : QuasiIso ε) (hres' : QuasiIso ε')
            (a : K ⟶ K') (v : N ⟶ N') (t : F ⟶ F'),
          t ≫ ε' = ε ≫ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map v →
          DerivedCategory.Q.map
              (((ModuleCat.mixedTotalTensor f).map a).app F ≫
                ((ModuleCat.mixedTotalTensor f).obj K').map t) ≫
              (α K' N' F' ε' hfree' hbound' hres').hom =
            (α K N F ε hfree hbound hres).hom ≫
              (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map
                (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
                  ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map v)))) ∧
        (∀ (K : CochainComplex (ModuleCat.{u} S) ℤ) (N : ModuleCat.{u} R)
            (F : CochainComplex (ModuleCat.{u} R) ℤ)
            (ε : F ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N)
            (hfree : ∀ i : ℤ, Module.Free R (F.X i))
            (hbound : ∀ i : ℤ, 0 < i → IsZero (F.X i)) (hres : QuasiIso ε),
          (α K N F ε hfree hbound hres).hom ≫
              Functor.LaxMonoidal.μ (DerivedCategory.Q (C := ModuleCat.{u} S)) K
                (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj
                  ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N)) =
            DerivedCategory.Q.map
              (((ModuleCat.mixedTotalTensor f).obj K).map ε ≫
                (b K ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N)).hom)) ∧
        (∀ (K : CochainComplex (ModuleCat.{u} S) ℤ) (N : ModuleCat.{u} R)
            (F : CochainComplex (ModuleCat.{u} R) ℤ)
            (ε : F ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N),
          (∀ i : ℤ, Module.Free R (F.X i)) →
          (∀ i : ℤ, 0 < i → IsZero (F.X i)) → QuasiIso ε →
          Nonempty
            ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
                (DerivedCategory.Q.obj (((ModuleCat.mixedTotalTensor f).obj K).obj F)) ≅
              (ModuleCat.restrictScalars f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K) ⊗
                DerivedCategory.Q.obj
                  ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj N))) := by
  sorry

end CategoryTheory
