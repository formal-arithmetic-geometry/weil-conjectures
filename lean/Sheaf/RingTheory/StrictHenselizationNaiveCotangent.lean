module

public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.RingTheory.PointedEtaleFiltered
import Mathlib.RingTheory.Etale.Basic
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.IndEtaleNaiveCotangentAcyclic
import WeilConjectures.RingTheory.JacobiZariskiHomologySequence
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Strict henselization and the naive cotangent complex

Source: Stacks Project, More on Algebra, Tag 0D08, lemma-henselization-NL,
strict-henselization clause
(blueprint: lem-sfb-strict-henselization-naive-cotangent).

The cone of a degree-zero single map is the two-term complex in degrees -1,0.
Base changing its differential means ordinary termwise tensor product. The two
component equations specify the canonical chain map on both nonzero terms;
they identify the derived isomorphism with the square-induced comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v t w

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- The square-induced naive cotangent comparison for strict henselizations is
an isomorphism in the derived category. The component equations use the existing
canonical polynomial presentation map, hence send conormal classes to their
polynomial images and differential symbols to the corresponding symbols.
Source: Stacks Project, More on Algebra, Tag 0D08, lemma-henselization-NL
(blueprint: lem-sfb-strict-henselization-naive-cotangent).

Proof for stage 3:
1. The pointed-etale diagrams of def-sc-ring-strict-henselization are filtered by
lem-sc-pointed-etale-filtered. Their terms are finitely presented by
lem-weil-pbc-etale-algebra-finite-presentation-localization. Thus both structural
maps A → As and B → Bs are ind-etale (def-weil-pbc-ind-etale-algebra).
By lem-sfb-ind-etale-naive-cotangent-acyclic their naive cotangent differentials
are invertible. The first remains invertible after ordinary tensor with Bs.
The cokernel identifications of
lem-weil-pbc-naive-cotangent-complex-cokernel-kahler give the required vanishing
of relative differentials as well as degree minus one homology.
2. Apply lem-weil-pbc-jacobi-zariski-homology-sequence to A → As → Bs.
The first and fourth terms vanish, so the coefficient-change comparison is an
isomorphism in degrees -1,0.
3. Apply that sequence to A → B → Bs. The zero H1(Bs/B) gives surjectivity
on degree minus one. lem-sfb-ind-etale-jacobi-zariski-left-injective gives
injectivity. On degree zero, the same sequence identifies differentials, and
lem-weil-pbc-naive-cotangent-complex-cokernel-kahler with
lem-weil-pbc-tensor-right-exact identifies them with the cokernels after tensor.
No interchange of degree minus one homology with tensor is used.
4. Compose the two comparisons. On polynomials this fixes the prescribed image
of coefficients and sends X_b to X_(image b). The existing Cotangent.map and
CotangentSpace.map give precisely its two components after tensor extension,
as expressed below. It is an isomorphism on cohomology in degrees -1,0 and all
other cohomology vanishes. The localization def-weil-abstract-derived-category
therefore inverts this chain map, giving the displayed derived isomorphism. -/
theorem strictHenselization_naiveCotangent_iso
    {A : Type u} {B : Type v} {KA KB As Bs : Type (max u v t)}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Field KA] [Field KB]
    [Algebra (IsLocalRing.ResidueField A) KA]
    [IsSepClosure (IsLocalRing.ResidueField A) KA]
    [Algebra (IsLocalRing.ResidueField B) KB]
    [IsSepClosure (IsLocalRing.ResidueField B) KB]
    [Algebra A KA] [IsScalarTower A (IsLocalRing.ResidueField A) KA]
    [Algebra B KB] [IsScalarTower B (IsLocalRing.ResidueField B) KB]
    [CommRing As] [CommRing Bs] [IsLocalRing As] [IsLocalRing Bs]
    [Algebra A As] [Algebra B Bs] [Algebra As Bs] [Algebra A Bs]
    [IsScalarTower A B Bs] [IsScalarTower A As Bs]
    [IsLocalHom (algebraMap As Bs)]
    (PA : StrictHenselizationPresentationIn.{u, max v t} A KA As)
    (PB : StrictHenselizationPresentationIn.{v, max u t} B KB Bs)
    (i : KA →+* KB)
    (hi : i.comp (algebraMap (IsLocalRing.ResidueField A) KA) =
      (algebraMap (IsLocalRing.ResidueField B) KB).comp
        (IsLocalRing.ResidueField.map (algebraMap A B)))
    (hres : PB.residueMap.comp (algebraMap As Bs) = i.comp PA.residueMap)
    [HasDerivedCategory.{w} (ModuleCat.{max u v t} Bs)] :
    ∃ e : DerivedCategory.Q.obj (CochainComplex.mappingCone
        ((HomologicalComplex.single (ModuleCat.{max u v t} Bs) (.up ℤ) 0).map
          (ModuleCat.ofHom
            ((Generators.self A B).toExtension.cotangentComplex.baseChange Bs)))) ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone
          ((HomologicalComplex.single (ModuleCat.{max u v t} Bs) (.up ℤ) 0).map
            (ModuleCat.ofHom (Generators.self As Bs).toExtension.cotangentComplex))),
      ∃ f : CochainComplex.mappingCone
          ((HomologicalComplex.single (ModuleCat.{max u v t} Bs) (.up ℤ) 0).map
            (ModuleCat.ofHom
              ((Generators.self A B).toExtension.cotangentComplex.baseChange Bs))) ⟶
          CochainComplex.mappingCone
            ((HomologicalComplex.single (ModuleCat.{max u v t} Bs) (.up ℤ) 0).map
              (ModuleCat.ofHom (Generators.self As Bs).toExtension.cotangentComplex)),
        DerivedCategory.Q.map f = e.hom ∧
        (CochainComplex.mappingCone.inl
          ((HomologicalComplex.single (ModuleCat.{max u v t} Bs) (.up ℤ) 0).map
            (ModuleCat.ofHom
              ((Generators.self A B).toExtension.cotangentComplex.baseChange Bs)))).v
            0 (-1) rfl ≫ f.f (-1) =
          ModuleCat.ofHom (LinearMap.liftBaseChange Bs
            (Extension.Cotangent.map
              (Generators.defaultHom (Generators.self A B)
                (Generators.self As Bs)).toExtensionHom)) ≫
          (CochainComplex.mappingCone.inl
            ((HomologicalComplex.single (ModuleCat.{max u v t} Bs) (.up ℤ) 0).map
              (ModuleCat.ofHom (Generators.self As Bs).toExtension.cotangentComplex))).v
                0 (-1) rfl ∧
        (CochainComplex.mappingCone.inr
          ((HomologicalComplex.single (ModuleCat.{max u v t} Bs) (.up ℤ) 0).map
            (ModuleCat.ofHom
              ((Generators.self A B).toExtension.cotangentComplex.baseChange Bs)))).f 0 ≫ f.f 0 =
          ModuleCat.ofHom (LinearMap.liftBaseChange Bs
            (Extension.CotangentSpace.map
              (Generators.defaultHom (Generators.self A B)
                (Generators.self As Bs)).toExtensionHom)) ≫
          (CochainComplex.mappingCone.inr
            ((HomologicalComplex.single (ModuleCat.{max u v t} Bs) (.up ℤ) 0).map
              (ModuleCat.ofHom (Generators.self As Bs).toExtension.cotangentComplex))).f 0 := by
  sorry

end Algebra
