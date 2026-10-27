/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.OrdinaryLineScalarData

/-! # Evaluation compatibility of the scalar and line comparison

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0G7E and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t a w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
namespace SheafOfModules.OrdinaryLineScalar
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
variable {X : Scheme.{t}} [EssentiallySmall.{max a (t + 1)} X.ProEt]
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
variable {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}

/-- Evaluation is preserved by any representative-normalized scalar comparison.
Source: blueprint Tate-twist local freeness proof (3); Stacks 07A4 and 06YU.
(blueprint: lem-pur-ordinary-line-scalar-evaluation).
Proof: choose a flat-term K-flat representative P of the derived input. Both line
tensors and scalar extension preserve this class. Substitute the representative
squares for m and -m and the two epsilon_computed equations. The remaining equality
is the ordinary chain evaluation square. On generators its two paths send
((x tensor y) tensor z) tensor s to x tensor s alpha(ev(y,z)).
To check the ordinary square, work on a covering slice trivializing L. Transport
its basis through b to the scalar-extended basis of K, and take the recorded signed
basis powers e_n and f_n. The hypothesis hB sends 1 tensor e_n to f_n; the two
evaluation_basis equations send e_m tensor e_-m and f_m tensor f_-m to 1.
For multiples a e_m and c e_-m, bilinearity gives a*c and alpha(a)*alpha(c),
respectively, so the displayed generator formulas agree. This includes n=0 and
negative n with the actual dual basis. Restriction naturality, sheaf separatedness
and the balanced tensor universal property prove equality without asserting global
pure-tensor generation of sheaf sections. Localization transports the square to Q(P);
naturality along
the resolution isomorphism extends it to every derived object. -/
theorem ordinary_scalar_line_evaluation
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (L : Modules.{t, a} X R) (K : Modules.{t, a} X S)
    [L.IsFiniteLocallyFreeOfRank 1] [K.IsFiniteLocallyFreeOfRank 1]
    (B : ∀ m : ℤ, changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α (power.{t, a} L m) ≅ power.{t, a} K m)
    (l : LineData L) (k : LineData K)
    (b : changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α L ≅ K)
    (hB : SignedLineComparisonNormalized.{t + 1, t, a} α L K b B)
    (o : ∀ m : ℤ, tensor.{t, a} L m ⋙ p.ordinary ≅
      p.ordinary ⋙ tensor.{t, a} K m)
    (ho : ∀ (m : ℤ) (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U) (y : (power.{t, a} L m).val.obj U) (s : S.obj.obj U),
      ((o m).hom.app M).val.app U
        (scalar.{t, a, w} p ((tensor.{t, a} L m).obj M) U s
          (LineUnbounded.pureTensor.{t, a} X R M (power.{t, a} L m) U x y)) =
      LineUnbounded.pureTensor.{t, a} X S (p.ordinary.obj M) (power.{t, a} K m) U
        (scalar.{t, a, w} p M U s x)
        ((B m).hom.val.app U (scalarExtensionSection α (power.{t, a} L m) U 1 y)))
    (d : ∀ m : ℤ, twist.{t, a, w} L m ⋙ p.derived ≅
      p.derived ⋙ twist.{t, a, w} K m)
    (hd : ∀ (m : ℤ) (P : CochainComplex (Modules.{t, a} X R) ℤ), FlatModel P →
      (d m).hom.app (𝒬[R].obj P) ≫
        (twist.{t, a, w} K m).map (compute.{t, a, w} p P) ≫
        (k.factors m).hom.app ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
      p.derived.map ((l.factors m).hom.app P) ≫
        compute.{t, a, w} p (((tensor.{t, a} L m).mapHomologicalComplex (.up ℤ)).obj P) ≫
        𝒬[S].map ((Functor.mapHomologicalComplexCompIso (o m) (.up ℤ)).hom.app P)) :
    ∀ (m : ℤ) (Y : DerivedCategory (Modules.{t, a} X R)),
      (d (-m)).hom.app ((twist.{t, a, w} L m).obj Y) ≫
        (twist.{t, a, w} K (-m)).map ((d m).hom.app Y) ≫
        (k.epsilon m).hom.app (p.derived.obj Y) =
      p.derived.map ((l.epsilon m).hom.app Y) := by sorry

end SheafOfModules.OrdinaryLineScalar
