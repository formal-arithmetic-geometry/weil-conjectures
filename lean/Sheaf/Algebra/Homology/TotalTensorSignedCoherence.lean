/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.LargeSetSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-! # Signed coherence of total cochain tensors

Source: Stacks Project, Tag 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory WeilConjectures
namespace CategoryTheory.RingedDerivedNative

section Formulas

universe uA vA
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A]
  [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
  [∀ X : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
  [∀ X : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
  [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

/-- The canonical extraction of two integer shifts, second factor first.
Source: Stacks 0FPQ and More on Algebra, item-shift-tensor, with shifted-degree normalization
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorShiftIso (E F : CochainComplex A ℤ) (a b : ℤ) :
    (E⟦a⟧) ⊗ (F⟦b⟧) ≅ (E ⊗ F)⟦a + b⟧ :=
  CochainComplex.mapBifunctorShift₂Iso (E⟦a⟧) F (curriedTensor _) b ≪≫
    (shiftFunctor _ b).mapIso (CochainComplex.mapBifunctorShift₁Iso E F (curriedTensor _) a) ≪≫
    ((shiftFunctorAdd _ a b).app (E ⊗ F)).symm

/-- The prescribed shifted-degree formula for a map extracting two shifts.
Source: Stacks 0FPQ and More on Algebra, item-shift-tensor, shifted-degree normalization
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorShiftFormula (E F : CochainComplex A ℤ) (a b : ℤ)
    (f : (E⟦a⟧) ⊗ (F⟦b⟧) ⟶ (E ⊗ F)⟦a + b⟧) : Prop :=
  ∀ (p q n : ℤ) (h : p + q = n) (h' : (p + a) + (q + b) = n + (a + b)),
    HomologicalComplex.ιTensorObj (E⟦a⟧) (F⟦b⟧) p q n h ≫ f.f n =
      (b * p).negOnePow •
        HomologicalComplex.ιTensorObj E F (p + a) (q + b) (n + (a + b)) h'

/-- The unsigned reassociation formula, as a predicate on an arbitrary chain map.
Source: Stacks 0FPQ, associativity hint
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorAssociatorFormula (E F G : CochainComplex A ℤ)
    (f : (E ⊗ F) ⊗ G ⟶ E ⊗ (F ⊗ G)) : Prop :=
  ∀ (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n),
    (HomologicalComplex.ιTensorObj E F p q pq hpq ▷ G.X r) ≫
      HomologicalComplex.ιTensorObj (E ⊗ F) G pq r n hn ≫ f.f n =
    (α_ (E.X p) (F.X q) (G.X r)).hom ≫
      (E.X p ◁ HomologicalComplex.ιTensorObj F G q r qr hqr) ≫
      HomologicalComplex.ιTensorObj E (F ⊗ G) p qr n hn'

/-- The Koszul symmetry formula, as a predicate on an arbitrary chain map.
Source: Stacks 0FPQ and More on Algebra, item-flip-tensor-product
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorSymmetryFormula (E F : CochainComplex A ℤ)
    (f : E ⊗ F ⟶ F ⊗ E) : Prop :=
  ∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
    HomologicalComplex.ιTensorObj E F p q n h ≫ f.f n =
      (p * q).negOnePow • ((β_ (E.X p) (F.X q)).hom ≫
        HomologicalComplex.ιTensorObj F E q p n h')

/-- The shift formula clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_shift_formula : Prop :=
  ∀ (E F : CochainComplex A ℤ) (a b : ℤ),
  totalTensorShiftFormula (A := A) E F a b (totalTensorShiftIso (A := A) E F a b).hom

/-- The associator formula clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associator_formula : Prop :=
  ∀ (E F G : CochainComplex A ℤ),
  totalTensorAssociatorFormula (A := A) E F G (α_ E F G).hom

/-- The symmetry formula clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_formula : Prop :=
  ∀ (E F : CochainComplex A ℤ),
  totalTensorSymmetryFormula (A := A) E F (β_ E F).hom

/-- The shift inverse clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_shift_inverse : Prop :=
  ∀ (E F : CochainComplex A ℤ) (a b p q n : ℤ)
    (h : p + q = n) (h' : (p + a) + (q + b) = n + (a + b)),
    HomologicalComplex.ιTensorObj E F (p + a) (q + b) (n + (a + b)) h' ≫
      (totalTensorShiftIso (A := A) E F a b).inv.f n =
    (b * p).negOnePow • HomologicalComplex.ιTensorObj (E⟦a⟧) (F⟦b⟧) p q n h

/-- The associator inverse clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associator_inverse : Prop :=
  ∀ (E F G : CochainComplex A ℤ)
    (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
    (hn : pq + r = n) (hn' : p + qr = n),
    (E.X p ◁ HomologicalComplex.ιTensorObj F G q r qr hqr) ≫
      HomologicalComplex.ιTensorObj E (F ⊗ G) p qr n hn' ≫ (α_ E F G).inv.f n =
    (α_ (E.X p) (F.X q) (G.X r)).inv ≫
      (HomologicalComplex.ιTensorObj E F p q pq hpq ▷ G.X r) ≫
      HomologicalComplex.ιTensorObj (E ⊗ F) G pq r n hn

/-- The symmetry inverse clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_inverse : Prop :=
  ∀ (E F : CochainComplex A ℤ),
  (β_ E F).inv = (β_ F E).hom

/-- The shift natural clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_shift_natural : Prop :=
  ∀ (E E' F F' : CochainComplex A ℤ)
  (f : E ⟶ E') (g : F ⟶ F') (a b : ℤ),
  ((f⟦a⟧') ⊗ₘ (g⟦b⟧')) ≫ (totalTensorShiftIso (A := A) E' F' a b).hom =
    (totalTensorShiftIso (A := A) E F a b).hom ≫ (f ⊗ₘ g)⟦a + b⟧'

/-- The associator natural clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associator_natural : Prop :=
  ∀ (E E' F F' G G' : CochainComplex A ℤ)
  (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G'),
  ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ E' F' G').hom = (α_ E F G).hom ≫ (f ⊗ₘ (g ⊗ₘ h))

/-- The symmetry natural clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_natural : Prop :=
  ∀ (E E' F F' : CochainComplex A ℤ)
  (f : E ⟶ E') (g : F ⟶ F'),
  (f ⊗ₘ g) ≫ (β_ E' F').hom = (β_ E F).hom ≫ (g ⊗ₘ f)

/-- The shift unique clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_shift_unique : Prop :=
  ∀ (E F : CochainComplex A ℤ) (a b : ℤ)
  (f : (E⟦a⟧) ⊗ (F⟦b⟧) ⟶ (E ⊗ F)⟦a + b⟧),
  totalTensorShiftFormula (A := A) E F a b f →
    f = (totalTensorShiftIso (A := A) E F a b).hom

/-- The associator unique clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associator_unique : Prop :=
  ∀ (E F G : CochainComplex A ℤ)
  (f : (E ⊗ F) ⊗ G ⟶ E ⊗ (F ⊗ G)),
  totalTensorAssociatorFormula (A := A) E F G f → f = (α_ E F G).hom

/-- The symmetry unique clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_unique : Prop :=
  ∀ (E F : CochainComplex A ℤ)
  (f : E ⊗ F ⟶ F ⊗ E), totalTensorSymmetryFormula (A := A) E F f → f = (β_ E F).hom

/-- The associativity clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associativity : Prop :=
  ∀ (E F G : CochainComplex A ℤ) (a b d : ℤ),
  ((totalTensorShiftIso (A := A) E F a b).hom ▷ (G⟦d⟧)) ≫
      (totalTensorShiftIso (A := A) (E ⊗ F) G (a + b) d).hom ≫
      (α_ E F G).hom⟦(a + b) + d⟧' =
    (α_ (E⟦a⟧) (F⟦b⟧) (G⟦d⟧)).hom ≫
      ((E⟦a⟧) ◁ (totalTensorShiftIso (A := A) F G b d).hom) ≫
      (totalTensorShiftIso (A := A) E (F ⊗ G) a (b + d)).hom ≫
      (eqToIso (congrArg (fun k : ℤ ↦ (E ⊗ (F ⊗ G))⟦k⟧)
        (Int.add_assoc a b d).symm)).hom

/-- The symmetry clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry : Prop :=
  ∀ (E F : CochainComplex A ℤ) (a b : ℤ),
  (totalTensorShiftIso (A := A) E F a b).hom ≫ (β_ E F).hom⟦a + b⟧' =
    (a * b).negOnePow • ((β_ (E⟦a⟧) (F⟦b⟧)).hom ≫
      (totalTensorShiftIso (A := A) F E b a).hom ≫
      (eqToIso (congrArg (fun k : ℤ ↦ (F ⊗ E)⟦k⟧) (Int.add_comm b a))).hom)

/-- The associativity coefficients clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_associativity_coefficients : Prop :=
  ∀ (b d p q : ℤ),
  (b * p + d * (p + q)).negOnePow = (d * q + (b + d) * p).negOnePow

/-- The symmetry coefficients clause of signed total-tensor coherence.
Source: Stacks 0FPQ and More on Algebra, integer sign rules
(blueprint: lem-pur-total-tensor-signed-coherence). -/
def totalTensorCoherence_symmetry_coefficients : Prop :=
  ∀ (a b p q : ℤ),
  (b * p + (p + a) * (q + b)).negOnePow = (a * b + p * q + a * q).negOnePow

/-- All summand, inverse, naturality, uniqueness and signed coherence identities.
The tensor, associator and symmetry are the native direct-sum total constructions;
`totalTensorShiftIso` is constructed from the recorded integer bifunctor comparisons.
Source: Stacks 0FPQ and More on Algebra, integer sign rules, with shifted-degree normalization
(blueprint: lem-pur-total-tensor-signed-coherence). -/
structure TotalTensorSignedCoherence : Prop where
  shift_formula : totalTensorCoherence_shift_formula (A := A)
  associator_formula : totalTensorCoherence_associator_formula (A := A)
  symmetry_formula : totalTensorCoherence_symmetry_formula (A := A)
  shift_inverse : totalTensorCoherence_shift_inverse (A := A)
  associator_inverse : totalTensorCoherence_associator_inverse (A := A)
  symmetry_inverse : totalTensorCoherence_symmetry_inverse (A := A)
  shift_natural : totalTensorCoherence_shift_natural (A := A)
  associator_natural : totalTensorCoherence_associator_natural (A := A)
  symmetry_natural : totalTensorCoherence_symmetry_natural (A := A)
  shift_unique : totalTensorCoherence_shift_unique (A := A)
  associator_unique : totalTensorCoherence_associator_unique (A := A)
  symmetry_unique : totalTensorCoherence_symmetry_unique (A := A)
  associativity : totalTensorCoherence_associativity (A := A)
  symmetry : totalTensorCoherence_symmetry (A := A)
  associativity_coefficients : totalTensorCoherence_associativity_coefficients
  symmetry_coefficients : totalTensorCoherence_symmetry_coefficients

end Formulas

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- Signed coherence for arbitrary unbounded complexes on a small ringed site.
Source: Stacks 0FPQ; More on Algebra, item-shift-tensor and item-flip-tensor-product
(blueprint: lem-pur-total-tensor-signed-coherence).

Proof:
1. In the module universe max(c,v,u), the site is small. Additive sheafification exists
and has locally bijective equivalences. Set sheafification preserves finite products;
lifting its adjunction to abelian group objects identifies its underlying set functor
with abelian sheafification (the three sheafification nodes in the DAG).
2. By the sheaf-tensor bilinear universal property, maps agree if they agree on local
pure tensors. Tensor preserves coproducts in each variable. Apply this in each total
degree to obtain equality tests for double and triple tensors. For nested tensors,
use product-preserving set sheafification on the inner tensor, rather than assuming
that global sections are generated by global pure tensors. No boundedness is needed.
3. Apply lem-sf-ringed-tensor-complex-constraints: the native associator is unsigned
and the braiding has coefficient (-1)^(pq). Reassociation preserves the differential's
three coefficients 1, (-1)^p, (-1)^(p+q). The flip commutes with the differential since
(p+1)q=pq+q and p+p(q+1) is congruent to pq modulo 2. Reverse reassociation is inverse;
the two flips multiply to (-1)^(pq+qp)=1. Step 2 gives uniqueness.
4. Apply lem-weil-pbc-total-tensor-integer-shifts to the additive tensor bifunctor.
Extract b from the second factor of E[a] tensor F[b], then a from the first factor,
then identify [a][b] with [a+b]. This is the actual definition above, with coefficient
(-1)^(bp) on shifted first degree p.
5. In the chain-map square for this extraction the dx coefficients have exponents
a+b(p+1) and bp+a+b; the dy exponents are p+b+bp and bp+a+b+p+a, equal modulo 2.
Reverse reindexing uses the same bp, not b(p+a); composing gives (-1)^(2bp)=1.
6. Chain maps preserve degree. Both naturality routes on pure sections therefore
produce (-1)^(bp) f(x) tensor g(y), or (-1)^(pq) g(y) tensor f(x), or
f(x) tensor (g(y) tensor h(z)), respectively. Step 2 proves the naturality identities.
7. For triple shifted degrees p,q,r, the left extraction has exponent bp+d(p+q),
whereas the right extraction has exponent dq+(b+d)p. These are equal as integers.
The underlying output is x tensor (y tensor z), so step 2 proves associativity.
8. The symmetry square has exponents bp+(p+a)(q+b) and ab+pq+aq; they differ by
2bp. Hence their signs agree, and step 2 proves the signed symmetry identity.
9. Integer negOnePow is parity for every integer. Reindexing by negative integers
is still bijective; coproducts and all calculations apply to unbounded complexes.
No flatness, localization or degree-zero restriction is involved. -/
theorem totalTensor_signed_coherence :
    TotalTensorSignedCoherence (A := Modules.{c, v, u} J R) := by
  sorry

end CategoryTheory.RingedDerivedNative
