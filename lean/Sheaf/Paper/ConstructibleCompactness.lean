/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Paper.LocalizingClosureExistence
public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.AmbientIndDerivedTriangulated
import Sheaf.Paper.ConstructibleCompactnessBounded
import Sheaf.CategoryTheory.CompactObjectsThick
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.Paper.AmbientIndDerivedSums
import Sheaf.Paper.FiniteWindow
import Sheaf.Paper.UniformConstructibleExt

/-!
# Compactness with rational coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-constructible-compactness, statement and proof; Stacks Project, Tag 09QH
(blueprint: sk-thm-constructible-compactness).

The two coefficient choices are the continuous-function condensed ring of a finite
subextension and the finite-subextension-valued condensed algebraic closure. The
ambient category is the ordinary unbounded derived category of internal left modules.
Cons and Dbc use finite constant scalar models, rather than arbitrary local finite
presentations. IndCons and Dic are expressed inline using Mathlib's filtered-colimit
property and the ambient cohomology functors.
-/

@[expose] public section

set_option autoImplicit false

universe t w v u

open CategoryTheory CategoryTheory.Limits DirectSum

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Classical in
/-- The canonical additive map from the direct sum of Hom groups, induced by the
coprojections of the specified ambient cofan. On a finitely supported tuple it sums
the composites with those coprojections.
Source: blueprint sk-thm-constructible-compactness, displayed comparison
(blueprint: sk-thm-constructible-compactness). -/
noncomputable def constructibleCompactnessComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {I : Type t} (C : DerivedCategory A) (K : I → DerivedCategory A) (c : Cofan K) :
    (⨁ i : I, (C ⟶ K i)) →+ (C ⟶ c.pt) :=
  DirectSum.toAddMonoid fun i ↦ Preadditive.rightComp C (c.inj i)

/-- The two compactness assertions for a specified condensed coefficient ring.
The first is compactness in the full localizing closure of Dbc, using the recorded
compact-object definition. The second uses ambient Hom groups and ambient coproducts
for every small family with ind-constructible cohomology, without a common bound.
Existence of the coproduct cofan is included, so no coproduct choice is assumed.
Any other coproduct gives the same comparison through its unique compatible isomorphism.
Source: blueprint sk-thm-constructible-compactness, both assertions
(blueprint: sk-thm-constructible-compactness). -/
def HasConstructibleCompactness
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  (∃ _ : HasCoproducts.{u + 1}
      (localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory,
    ∀ C : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      constantModelBoundedConstructible Λ X C →
      ∃ hC : localizingClosure (constantModelBoundedConstructible Λ X) C,
        IsCompactObject.{u + 1}
          (ObjectProperty.FullSubcategory.mk C hC)) ∧
  (∀ (C : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
    constantModelBoundedConstructible Λ X C →
    ∀ (I : Type (u + 1))
      (K : I → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      (∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∃ (c : Cofan K) (_ : IsColimit c),
        Function.Bijective (constructibleCompactnessComparison C K c))

/-- Every bounded constructible complex is compact in the localizing closure of Dbc;
its ambient Hom functor also commutes with every small coproduct of Dic objects.
Both rational coefficient choices are asserted, with their canonical ring structures.
Here `PadicAlgCl ℓ` is the fixed algebraic closure, and `E` ranges over all its finite
intermediate fields; this is the coefficient convention of sk-def-sfb-qlbar-condensed.
Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-constructible-compactness, statement and proof; Stacks Tags 09QH and 08J5
(blueprint: sk-thm-constructible-compactness).

Proof plan, for each of the two coefficient rings:
1. Use only the ordinary layer-(B) ambient category of sk-def-sfb-derived-categories.
   By det-ambient-ind-derived-triangulated, Dic is a full triangulated subcategory.
   By det-ambient-ind-derived-sums it contains Dbc and its localizing closure and
   is closed under ambient small sums and both truncations. The sums exist and are
   termwise by det-def-localizing-closure-existence. Fullness gives the same Hom
   groups and coproducts internally, so def-pc-compact-object is exactly the Hom
   comparison for every family in Dic.
2. For a constructible sheaf C, choose the nonnegative bound d_C of
   sk-lem-uniform-constructible-ext and set T_C = tau_ge_(-d_C) tau_le_0.
   The canonical map from the sum of T_C(K_i) to T_C(sum K_i) induces the identity
   on cohomology in [-d_C,0], and zero-to-zero outside. This uses def-kun-truncations
   and cohomology commuting with sums from det-ambient-ind-derived-sums. On complex
   representatives the map is induced by the truncated coprojections, so it is a
   quasi-isomorphism and is inverted by def-weil-abstract-derived-category.
3. Apply sk-lem-finite-window with m=0 to each K_i and their sum. Naturality and
   step 2 identify their Hom comparison with the comparison for the family T_C(K_i).
   This family has the common interval [-d_C,0]. Apply
   det-constructible-compactness-bounded with a=-d_C, b=0 and s=0 to make this
   comparison bijective. Thus C is compact in Dic for all families, including
   families with no common bound.
4. Compact objects of Dic are closed under shifts and triangles by
   lem-sc-compact-objects-thick (Tag 09QH). For bounded constructible C choose
   [a,b] containing its cohomology. The successive triangles of
   lem-weil-pbc-truncation-triangle have third term H^n(C)[-n], which is compact
   by step 3 and shift closure. The formulas of def-kun-truncations identify
   tau_le_(a-1) C with zero and tau_le_b C with C. Finite induction on the
   truncations therefore proves compactness for C.
5. Apply det-def-localizing-closure-existence to the actual class Dbc, rather than
   Dctf. By det-ambient-ind-derived-sums its closure is in Dic. Fullness and closure
   under ambient sums make the comparison of step 4 the internal compactness
   comparison in this localizing closure too. -/
theorem constructible_compactness
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    HasConstructibleCompactness (Profinite.continuousMapRingObj E) X ∧
      HasConstructibleCompactness (Profinite.padicAlgClRingObj ℓ) X := by
  sorry

end AlgebraicGeometry.ProEtale
