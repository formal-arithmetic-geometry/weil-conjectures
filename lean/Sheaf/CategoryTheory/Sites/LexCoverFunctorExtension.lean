/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.CategoryTheory.Sites.LexCoverFunctors
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Elements
import Sheaf.TraceFormula.SieveSheavesCoveringSite
import Sheaf.CategoryTheory.SheafSubcategoryComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Extension of left exact covering functors

Source: Stacks Project, Sites, Tags 00X6, 03A1, 00WS and 0GLW; the equivalence and the
transformation assertion are the categorical assembly recorded in the DAG
(blueprint: lem-per-lex-cover-functor-extension).

The hom universe `w` is the containing universe of the size convention. The site is small
in it, sheaves take values in `Type w`, and the topos may have objects in any universe `u`.
The category indexing a sheaf's presentation is its opposite category of elements.
-/

@[expose] public section

set_option autoImplicit false

universe w u

namespace CategoryTheory

open Limits Opposite

/-- The sheafified representables, using the recorded sheafification functor.
Source: Stacks Sites 00WH, 0GLW (blueprint: lem-per-lex-cover-functor-extension). -/
noncomputable def lexCoverSheafifiedYoneda {C : Type w} [SmallCategory C]
    (K : Precoverage C) : C ⥤ Sheaf K.toGrothendieck (Type w) :=
  yoneda ⋙ presheafToSheaf K.toGrothendieck (Type w)

/-- The section map `h_U^# → F` corresponding to a section of `F(U)`.
Source: Stacks Sites 00WH, 0GLW and Categories 001P
(blueprint: lem-per-lex-cover-functor-extension). -/
noncomputable def lexCoverSectionMap {C : Type w} [SmallCategory C]
    (K : Precoverage C) (F : Sheaf K.toGrothendieck (Type w))
    (U : C) (s : F.obj.obj (op U)) : (lexCoverSheafifiedYoneda K).obj U ⟶ F :=
  ((sheafificationAdjunction K.toGrothendieck (Type w)).homEquiv (yoneda.obj U) F).symm
    (yonedaEquiv.symm s)

/-- The Hom presheaf, functorial in its target. At `G,U` its value is `A(U) ⟶ G`, with
restriction by precomposition with `A.map` and target action by postcomposition.
Source: Stacks Sites 03A1 and 00X6
(blueprint: lem-per-lex-cover-functor-extension). -/
def lexCoverHomPresheaf {C : Type w} [SmallCategory C]
    {E : Type u} [Category.{w} E] (A : C ⥤ E) : E ⥤ Cᵒᵖ ⥤ Type w :=
  yoneda ⋙ (Functor.whiskeringLeft Cᵒᵖ Eᵒᵖ (Type w)).obj A.op

/-- Restriction to sheafified representables is an equivalence. Its inverse has the stated
Hom right adjoint, canonical element-colimit presentation and representable normalization;
all transformations extend uniquely. The adjunction and left exactness are packaged as the
recorded geometric-morphism datum.

Source: Stacks Sites 00X6, 03A1, 00WS, 0GLW
(blueprint: lem-per-lex-cover-functor-extension).

Proof:
1. Present the topos by a small sieve site and replace it by a covering-family site using
   lem-trf-sieve-sheaves-covering-site. Close the representables and the objects A(U) under
   finite limits. Apply lem-weil-pbc-sheaf-subcategory-comparison to obtain its epimorphic
   covering site and the restricted-Yoneda equivalence, including the chosen image covers.
2. Corestrict A to that site. Finite limits and image covers give continuity directly by
   the equalizer sheaf condition. Use the same-universe adjunction of
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction. The presheaf left Kan extension
   is left exact by lem-weil-pbc-presheaf-pullback-sets-left-exact, sheafification by
   lem-weil-pbc-sheafification-sets-exact, and sheaf limits are sectionwise by
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise. Transport along the equivalence; the nerve
   formula gives the Hom right adjoint with its restriction and target actions.
3. Sheafification adjunction (lem-trf-sieve-set-sheafification-exists) and
   lem-galois-yoneda-hom-bijection identify Hom(H_U,F) with F(U). Adjunction now identifies
   Hom(L_A H_U,G) with Hom(A(U),G); evaluate at identities to obtain the natural isomorphism.
4. The section maps form a colimit of sheafified representables: a cocone is exactly a
   compatible assignment of elements, hence a map F → G, by those same two Hom bijections.
   This works without subcanonicity or fullness of sheafified Yoneda.
5. Apply lem-weil-pbc-left-adjoint-preserves-colimits to that cocone. The comparison of
   Step 3 identifies the image legs with the displayed legs; this is the asserted canonical
   colimit, and is functorial in F since section maps are natural in F.
6. For alpha on restrictions, precomposition defines R_M → R_L on Hom sheaves. Transpose
   the composite of M's unit and this transformation to obtain beta. Adjunction at the
   identity section gives beta at H_U equal to alpha_U, including nonrepresentable sections.
   Naturality with every section map and the colimit in Step 4 force uniqueness.
7. Sheafified Yoneda preserves finite limits by exactness of sheafification. A generating
   cover is jointly epimorphic by uniqueness in the sheaf condition. Left adjoints preserve
   this cancellation condition by adjunction, even for an empty cover, so restriction lands
   in LexCov.
8. Step 6 gives full faithfulness; Steps 2--3 give essential surjectivity. Unique normalized
   comparisons give the equivalence identities. The datum of Step 2 is a geometric morphism
   by def-trf-geometric-morphism, and Step 6 makes the normalized extension independent of
   the site presentation.
-/
theorem lexCoverFunctor_extension {C : Type w} [SmallCategory C] [HasFiniteLimits C]
    (K : Precoverage C) (hfinite : K ≤ Precoverage.finite C)
    (E : Type u) [Category.{w} E] (hE : IsGrothendieckTopos.{w} E) :
    ∃ e : (lexLeftAdjointProperty (Sheaf K.toGrothendieck (Type w)) E).FullSubcategory ≌
        (lexCoverFunctorProperty K E).FullSubcategory,
      Nonempty (e.functor ⋙ (lexCoverFunctorProperty K E).ι ≅
        (lexLeftAdjointProperty (Sheaf K.toGrothendieck (Type w)) E).ι ⋙
          (Functor.whiskeringLeft C (Sheaf K.toGrothendieck (Type w)) E).obj
            (lexCoverSheafifiedYoneda K)) ∧
      (∀ A : (lexCoverFunctorProperty K E).FullSubcategory,
        ∃ (g : GeometricMorphism E (Sheaf K.toGrothendieck (Type w)))
          (n : lexCoverSheafifiedYoneda K ⋙ g.inverse ≅ A.obj),
          Nonempty (g.inverse ≅ (e.inverse.obj A).obj) ∧
          Nonempty (g.direct ⋙ sheafToPresheaf K.toGrothendieck (Type w) ≅
            lexCoverHomPresheaf A.obj) ∧
          ∀ F : Sheaf K.toGrothendieck (Type w),
            ∃ (c : Cocone ((CategoryOfElements.π F.obj).leftOp ⋙ A.obj))
              (t : c.pt ≅ g.inverse.obj F),
              Nonempty (IsColimit c) ∧
              ∀ x : F.obj.Elementsᵒᵖ,
                c.ι.app x ≫ t.hom = n.inv.app x.unop.1.unop ≫
                  g.inverse.map (lexCoverSectionMap K F x.unop.1.unop x.unop.2)) ∧
      (∀ (L M : (lexLeftAdjointProperty (Sheaf K.toGrothendieck (Type w)) E).FullSubcategory)
        (α : lexCoverSheafifiedYoneda K ⋙ L.obj ⟶ lexCoverSheafifiedYoneda K ⋙ M.obj),
        ∃! β : L.obj ⟶ M.obj, Functor.whiskerLeft (lexCoverSheafifiedYoneda K) β = α) := by
  sorry

end CategoryTheory
