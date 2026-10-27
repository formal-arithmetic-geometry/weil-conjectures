/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.NormalizedRingHomExtension
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Projective
import Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension
import Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree

/-! # Oppositely bounded finite-free Hom and scalar extension

Source: Stacks Project, more-algebra.tex, Tag 0ATK, proof of clause (3),
specialized to a scalar complex in degree zero.
(blueprint: lem-trf-half-bounded-hom-scalar-isomorphism)

We use the one-object bottom-topology model explicitly allowed in the node.
Evaluation identifies its product Hom with `CochainComplex.moduleHomComplex`.
All truncations below are stupid truncations of complexes, degree by degree.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The normalized scalar-extension chain map, using the existing construction without
any boundedness assumption. Its coordinate formula is
`chi(s tensor f)_p(t tensor x) = st tensor f_p(x)`; this determines the map uniquely,
since pure tensors span on the punctual site and the product projections detect equality.
Thus this selection is independent of the existence witness, not an arbitrary Hom map.
Source: Stacks, Tag 0ATK(3), and the normalized comparison of Tag 0A8X
(blueprint: lem-trf-half-bounded-hom-scalar-isomorphism). -/
noncomputable def halfBoundedHomScalarMap
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : RingSiteModules R ⥤ RingSiteModules S)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P N : CochainComplex (RingSiteModules R) ℤ) :
    (ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf R) P N) ⟶
      homComplex (R := CochainComplex.onePointRingSheaf S)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj N) :=
  (normalizedRingHomExtension_exists φ F h hm hF P N).choose

/-- The normalized chain map is natural in precomposition and postcomposition.
Source: Stacks, Tag 0ATK(3), naturality of its canonical comparison
(blueprint: lem-trf-half-bounded-hom-scalar-isomorphism).

Proof: by the functoriality in def-pur-hom-complex, both sides evaluated in coordinate
p on `s tensor f` and `t tensor x` give `st tensor beta(f_p(alpha(x)))`.
Use lem-pc-normalized-ring-hom-extension for this formula. Pure tensors generate,
and the shared product projections detect equality. This proves the square for
arbitrary complexes, hence also on the bounded classes of the isomorphism theorem.
Multiplication by inverse isomorphisms gives the inverse naturality square. -/
theorem halfBoundedHomScalarMap_naturality
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : RingSiteModules R ⥤ RingSiteModules S)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P P' N N' : CochainComplex (RingSiteModules R) ℤ)
    (α : P' ⟶ P) (β : N ⟶ N') :
    (ringExtensionComplex F hF).map
        (((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).map α.op).app N ≫
          ((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).obj (op P')).map β) ≫
        halfBoundedHomScalarMap φ F h hm hF P' N' =
      halfBoundedHomScalarMap φ F h hm hF P N ≫
        ((homComplexFunctor (R := CochainComplex.onePointRingSheaf S)).map
          ((ringExtensionComplex F hF).map α).op).app ((ringExtensionComplex F hF).obj N) ≫
        ((homComplexFunctor (R := CochainComplex.onePointRingSheaf S)).obj
          (op ((ringExtensionComplex F hF).obj P'))).map
            ((ringExtensionComplex F hF).map β) := by
  sorry

/-- Opposite half bounds make the normalized scalar Hom comparison an isomorphism of
complexes. Its degreewise restriction identifications are the actual Hom maps of the
stupid-truncation inclusion, their inverses insert zero, and the comparison square
identifies each degree with the bounded finite-free comparison.
Source: Stacks, Tag 0ATK(3), degree-dependent finite-support refinement
(blueprint: lem-trf-half-bounded-hom-scalar-isomorphism).

Proof, following the six steps of the DAG:
1. Use lem-weil-pbc-singleton-site-module-comparison to identify ordinary modules,
tensor products and product Hom with this model, and def-sc-module-total-hom-complex
and def-pur-hom-complex for the signed differential. The construction in
lem-pc-normalized-ring-hom-extension gives the displayed pure-tensor chain map.
2. For degree n put c=a-n. If p<c then N^(p+n)=0. Restriction to the stupid tail
(def-kun-truncations) is therefore invertible, with inverse zero insertion. The same
holds after tensoring since tensor sends zero to zero. The tail is supported in [c,b];
if c>b it is zero, and otherwise its retained terms are finite free.
3. A finite basis gives finite generation (def-weil-finitely-generated-module) and
a lift along every surjection by choosing preimages of basis elements, hence projectivity
(def-weil-pbc-projective-module). Apply lem-pc-finite-projective-ring-hom-extension
at each retained term, with no restriction on S or the corresponding term of N.
4. Apply lem-pc-bounded-ring-hom-extension-degree on [min(c,b),b]. Restriction and
zero insertion keep all retained coordinates, so the conjugated comparison has the
same normalized formula as the comparison for the tail. Pure tensors and product
projections detect equality. This gives the stated square and degreewise invertibility.
5. If psi^n is the inverse of chi^n, multiply the chain equation by the two inverses
to obtain F(d_H)^n psi^n = psi^(n+1) d_H'^n. Thus the inverses form a chain map,
giving the actual complex isomorphism e. No derived equivalence of the tail is asserted.
6. Precomposition and postcomposition give the same pure-tensor formula on either
path of the naturality square, as stated by halfBoundedHomScalarMap_naturality.
Conjugate that square by the inverse chain maps for inverse naturality. -/
theorem halfBoundedHomScalar_isomorphism
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : RingSiteModules R ⥤ RingSiteModules S)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P N : CochainComplex (RingSiteModules R) ℤ) (a b : ℤ)
    (hP : ∀ p : ℤ, b < p → IsZero (P.X p))
    (hfree : ∀ p : ℤ, Module.Free R ((P.X p).val.obj (op ⟨PUnit.unit⟩)))
    (hfinite : ∀ p : ℤ, Module.Finite R ((P.X p).val.obj (op ⟨PUnit.unit⟩)))
    (hN : ∀ q : ℤ, q < a → IsZero (N.X q)) :
    ∃ e : (ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf R) P N) ≅
      homComplex (R := CochainComplex.onePointRingSheaf S)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj N),
      e.hom = halfBoundedHomScalarMap φ F h hm hF P N ∧
      (∀ n : ℤ, IsIso ((halfBoundedHomScalarMap φ F h hm hF P N).f n)) ∧
      (∀ n : ℤ,
        ∃ rR : (homComplex (R := CochainComplex.onePointRingSheaf R) P N).X n ≅
            (homComplex (R := CochainComplex.onePointRingSheaf R)
              (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - n))) N).X n,
        ∃ rS : (homComplex (R := CochainComplex.onePointRingSheaf S)
            ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj N)).X n ≅
          (homComplex (R := CochainComplex.onePointRingSheaf S)
            ((ringExtensionComplex F hF).obj
              (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - n))))
            ((ringExtensionComplex F hF).obj N)).X n,
          rR.hom = (((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).map
            (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE (a - n))).op).app N).f n ∧
          rS.hom = (((homComplexFunctor (R := CochainComplex.onePointRingSheaf S)).map
            ((ringExtensionComplex F hF).map
              (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE (a - n)))).op).app
                ((ringExtensionComplex F hF).obj N)).f n ∧
          (halfBoundedHomScalarMap φ F h hm hF P N).f n ≫ rS.hom =
            F.map rR.hom ≫ (halfBoundedHomScalarMap φ F h hm hF
              (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - n))) N).f n ∧
          (∀ (p : ℤ) (_hp : p < a - n) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
            (f : (homComplex (R := CochainComplex.onePointRingSheaf R)
              (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - n))) N).X n |>.val.obj U)
            (x : (P.X p).val.obj U),
            ringHomEvaluate P N n p U (rR.inv.val.app U f) x = 0) ∧
          (∀ (p : ℤ) (_hp : p < a - n) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
            (f : (homComplex (R := CochainComplex.onePointRingSheaf S)
              ((ringExtensionComplex F hF).obj
                (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - n))))
              ((ringExtensionComplex F hF).obj N)).X n |>.val.obj U)
            (x : (((ringExtensionComplex F hF).obj P).X p).val.obj U),
            ringHomEvaluate ((ringExtensionComplex F hF).obj P)
              ((ringExtensionComplex F hF).obj N) n p U (rS.inv.val.app U f) x = 0)) := by
  sorry

end CategoryTheory
