/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit

/-! # Scalar telescopes for a functorial K-injective Hom representative

Source: Stacks Project, derived.tex, Tag 070I (lemma-K-injective), Tags 093W and 0949;
sites-cohomology.tex, Section 0A8X (section-hom-complexes)
(blueprint: lem-sfb-kinjective-hom-scalar-telescope).

The resolution functor is arbitrary and is not required to be linear. The two explicit
sequence diagrams have the same Hom-complex objects, and their colimits are taken in
complexes, hence termwise. Their derived comparison preserves every colimit leg.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Multiplication by a global section on a complex, using the canonical sectionwise action.
Source: Stacks Project, Section 0A8X; the scalar-Hom telescope argument
(blueprint: lem-sfb-kinjective-hom-scalar-telescope). -/
def kInjectiveHomScalarEndomorphism
    (s : RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (K : CochainComplex (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    K ⟶ K :=
  letI : Linear (RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
      (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).property
  s • 𝟙 K

/-- The sequence with constant term Hom(A,I(P)) and transition Hom(A,I(s_P)).
Source: Stacks Project, Tag 070I and Section 0A8X; the scalar-Hom telescope argument
(blueprint: lem-sfb-kinjective-hom-scalar-telescope). -/
def kInjectiveHomFunctorialScalarTower
    (I : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (s : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (A P : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ℕ ⥤ CochainComplex (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ :=
  Functor.ofSequence
    (X := fun _n : ℕ ↦ homComplex.{c, v, max c v r, max c v r} (R := R) A (I.obj P))
    (fun _n ↦ ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map
        (I.map (kInjectiveHomScalarEndomorphism.{c, v, r} J R s P)))

/-- The sequence with constant term X = Hom(A,I(P)) and scalar transition s_X.
Source: Stacks Project, Section 0A8X and Tags 093W, 0949; the scalar-Hom telescope argument
(blueprint: lem-sfb-kinjective-hom-scalar-telescope). -/
def kInjectiveHomScalarTower
    (I : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (s : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (A P : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ℕ ⥤ CochainComplex (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ :=
  Functor.ofSequence
    (X := fun _n : ℕ ↦ homComplex.{c, v, max c v r, max c v r} (R := R) A (I.obj P))
    (fun _n ↦ kInjectiveHomScalarEndomorphism.{c, v, r} J R s
      (homComplex.{c, v, max c v r, max c v r} (R := R) A (I.obj P)))

/-- The functorial-resolution and scalar transitions on Hom(A,I(P)) are homotopic;
their termwise colimits become isomorphic in D(R), compatibly with every leg, including zero.
Source: Stacks Project, Tag 070I (lemma-K-injective), Tags 093W, 0949 and Section 0A8X
(blueprint: lem-sfb-kinjective-hom-scalar-telescope).

Proof:
1. Write J₀ = I(P), a = I(s_P), b = s_J₀. Naturality of η and linearity of η_P give
η_P followed by a = s_P followed by η_P = η_P followed by b. Cancel Q(η_P), an
isomorphism, to obtain Q(a) = Q(b). The K-injective mapping-class bijection
(lem-weil-pbc-kinjective-hom-derived, Tag 070I) gives h with a-b = dh+hd.
2. On a degree-n family f in the Hom complex set H(f)^p = h^(p+n) f^p.
The Hom differential is d(f) = d_J₀ f - (-1)^n f d_A. Thus dH(f) has the term
(+(-1)^n) hf d_A while Hd(f) has its negative. They cancel, giving
dH+Hd = (dh+hd) postcomposition = t₁-t₂. Postcomposition with b is scalar s_X.
3. For each tower take B = the direct sum of its copies of X and set
u_k e_n = e_n - e_(n+1) t_k. The complex-colimit/homotopy-colimit theorem
(lem-kun-complex-colimit-hocolim) gives a canonical quasi-isomorphism
p_k : Cone(u_k) → C_k. It is q_k on the unshifted summand, zero on the shifted
summand, and satisfies p_k v_k e_n = j_n^(k) for every n. Exact filtered colimits
apply to the small filtered category of natural numbers, without monic transitions.
4. Define K e_n = -e_(n+1) H degreewise using the coproduct universal property.
Then dK+Kd = u₁-u₂. In the cone convention d(b,c) = (db+u_k c,-dc),
F(b,c) = (b+Kc,c) is a chain isomorphism Cone(u₁) → Cone(u₂), with inverse
(b,c) ↦ (b-Kc,c). Direct matrix multiplication gives the chain identity;
F v₁ e_n = v₂ e_n holds identically for every n, including zero.
5. Set γ = Q(p₁)⁻¹ followed by Q(F) followed by Q(p₂). All three factors are
isomorphisms. The equations in steps 3 and 4 give Q(j_n^(1)) followed by γ
= Q(j_n^(2)) for every n. All calculations allow arbitrary integer degrees;
no boundedness or continuity of derived internal Hom is used. -/
theorem kInjectiveHom_scalar_telescope
    [AB5OfSize.{max c v r, max c v r} (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (I : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective)
    (s : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (A P : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    Nonempty (Homotopy
      (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map
        (I.map (kInjectiveHomScalarEndomorphism.{c, v, r} J R s P)))
      (kInjectiveHomScalarEndomorphism.{c, v, r} J R s
        (homComplex.{c, v, max c v r, max c v r} (R := R) A (I.obj P)))) ∧
    ∃ γ : DerivedCategory.Q.obj
        (colimit (kInjectiveHomFunctorialScalarTower.{c, v, r} J R I s A P)) ≅
        DerivedCategory.Q.obj (colimit (kInjectiveHomScalarTower.{c, v, r} J R I s A P)),
      ∀ n : ℕ,
        DerivedCategory.Q.map
          (colimit.ι (kInjectiveHomFunctorialScalarTower.{c, v, r} J R I s A P) n) ≫
          γ.hom =
        DerivedCategory.Q.map (colimit.ι (kInjectiveHomScalarTower.{c, v, r} J R I s A P) n) := by
  sorry

end CategoryTheory
