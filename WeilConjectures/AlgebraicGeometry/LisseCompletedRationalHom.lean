/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseCompletedSystemData

/-! # Localized Hom groups of completed lisse lattices -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompletedLisse
variable (l : ℕ) [Fact l.Prime]

/-- The actual scalar extension of the reconstructed integral lattice.
Source: BS 6.8.4(4) (blueprint: lem-per-completed-lisse-rational-hom). -/
abbrev rationalizedLattice (P : Base.{u} l) (I : IntegralComparison l P)
    (F : RawRational l P) :=
  (completedAdicChange P.X (I.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)).obj
    (I.equivalence.inverse.obj ⟨F.obj.integral, F.property⟩).obj

/-- The canonical tensor map on Hom groups is bijective.
The additive map is uniquely specified on all pure tensors.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(4), pp.58--59
(blueprint: lem-per-completed-lisse-rational-hom).

Proof: scalar extension carries a finite local basis to the same basis over the rational
coefficient sheaf. IntegralComparison identifies integral Hom with compatible maps of the
finite quotient towers; its scalar projection equation makes that identification A-linear.
For two integral lattices, their internal Hom is locally a finite matrix module. Localizing
it is therefore the rational internal Hom, with the map sending a tensor a tensor f to
a times scalar extension of f. The supplied localization cocone identifies inversion of l
with the continuous field coefficients. Noetherianity and separatedness make the scheme
qcqs. Degree zero bounded-continuity-sections applied to the scalar multiplication sequence
of the internal Hom identifies its localized global sections with the global sections of
its localization. Algebraically these localized sections are E tensor_A Hom. This proves
bijectivity. Additivity and A-balancing give the displayed additive map, and generation by
pure tensors proves uniqueness. The matrix calculation includes empty and rank-zero charts. -/
theorem completed_lisse_rational_hom (P : Base.{u} l) (I : IntegralComparison l P) :
    ∀ F G : RawRational l P,
        ∃! h : (F.obj ⟶ G.obj) →+
            (rationalizedLattice l P I F ⟶ rationalizedLattice l P I G),
          Function.Bijective h ∧
          ∀ (a : P.E) (f : F.obj.integral ⟶ G.obj.integral),
            h (TensorProduct.tmul (Integers l P) a f) =
              (completedAdicChange P.X
                (I.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)).map
                  (I.equivalence.inverse.map ⟨f⟩).hom ≫
                    rationalScalar l P _ a := by sorry

end AlgebraicGeometry.ProEtale.CompletedLisse
