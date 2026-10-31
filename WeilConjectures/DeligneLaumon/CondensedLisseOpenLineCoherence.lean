/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
import WeilConjectures.DeligneLaumon.CondensedLisseOpenGeometry
import WeilConjectures.DeligneLaumon.CondensedLisseCanonicalLineComposition
import WeilConjectures.DeligneLaumon.CondensedLisseNormalizedLineComposition

/-! # Coherent root-normalized restriction of shifted Tate lines -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual
variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- Root-normalized shifted Tate lines form a Cartesian family on compatible opens.
Source: Step 2 of `thm-a1-curve-perverse-heart`, restriction and compatibility of
smooth orientations
(blueprint: lem-per-condensed-lisse-open-line-coherence).

Proof: transport invertibility of ell from the field to every residue field of
these schemes. The individual isomorphisms and their normalization are given; their existence
is proved in `open_line_normalized_exists`. For composition first check the finite root maps
on local roots: successive restriction equals composite restriction. The
projection equations and uniqueness of the normalized finite comparisons give
the corresponding integral equality by limit extensionality. The scalar
associators and monoidal inverse-image compositors carry it to the first Tate
line, and induction on the tensor power gives the equality on every ordinary
line. Apply the derived single-functor comparison and its shift compositor; the
total-versus-exact comparisons commute with composition, giving exactly
`pullComp`. Empty-source cases are equalities of maps in a zero category. These
arguments include power zero, the identity open, and semilinear base isomorphisms.
-/
theorem open_line_coherence (k : Type u) [Field k] (hEll : IsUnit (ell : k))
    (rho : ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j],
      (∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom) →
        ((pull ell c j).obj (c.derivedLine ell T.scheme T.dim.val) ≅
          c.derivedLine ell V.scheme V.dim.val))
    (hn : ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j]
        (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
        (q : PurityTransport.LinePullCoordinates ell c j), V.dim = T.dim →
        HEq (rho V T j hj).hom
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) j).inv.app _ ≫ (q.derived ell T.dim.val).hom)) :
    ∀ (W V T : Space k) (i : W.scheme ⟶ V.scheme) (j : V.scheme ⟶ T.scheme)
        [IsOpenImmersion i] [IsOpenImmersion j]
        (hi : ∃ b : Spec (.of k) ≅ Spec (.of k), i ≫ V.map = W.map ≫ b.hom)
        (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
        (hij : ∃ b : Spec (.of k) ≅ Spec (.of k), (i ≫ j) ≫ T.map = W.map ≫ b.hom),
        (pullComp ell c i j).hom.app (c.derivedLine ell T.scheme T.dim.val) ≫
            (pull ell c i).map (rho V T j hj).hom ≫ (rho W V i hi).hom =
          (rho W T (i ≫ j) hij).hom := by
  intro W V T i j _ _ hi hj hij
  by_cases hW : Nonempty W.scheme
  · letI : Nonempty W.scheme := hW
    have hV : Nonempty V.scheme := ⟨i.base (Nonempty.some hW)⟩
    letI : Nonempty V.scheme := hV
    have hT : Nonempty T.scheme := ⟨j.base (Nonempty.some hV)⟩
    letI : Nonempty T.scheme := hT
    have hInv (S : Space k) : ∀ x : S.scheme, Invertible (ell : S.scheme.residueField x) :=
      fun x ↦ (by simpa using hEll.map (S.map.residueFieldAlgebraMap x) :
        IsUnit (ell : S.scheme.residueField x)).invertible
    letI : ∀ x : W.scheme, Invertible (ell : W.scheme.residueField x) := hInv W
    letI : ∀ x : V.scheme, Invertible (ell : V.scheme.residueField x) := hInv V
    letI : ∀ x : T.scheme, Invertible (ell : T.scheme.residueField x) := hInv T
    have hWV : W.dim = V.dim := open_dimensions_eq i hi
    have hVT : V.dim = T.dim := open_dimensions_eq j hj
    have hWT : W.dim = T.dim := hWV.trans hVT
    obtain ⟨qi⟩ := PurityTransport.linePullCoordinates_nonempty ell c i
    obtain ⟨qj⟩ := PurityTransport.linePullCoordinates_nonempty ell c j
    obtain ⟨qij, hcanonical⟩ := canonical_line_composition ell c k hEll i j qi qj
    have hri := hn W V i hi qi hWV
    have hrj := hn V T j hj qj hVT
    have hrij := hn W T (i ≫ j) hij qij hWT
    exact normalized_line_composition ell c k i j hi hj hij hWV hVT qi qj rho qij hri hrj
      hrij hcanonical
  · have hEmpty : IsEmpty W.scheme := not_nonempty_iff.mp hW
    letI : IsEmpty W.scheme := hEmpty
    have hZ : IsZero (c.derivedLine ell W.scheme W.dim.val) :=
      isZero_empty ell c W.scheme _
    apply hZ.eq_of_tgt

end AlgebraicGeometry.ProEtale.CondensedLisseDual
