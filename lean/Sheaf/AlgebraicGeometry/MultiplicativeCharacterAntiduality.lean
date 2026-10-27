module

public import Sheaf.AlgebraicGeometry.MultiplicativeCharacterData

import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-! # Character antiequivalence for groups of multiplicative type

Source: Milne, Algebraic Groups (2017), Theorems 12.8, 12.9, 12.23,
Corollary 12.19, and the proof of Corollary 12.25, pp.230--240
(blueprint: lem-sfb-multiplicative-character-antiduality).

The equivalence is specified on actual characters, their addition, conjugation,
and pullback maps. Its inverse has the actual finite-Galois invariant coordinate
algebra, with its descended Hopf law and indexed character normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeType

/-- Character antiequivalence, finite separable splitting, the invariant-algebra
quasi-inverse, the closed-immersion criterion, and arbitrary scalar extension.

Source: Milne, Sections 12(a)--(c), 12(g), pp.230--240, especially Theorems
12.8, 12.9, 12.23 and Corollaries 12.19, 12.25
(blueprint: lem-sfb-multiplicative-character-antiduality).

Proof plan:
1. By lem-sfb-affine-group-coordinate-hopf, characters correspond to group-like
   coordinate elements: the Laurent generator maps to a with counit 1 and
   coproduct a tensor a. The antipode supplies its inverse.
2. Use lem-sfb-split-torus-subgroups-diagonalizable over the algebraic closure,
   then lem-sfb-geometrically-diagonal-coalgebra-separable-basis to obtain a
   group-like basis over ks. Finite algebra generators have finite supports,
   which generate the finitely generated label group. Finitely many coefficients
   descend this splitting to a finite separable extension. Enlarge it using
   lem-weil-pbc-finite-set-in-finite-galois-subextension.
3. By lem-sfb-group-algebra-group-like-basis the group-like elements in F[M]
   are exactly e_m. Every Hopf map is uniquely e_n maps to e_(alpha n), so
   characters of D(M) identify with M, compatibly with composition.
4. The coefficient Galois action permutes this basis and has open stabilizers.
   Conversely a continuous action on finitely many generators factors through
   a finite Galois extension L. Apply lem-sfb-galois-hopf-algebra-descent to
   sigma(a e_m) = sigma(a) e_(sigma m). Its invariant algebra has the uniquely
   descended Hopf operations and becomes L[M] after scalar extension.
5. Descend equivariant Hopf maps uniquely, obtaining full faithfulness and the
   natural unit and counit. The evaluation e_chi maps to chi-star(t) gives the
   inverse identifications. Passing to a finite Galois compositum proves the
   independence of L, including its character labels.
6. By def-weil-closed-immersion, a closed immersion is a surjective coordinate
   map. Detect surjectivity after extending to ks; the image is the span of
   e_m with m in the image of the character map. This gives the stated iff,
   without reducedness or smoothness assumptions.
7. The canonical Hopf isomorphism K tensor k[M] to K[M] sends lambda tensor
   e_m to lambda e_m. The group-like-basis lemma shows that extension preserves
   exactly these character labels. Coefficient conjugation restricts the Galois
   action, and both orders of extending and pulling back send e_n to e_(f-star n).
   The same formula gives split scalar extension. -/
theorem multiplicative_character_antiduality
    (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks] :
    (∀ G : FiniteTypeGroups k,
      ∃ L : IntermediateField k ks, FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
        ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
          Nonempty ((baseChange (K := L)).obj G.obj ≅ diagonalizableGroup L M)) ∧
    ∃ E : (FiniteTypeGroups k)ᵒᵖ ≌ CharacterModules k ks,
    ∃ e : ∀ G : FiniteTypeGroups k,
      (E.functor.obj (op G)).obj.V ≃ GeometricCharacters ks G.obj,
    (∀ (G : FiniteTypeGroups k) (x y : (E.functor.obj (op G)).obj.V),
      (e G (x + y)).hom.hom = (e G x).hom.hom * (e G y).hom.hom) ∧
    (∀ (G : FiniteTypeGroups k) (σ : ks ≃ₐ[k] ks)
      (m : (E.functor.obj (op G)).obj.V),
      IsConjugate σ (e G m) (e G (((E.functor.obj (op G)).obj.ρ σ).hom m))) ∧
    (∀ (G H : FiniteTypeGroups k) (f : G ⟶ H)
      (m : (E.functor.obj (op H)).obj.V),
      e G ((E.functor.map f.op).hom.hom.hom m) =
        (baseChange (K := ks)).map f.hom ≫ e H m) ∧
    (∀ (G H : FiniteTypeGroups k) (f : G ⟶ H),
      IsClosedImmersion f.hom.hom.hom.left ↔
        Function.Surjective (E.functor.map f.op).hom.hom.hom) ∧
    (∀ M : CharacterModules k ks,
      ∃ L : FiniteGaloisIntermediateField k ks,
      ∃ ρ : (L ≃ₐ[k] L) →* End M.obj.V,
        ∀ σ : ks ≃ₐ[k] ks,
          M.obj.ρ σ = ρ (AlgEquiv.restrictNormalHom L.toIntermediateField σ)) ∧
    (∀ (M : CharacterModules k ks) (L : IntermediateField k ks)
      [FiniteDimensional k L] [IsGalois k L]
      (ρ : (L ≃ₐ[k] L) →* End M.obj.V),
      (∀ σ : ks ≃ₐ[k] ks, M.obj.ρ σ = ρ (AlgEquiv.restrictNormalHom L σ)) →
      ∃ d : InvariantHopfModel M.obj.V ρ,
      ∃ i : (E.inverse.obj M).unop.obj ≅ invariantHopfGroup M.obj.V ρ d.hopf,
      ∃ s : (baseChange (K := ks)).obj (invariantHopfGroup M.obj.V ρ d.hopf) ≅
        diagonalizableGroup ks M.obj.V,
      s.inv.hom.hom.left ≫ scalarProjection (invariantHopfGroup M.obj.V ρ d.hopf) =
        Spec.map (CommRingCat.ofHom
          ((AddMonoidAlgebra.mapRingHom M.obj.V (algebraMap L ks)).comp
            (invariantGroupAlgebra M.obj.V ρ).val.toRingHom)) ∧
      ∀ m : M.obj.V,
        (Scheme.ΓSpecIso (.of (AddMonoidAlgebra ks M.obj.V))).hom
          (characterElement (s.inv ≫ (baseChange (K := ks)).map i.inv ≫
            e (E.inverse.obj M).unop ((E.counitIso.app M).inv.hom.hom.hom m))) =
          AddMonoidAlgebra.single m 1) ∧
    (∀ (K Ks : Type u) [Field K] [Field Ks] [Algebra k K] [Algebra K Ks]
      [IsSepClosure K Ks] [Algebra ks Ks] [Algebra k Ks]
      [IsScalarTower k K Ks] [IsScalarTower k ks Ks],
      ∃ ext : ∀ G : FiniteTypeGroups k,
        (E.functor.obj (op G)).obj.V ≃
          ((baseChange (K := Ks)).obj ((baseChange (K := K)).obj G.obj) ⟶
            (baseChange (K := Ks)).obj ((baseChange (K := K)).obj
              (Grp.mk (StandardGroupSchemes.multiplicative k)))),
      (∀ (G : FiniteTypeGroups k) (m : (E.functor.obj (op G)).obj.V),
        IsCharacterExtension (e G m) (ext G m)) ∧
      (∀ (G : FiniteTypeGroups k) (x y : (E.functor.obj (op G)).obj.V),
        (ext G (x + y)).hom.hom = (ext G x).hom.hom * (ext G y).hom.hom) ∧
      (∀ (G H : FiniteTypeGroups k) (f : G ⟶ H)
        (m : (E.functor.obj (op H)).obj.V),
        ext G ((E.functor.map f.op).hom.hom.hom m) =
          (baseChange (K := Ks)).map ((baseChange (K := K)).map f.hom) ≫ ext H m) ∧
      (∀ (τ : Ks ≃ₐ[K] Ks) (σ : ks ≃ₐ[k] ks),
        (∀ a : ks, τ (algebraMap ks Ks a) = algebraMap ks Ks (σ a)) →
        ∀ (G : FiniteTypeGroups k) (m : (E.functor.obj (op G)).obj.V),
          IsConjugate τ (ext G m)
            (ext G (((E.functor.obj (op G)).obj.ρ σ).hom m)))) ∧
    (∀ (K : Type u) [Field K] [Algebra k K] (M : AddCommGrpCat.{u}),
      ∃ s : (baseChange (K := K)).obj (diagonalizableGroup k M) ≅ diagonalizableGroup K M,
        s.inv.hom.hom.left ≫ scalarProjection (diagonalizableGroup k M) =
          Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom M (algebraMap k K)))) := by
  sorry

end AlgebraicGeometry.MultiplicativeType
