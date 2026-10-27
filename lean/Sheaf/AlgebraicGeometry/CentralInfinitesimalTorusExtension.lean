module

public import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Exact.Basic

import Sheaf.AlgebraicGeometry.CommutativeMultiplicativeTypeExtension
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-! # Central infinitesimal extensions of tori

Source: Milne, Algebraic Groups (2017), Corollary 12.22 and Theorem 12.23,
printed pp.239--240; central commutator descent as in Stacks Tag 023M
(blueprint: lem-sfb-central-infinitesimal-torus-extension).

Character modules are identified with actual geometric characters, with their addition,
Galois conjugation, pullback and restriction. No smoothness or reducedness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeType

/-- A central extension of a torus by an infinitesimal multiplicative group is
commutative and of multiplicative type, with its exact geometric character sequence.

Source: Milne, Corollary 12.22 and Theorem 12.23, pp.239--240
(blueprint: lem-sfb-central-infinitesimal-torus-extension).

Proof plan:
1. Extend to the algebraic closure. Tensor pushouts identify the base-changed kernel;
   faithful flatness is preserved by base change. Its augmentation ideal stays nilpotent,
   and centrality holds on all algebras. The torus splits and its multiplicative kernel
   is diagonalizable (lem-sfb-split-torus-subgroups-diagonalizable).
2. The commutator factors through the kernel and agrees on the two pullbacks along
   E times E over T times T, since multiplying either lift by a central kernel element
   does not change its commutator. The degree-zero faithfully flat Amitsur equalizer
   (lem-pc-cech-exact) descends it to T times T.
3. The coordinate ring of the split torus T times T is reduced by
   lem-trf-lattice-torus-coordinates-action and lem-trf-split-lattice-torus-projection.
   Thus the descended map kills the nilpotent augmentation ideal and is the identity
   point. The commutator is trivial. Faithful flatness of field extension and universal
   injectivity descend commutativity to k.
4. Apply lem-sfb-commutative-multiplicative-type-extension to the diagonalizable ends
   over the algebraic closure. Finite generation of characters embeds the resulting
   diagonalizable group in a finite split torus, giving IsMultiplicativeType E.
5. By lem-sfb-multiplicative-character-antiduality, work over a separable closure with
   group algebras K[L] and K[M]. The faithfully flat coordinate map is injective;
   independence of its basis elements makes the character map L to M injective.
6. The kernel has coordinate algebra K[M] tensor over K[L] K, namely
   K[M]/(e_(u(l))-1), canonically K[M/u(L)]. The mutually inverse maps on basis
   labels identify restriction with the quotient M to M/u(L). This gives exactness
   and surjectivity. Both maps commute with conjugation because q and the kernel
   inclusion are defined over k.
7. Characters of a rank-r split torus form Z^r by the group-like-basis lemma;
   scalar-extension compatibility gives freeness and finite rank for X*(T).
   Finiteness of q makes the kernel coordinate algebra finite dimensional, so its
   group-algebra basis has finitely many labels and X*(N) is finite. -/
theorem central_infinitesimal_torus_extension
    {k : Type u} [Field k]
    (E T : Grp (Over (Spec (.of k))))
    [IsAffine E.X.left] [IsAffine T.X.left]
    [LocallyOfFiniteType E.X.hom] [QuasiCompact E.X.hom]
    [LocallyOfFiniteType T.X.hom] [QuasiCompact T.X.hom]
    (q : E ⟶ T) (hT : IsTorus T)
    (hqfinite : q.hom.hom.left.appTop.hom.Finite)
    (hqflat : q.hom.hom.left.appTop.hom.FaithfullyFlat)
    (hlocal : IsLocalRing Γ((GrpObj.ker q.hom.hom).left, ⊤))
    (hnil : IsNilpotent (RingHom.ker
      ((Scheme.ΓSpecIso (.of k)).hom.hom.comp
        (MonObj.one (X := GrpObj.ker q.hom.hom)).left.appTop.hom)))
    (hcentral : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (n : (Spec (.of A)).asOver (Spec (.of k)) ⟶ GrpObj.ker q.hom.hom)
      (e : (Spec (.of A)).asOver (Spec (.of k)) ⟶ E.X),
      Commute (n ≫ GrpObj.kerι q.hom.hom) e)
    (hN : IsMultiplicativeType (Grp.mk (GrpObj.ker q.hom.hom))) :
    IsCommMonObj E.X ∧ IsMultiplicativeType E ∧
    ∀ (ks : Type u) [Field ks] [Algebra k ks] [IsSepClosure k ks],
      ∃ MT ME MN : CharacterModules k ks,
      ∃ eT : MT.obj.V ≃ GeometricCharacters ks T,
      ∃ eE : ME.obj.V ≃ GeometricCharacters ks E,
      ∃ eN : MN.obj.V ≃ GeometricCharacters ks (Grp.mk (GrpObj.ker q.hom.hom)),
        (∀ x y : MT.obj.V, (eT (x + y)).hom.hom = (eT x).hom.hom * (eT y).hom.hom) ∧
        (∀ x y : ME.obj.V, (eE (x + y)).hom.hom = (eE x).hom.hom * (eE y).hom.hom) ∧
        (∀ x y : MN.obj.V, (eN (x + y)).hom.hom = (eN x).hom.hom * (eN y).hom.hom) ∧
        (∀ (σ : ks ≃ₐ[k] ks) (x : MT.obj.V),
          IsConjugate σ (eT x) (eT ((MT.obj.ρ σ).hom x))) ∧
        (∀ (σ : ks ≃ₐ[k] ks) (x : ME.obj.V),
          IsConjugate σ (eE x) (eE ((ME.obj.ρ σ).hom x))) ∧
        (∀ (σ : ks ≃ₐ[k] ks) (x : MN.obj.V),
          IsConjugate σ (eN x) (eN ((MN.obj.ρ σ).hom x))) ∧
        ∃ (p : MT.obj.V →+ ME.obj.V) (r : ME.obj.V →+ MN.obj.V),
          (∀ x : MT.obj.V, eE (p x) = (baseChange (K := ks)).map q ≫ eT x) ∧
          (∀ x : ME.obj.V, eN (r x) = (baseChange (K := ks)).map
            (Grp.ofHom (GrpObj.kerι q.hom.hom)) ≫ eE x) ∧
          (∀ (σ : ks ≃ₐ[k] ks) (x : MT.obj.V),
            p ((MT.obj.ρ σ).hom x) = (ME.obj.ρ σ).hom (p x)) ∧
          (∀ (σ : ks ≃ₐ[k] ks) (x : ME.obj.V),
            r ((ME.obj.ρ σ).hom x) = (MN.obj.ρ σ).hom (r x)) ∧
          Function.Injective p ∧ Function.Exact p r ∧ Function.Surjective r ∧
          Module.Free ℤ MT.obj.V ∧ Module.Finite ℤ MT.obj.V ∧ Finite MN.obj.V := by
  sorry

end AlgebraicGeometry.MultiplicativeType
