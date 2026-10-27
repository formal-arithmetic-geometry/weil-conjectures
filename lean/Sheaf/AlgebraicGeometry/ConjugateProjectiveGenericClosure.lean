module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.IntegralChowRelativelyAmple
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Conjugate projective products and their integral generic closures

Source: ILO, Travaux de Gabber, Exposé X, Theorem 3.4, Step 4, pp. 160--161,
and its agent conjugate-product expansion; Stacks Tags 0201, 01WD and 01J3.
(blueprint: lem-sfb-conjugate-projective-generic-closure)

The limiting cone has one factor `B` indexed by `none` and one twisted copy of `Y`
for each `some j`. A reduced closed immersion with the indicated image represents
the reduced induced closure, uniquely up to its unique isomorphism over the product.
The normalization equations on every generic-fibre isomorphism record the specified
identifications, including the function-field identification induced by the generic map.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The equivariant conjugate product and reduced generic graph closure.

Source: ILO, Exposé X, Theorem 3.4, Step 4, pp. 160--161 (agent expansion);
Stacks Tags 0201 (2),(3), 01WD and 01J3.
(blueprint: lem-sfb-conjugate-projective-generic-closure)

Proof, following the eleven steps of the node:
1. Projectivity makes S proper over k, hence T is proper over k. Apply integral Chow
   (lem-weil-pbc-integral-chow-relatively-ample). Its immersion into projective space
   is proper over the separated target, hence closed, giving the projective Y and π.
2. The unique point of T_K is its generic point, which belongs to the open where π
   is an isomorphism. Base change therefore gives Y_K = Spec L, compatibly with π.
   The specified embedding L → M then gives f (integral affine function-field lemma).
3. Put s_M = u η_B = v f. Equivariance gives s_M d_j = h_j s_M, hence all the
   proposed q-components have common base s_M and define q by the universal property.
   Twisting a projective embedding by the base-field automorphism embeds each Y_j
   in the same projective space (projective-space base-change construction).
4. The projective-fibre-product closed-model lemma embeds the finite product of Y_j.
   Separatedness of S embeds P into B ×_k that product. Product embeddings followed
   by the Segre embedding (lem-chow-segre) give a projective embedding of P.
5. Define g_P on B by a_g and on the j-factor by p_(g⁻¹j). The common-base
   identities define this morphism. Projection uniqueness proves the group laws and
   inverse formula, and proves that it lies over h_g, hence is semilinear on k.
6. Compare the B- and j-projections: a_g η_B = η_B d_g and
   f d_((g⁻¹j)⁻¹) = f d_(j⁻¹) d_g. Thus q is equivariant and its image is fixed.
7. The reduced induced closure of this point is integral. Its closed embedding in P
   makes it projective and finite type. Reduced-source factorization through closed
   subschemes restricts each g_P to C; uniqueness gives the action laws and equivariance
   of C → S (lem-weil-pbc-reduced-induced-closed-subscheme and reduced-source lemma).
8. P → B is proper over the separated B. On the generic fibre, q is a section of
   that separated projection, hence a closed immersion with residue field exactly M
   (proper base change and section-of-separated closed-immersion lemmas).
9. On an affine chart Spec R over Spec A containing q(*), the closure ideal is
   I = ker(R → M). Localizing at A \ {0} commutes with this kernel; the closed
   immersion in step 8 identifies the localized quotient with M. Charts missing
   q(*) miss its closure too. These identifications glue to C_K = Spec M.
10. The same calculation identifies Frac(R/I) with M, hence k(C) with M by the
   integral affine function-field lemma. All maps are induced by q, so its equivariance
   makes both identifications compatible with the given action σ, via Spec(σ⁻¹).
11. At the identity index the twist is v itself. The cone relation therefore gives
   v c = p and r π c = p, as k-morphisms. No action on Y or T is used. -/
theorem exists_conjugate_projective_generic_closure
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (ρS : S ⟶ Spec (.of k)) [IsHProjective ρS]
    [LocallyOfFiniteType ρS] [QuasiCompact ρS]
    (J : Type v) [Group J] [Finite J]
    (h : J →* Aut S) (τ : J →* (k ≃+* k))
    (hS : ∀ j : J, (h j).hom ≫ ρS =
      ρS ≫ Spec.map (CommRingCat.ofHom (τ j).symm.toRingHom))
    (B : Scheme.{u}) [IsIntegral B] (ρB : B ⟶ Spec (.of k))
    [IsHProjective ρB] [LocallyOfFiniteType ρB] [QuasiCompact ρB]
    (uB : B ⟶ S) [IsFinite uB] (huB : uB ≫ ρS = ρB)
    (M : Type u) [Field M] [Algebra S.functionField M] [Module.Finite S.functionField M]
    (ηB : Spec (.of M) ⟶ B)
    (eB : Spec (.of M) ≅ pullback uB (S.fromSpecStalk (genericPoint S)))
    (heB : eB.hom ≫ pullback.fst _ _ = ηB)
    (heBK : eB.hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField M)))
    (a : J →* Aut B) (σ : J →* (M ≃+* M))
    (hB : ∀ j : J, (a j).hom ≫ ρB =
      ρB ≫ Spec.map (CommRingCat.ofHom (τ j).symm.toRingHom))
    (hu : ∀ j : J, (a j).hom ≫ uB = uB ≫ (h j).hom)
    (hη : ∀ j : J, ηB ≫ (a j).hom =
      Spec.map (CommRingCat.ofHom (σ j).symm.toRingHom) ≫ ηB)
    (T : Scheme.{u}) [IsIntegral T] (ρT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType ρT] [QuasiCompact ρT]
    (r : T ⟶ S) [IsProper r] (hr : r ≫ ρS = ρT)
    (L : Type u) [Field L] [Algebra S.functionField L] [Module.Finite S.functionField L]
    (eT : Spec (.of L) ≅ pullback r (S.fromSpecStalk (genericPoint S)))
    (heTK : eT.hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)))
    (ι : L →ₐ[S.functionField] M) :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (ρY : Y ⟶ Spec (.of k)) (π : Y ⟶ T),
      IsHProjective ρY ∧ LocallyOfFiniteType ρY ∧ QuasiCompact ρY ∧
      IsProper π ∧ Surjective π ∧ π ≫ ρT = ρY ∧
      (∃ U : T.Opens, (U : Set T).Nonempty ∧ IsIso (π ∣_ U)) ∧
      ∃ (eY : Spec (.of L) ≅ pullback (π ≫ r) (S.fromSpecStalk (genericPoint S)))
        (f : Spec (.of M) ⟶ Y),
        eY.hom ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ∧
        eY.hom ≫ pullback.fst _ _ ≫ π = eT.hom ≫ pullback.fst _ _ ∧
        f = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ eY.hom ≫ pullback.fst _ _ ∧
        ∃ D : WidePullbackCone (X := S)
            (Y := fun t : Option J ↦ match t with | none => B | some _ => Y)
            (fun t ↦ match t with | none => uB | some j => π ≫ r ≫ (h j).hom),
          Nonempty (IsLimit D) ∧ IsHProjective (D.base ≫ ρS) ∧
          ∃ (q : Spec (.of M) ⟶ D.pt) (A : J →* Aut D.pt),
            q ≫ D.π none = ηB ∧
            (∀ j : J, q ≫ D.π (some j) =
              Spec.map (CommRingCat.ofHom (σ j⁻¹).symm.toRingHom) ≫ f) ∧
            (∀ g : J, (A g).hom ≫ D.π none = D.π none ≫ (a g).hom) ∧
            (∀ g j : J, (A g).hom ≫ D.π (some (g * j)) = D.π (some j)) ∧
            (∀ g : J, (A g).hom ≫ D.base = D.base ≫ (h g).hom) ∧
            (∀ g : J, (A g).hom ≫ D.base ≫ ρS =
              D.base ≫ ρS ≫ Spec.map (CommRingCat.ofHom (τ g).symm.toRingHom)) ∧
            (∀ g : J, q ≫ (A g).hom =
              Spec.map (CommRingCat.ofHom (σ g).symm.toRingHom) ≫ q) ∧
            ∃ (C : Scheme.{u}) (_ : IsIntegral C) (i : C ⟶ D.pt)
              (AC : J →* Aut C) (qC : Spec (.of M) ⟶ C)
              (eC : C.functionField ≅ CommRingCat.of M)
              (eCK : Spec (.of M) ≅
                pullback (i ≫ D.base) (S.fromSpecStalk (genericPoint S)))
              (c : C ⟶ Y),
              IsClosedImmersion i ∧
              i.ker = Scheme.IdealSheafData.vanishingIdeal
                ⟨closure (Set.range q), isClosed_closure⟩ ∧
              Set.range i = closure (Set.range q) ∧
              IsHProjective (i ≫ D.base ≫ ρS) ∧
              LocallyOfFiniteType (i ≫ D.base ≫ ρS) ∧ QuasiCompact (i ≫ D.base ≫ ρS) ∧
              (∀ g : J, (AC g).hom ≫ i = i ≫ (A g).hom) ∧
              (∀ g : J, (AC g).hom ≫ i ≫ D.base = i ≫ D.base ≫ (h g).hom) ∧
              qC ≫ i = q ∧
              (∀ g : J, qC ≫ (AC g).hom =
                Spec.map (CommRingCat.ofHom (σ g).symm.toRingHom) ≫ qC) ∧
              qC = Spec.map eC.hom ≫ C.fromSpecStalk (genericPoint C) ∧
              eCK.hom ≫ pullback.fst _ _ = qC ∧
              eCK.hom ≫ pullback.snd _ _ =
                Spec.map (CommRingCat.ofHom (algebraMap S.functionField M)) ∧
              c = i ≫ D.π (some 1) ∧
              c ≫ π ≫ r = i ≫ D.base ∧ c ≫ ρY = i ≫ D.base ≫ ρS := by
  sorry

end AlgebraicGeometry
