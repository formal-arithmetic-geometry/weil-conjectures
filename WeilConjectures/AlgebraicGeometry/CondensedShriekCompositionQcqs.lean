/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionDefs
import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionExistence
import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionSeparatedAgreement
import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionFormal
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian

/-! # Condensed compact-support composition over quasi-separated bases

Source: latest blueprint, lem-zl-shriek-composition.proof, and
sk-thm-sf-comp-composition (1),(2); Stacks Tag 0F7J, lemma-shriek-composition
(blueprint: lem-zl-condensed-shriek-composition-qcqs).

The witnesses below retain the actual compactification functors, proper-refinement maps,
normalized proper/open compositor, and the proper/open isomorphism exchange. All categories
are full subcategories of the ordinary derived category with the pulled-back condensed ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

open CompactSupportComposition

variable (ℓ : ℕ) [Fact ℓ.Prime]

private theorem geometricHeart (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
    [QuasiCompact T₀.hom] [QuasiSeparated T₀.hom] :
    (bc ℓ (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).left)).IsTriangulated := by
  let := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have : Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩
  have : Fact (ringChar D.k ≠ ℓ) := ⟨by rw [ringChar.eq D.k D.p]; exact hℓ.symm⟩
  let T := (Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀
  have : LocallyOfFiniteType T.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd T₀.hom _))
  have : QuasiCompact T.hom := inferInstanceAs (QuasiCompact (pullback.snd T₀.hom _))
  have : QuasiSeparated T.hom := inferInstanceAs (QuasiSeparated (pullback.snd T₀.hom _))
  exact (condensedQcqsConstructibleHeart ℓ D.k T).1

private theorem frobeniusSquare (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :
    IsPullback (StrictWeil.modelFrobenius D X₀).hom (modelMap D f₀)
      (modelMap D f₀) (StrictWeil.modelFrobenius D Y₀).hom := by
  exact (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1

set_option maxHeartbeats 2000000 in
-- Allow elaboration of the native internal-module derived functor composites.
/-- The canonical compactification composition isomorphism and isomorphism exchange on
ordinary Dbc over quasi-separated finite-type finite-field models. This includes the
semilinear geometric Frobenius specialization and the separated-scheme identification.
Source: latest blueprint lem-zl-shriek-composition.proof and sk-thm-sf-comp-composition
(1),(2); Stacks 0F7J, lemma-shriek-composition
(blueprint: lem-zl-condensed-shriek-composition-qcqs).

Proof plan, following the seven DAG steps:
1. Base change separated finite-type maps and qcqs models. Nagata and the compatible
compactification triangle supply a proper/open tower, without absolute separatedness.
2. Use Gamma from lem-zl-condensed-open-proper-pasting (b). Its open transpose is inverse
restriction, hence the uniquely normalized interchange of lem-sf-condensed-proper-open-
interchange. It is invertible on Dbc=Dctf (lem-integral-ctf-equals-bc). Apply the outer
proper image and the canonical proper/open compositors to obtain alpha.
3. Use precisely the normalized proper-refinement maps of the boundedness node.
Identity and pasting give their cocycle. Common refinements and the tower-refinement
lemma show independence of the tower and of all three compactifications.
4. Reindex pro-etale objects by an arbitrary scheme isomorphism and its inverse.
The canonical coefficient comparisons give exact inverse module equivalences. Termwise
derivation is t-exact; finite local models and stratifications pull back and back again.
5. Pull back a compactification along the target automorphism. Compose proper exchange,
open exchange B and the prescribed refinement comparison. The mixed cube and cocycle
make this independent of the model. The qcqs calculus gives shift compatibility, and
naturality gives a morphism of image triangles, including the connecting arrow.
6. Expand alpha and beta on a compatible tower. Mate-pasting cancels adjacent units and
counits; the remaining middle square is the mixed cube of open-proper-pasting (c).
Whiskering gives precisely comp_exchange, as an equality of global derived arrows.
7. Put phi_out=Rf_!(phi) composed with beta. Naturality transports equivariant maps;
comp_exchange and alpha naturality prove the WeilCompatibility equation. Specialize to
StrictWeil.modelFrobenius, the semilinear inverse-q-power automorphism. On separated
models the open-adjunction transpose is exactly that of sk-thm-sf-comp-composition;
uniqueness identifies alpha, beta and all refinements with its normalized system.
Taking the inverse compositor gives the constraint of lem-zl-shriek-composition. -/
theorem condensedShriekCompositionQcqs
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    (X₀ Z₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left] :
    Exists fun [(bc ℓ
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj
        X₀).left)).IsTriangulated] ↦
    Exists fun [(bc ℓ
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj
        Z₀).left)).IsTriangulated] ↦
    Exists fun [(bc ℓ
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj
        Y₀).left)).IsTriangulated] ↦
      ∃ H : Comparisons ℓ (modelMap D h₀) (modelMap D g₀),
        ExactCompatibility ℓ H ∧
        (∃ (shsq : IsPullback (StrictWeil.modelFrobenius D X₀).hom (modelMap D h₀)
            (modelMap D h₀) (StrictWeil.modelFrobenius D Z₀).hom)
          (sgsq : IsPullback (StrictWeil.modelFrobenius D Z₀).hom (modelMap D g₀)
            (modelMap D g₀) (StrictWeil.modelFrobenius D Y₀).hom),
          WeilCompatibility ℓ H (StrictWeil.modelFrobenius D X₀)
            (StrictWeil.modelFrobenius D Z₀) (StrictWeil.modelFrobenius D Y₀) shsq sgsq) ∧
        (∀ [IsSeparated X₀.hom] [IsSeparated Z₀.hom] [IsSeparated Y₀.hom],
          SeparatedAgreement ℓ D hℓ h₀ g₀ H) := by
  have := geometricHeart ℓ D hℓ X₀
  have := geometricHeart ℓ D hℓ Z₀
  have := geometricHeart ℓ D hℓ Y₀
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨A, hs⟩ := qcqsCompositionDataExists ℓ D hℓ h₀ g₀
  have hf := formalCompatibility ℓ A hs
  refine ⟨A, hf.1, ?_, ?_⟩
  · exact ⟨frobeniusSquare D h₀, frobeniusSquare D g₀,
      hf.2 _ _ _ (frobeniusSquare D h₀) (frobeniusSquare D g₀)⟩
  · exact qcqsSeparatedAgreement ℓ D hℓ h₀ g₀ A

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
