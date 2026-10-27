module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientLifting
import Sheaf.AlgebraicGeometry.GroupScheme.BorelSchemeNormalizer
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.GroupScheme.MonomorphismClosedImmersion
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality

/-! # Borel comparison under a multiplicative isogeny

Source: Milne, Algebraic Groups (2017), Proposition 18.18, proof and middle
character row, printed p.391.
(blueprint: lem-sfb-multiplicative-isogeny-borel-comparison)

The inverse image and kernel are specified by cartesian squares. The quotient
maps exhibit sheafifications of the right-coset presheaves. Characters are actual
group-scheme homomorphisms to the recorded Laurent multiplicative group; their
abelian law is multiplication of values. Exactness is written as injectivity,
the image-equals-trivial-restriction criterion, and surjectivity.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Inverse-image Borels, the canonical flag-quotient isomorphism, and the short
exact sequence of Borel characters for a multiplicative isogeny.

Source: Milne, Proposition 18.18, proof and middle exact row, printed p.391.
(blueprint: lem-sfb-multiplicative-isogeny-borel-comparison)

Proof plan:
1. The kernel N is normal. Apply
   lem-sfb-connected-action-multiplicative-type-rigidity to conjugation by G₁
   to make N central scheme-theoretically. The lifting theorem
   lem-sfb-borel-quotient-lifting gives B mapping faithfully flat onto B₀.
   The scheme normalizer theorem lem-sfb-borel-scheme-normalizer puts N in B.
2. For g in f⁻¹B₀, lift f(g) locally to b in B. Then gb⁻¹ belongs to N,
   hence g belongs to B locally. Base change of fppf coverings and representable
   fpqc descent identify B with the full inverse image, including nilpotents.
   The kernel square gives ker(f_B) = N and faithful flatness is inherited.
3. Use lem-sfb-homogeneous-orbit-quotient-geometry for the two represented
   coset sheafifications. The homomorphism factorization theorem makes f fppf:
   its closed-immersion factor has zero defining ideal by faithful flatness.
   Lift cosets locally along f and descend. Two lifts differ by B₁ exactly when
   their images differ by B₀. Yoneda gives the inverse scheme isomorphisms,
   with the stated equation on quotient maps.
4. Apply lem-sfb-faithfully-flat-group-quotient-universal to f_B. Characters
   trivial on N descend uniquely, giving injectivity and middle exactness.
5. Lie--Kolchin (lem-sfb-lie-kolchin-triangular-embedding) and
   lem-sfb-triangular-diagonal-kernel give B₁ → D with unipotent kernel V.
   The intersection N ∩ V is unipotent and maps trivially to N by
   lem-sfb-unipotent-to-multiplicative-trivial, hence is trivial as a scheme.
   Thus N → D is a closed immersion by the group monomorphism theorem.
6. Apply lem-sfb-multiplicative-character-antiduality: characters of D
   surject onto characters of N. Composing an extension with B₁ → D proves
   the asserted surjectivity. No reducedness of N is used. -/
theorem multiplicativeIsogeny_borel_comparison
    {F : Type u} [Field F] [IsAlgClosed F]
    (G₁ G₀ : Grp (Over (Spec (.of F))))
    [IsAffine G₁.X.left] [IsAffine G₀.X.left]
    [LocallyOfFiniteType G₁.X.hom] [QuasiCompact G₁.X.hom]
    [LocallyOfFiniteType G₀.X.hom] [QuasiCompact G₀.X.hom]
    [Smooth G₁.X.hom] [ConnectedSpace G₁.X.left]
    [Smooth G₀.X.hom] [ConnectedSpace G₀.X.left]
    (f : G₁ ⟶ G₀) (hf : f.hom.hom.left.appTop.hom.FaithfullyFlat)
    [IsFinite (GrpObj.ker f.hom.hom).hom]
    (hN : IsFiniteDiagonalizableGroupScheme (GrpObj.ker f.hom.hom))
    (B₀ : Grp (Over (Spec (.of F)))) (i₀ : B₀ ⟶ G₀)
    (hB₀ : IsBorelGroupScheme i₀.hom.hom) :
    ∃ (B₁ : Grp (Over (Spec (.of F)))) (i₁ : B₁ ⟶ G₁) (fB : B₁ ⟶ B₀)
      (n : Grp.mk (GrpObj.ker f.hom.hom) ⟶ B₁),
      IsPullback i₁.hom.hom fB.hom.hom f.hom.hom i₀.hom.hom ∧
      IsBorelGroupScheme i₁.hom.hom ∧
      fB.hom.hom.left.appTop.hom.FaithfullyFlat ∧
      n.hom.hom ≫ i₁.hom.hom = GrpObj.kerι f.hom.hom ∧
      IsPullback n.hom.hom (toUnit (GrpObj.ker f.hom.hom)) fB.hom.hom η[B₀.X] ∧
      Function.Injective
        (fun χ : B₀ ⟶ Grp.mk (StandardGroupSchemes.multiplicative F) ↦ fB ≫ χ) ∧
      (∀ χ : B₁ ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
        n.hom.hom ≫ χ.hom.hom =
            toUnit (GrpObj.ker f.hom.hom) ≫ η[StandardGroupSchemes.multiplicative F] ↔
          ∃ ψ : B₀ ⟶ Grp.mk (StandardGroupSchemes.multiplicative F), fB ≫ ψ = χ) ∧
      Function.Surjective
        (fun χ : B₁ ⟶ Grp.mk (StandardGroupSchemes.multiplicative F) ↦ n ≫ χ) ∧
      ∃ (Q₁ Q₀ : Over (Spec (.of F))) (q₁ : G₁.X ⟶ Q₁) (q₀ : G₀.X ⟶ Q₀),
        Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q₁) ∧
        Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q₀) ∧
        (∃ η₁ : coequalizer (yoneda.map (fst G₁.X B₁.X))
            (yoneda.map (lift (fst G₁.X B₁.X)
              (snd G₁.X B₁.X ≫ i₁.hom.hom) ≫ μ[G₁.X])) ⟶ yoneda.obj Q₁,
          coequalizer.π _ _ ≫ η₁ = yoneda.map q₁ ∧
          ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
            Function.Bijective (fun a : yoneda.obj Q₁ ⟶ Z.obj ↦ η₁ ≫ a)) ∧
        (∃ η₀ : coequalizer (yoneda.map (fst G₀.X B₀.X))
            (yoneda.map (lift (fst G₀.X B₀.X)
              (snd G₀.X B₀.X ≫ i₀.hom.hom) ≫ μ[G₀.X])) ⟶ yoneda.obj Q₀,
          coequalizer.π _ _ ≫ η₀ = yoneda.map q₀ ∧
          ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
            Function.Bijective (fun a : yoneda.obj Q₀ ⟶ Z.obj ↦ η₀ ≫ a)) ∧
        ∃ e : Q₁ ≅ Q₀, q₁ ≫ e.hom = f.hom.hom ≫ q₀ := by
  sorry

end AlgebraicGeometry
