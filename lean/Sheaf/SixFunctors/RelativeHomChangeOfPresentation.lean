module

public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Change of compact-support presentation in the relative Hom bijection

Source: blueprint main-20261015, thm-sf-ambient-adjoint-class.proof.md, four-factor
Hom chain and final compactification-comparison paragraph
(blueprint: lem-coef-relative-hom-change-of-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Supply the already established finiteness of the positive-level coefficient ring
as an instance. This is the dependency's actual finite-ring evidence.
Source: blueprint global coefficient datum, def-weil-l-adic-coefficient-extension
(blueprint: lem-coef-relative-hom-change-of-presentation). -/
instance presentationChangeCoefficientsFinite (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [hn : Fact (1 ≤ n)] :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n hn.out

/-- The comparison B_G is S_Y(e_G inverse), followed by the inverse canonical
compact-support comparison, followed by q at S_X G. The comparison used here is
exactly the specified counit-mate normalization of the relative Hom datum.
Source: blueprint main-20261015, thm-sf-ambient-adjoint-class.proof.md, Hom chain
(blueprint: lem-coef-relative-hom-change-of-presentation). -/
def relativeHomPresentationComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅ F)
    (q : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅ Q)
    (G : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj (F.obj G.obj) ≅
      Q.obj ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj G.obj) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
      (e.app G.obj).symm ≪≫
    ((fixedCompactSupportComparisonIso A c).app G).symm ≪≫
      q.app ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj G.obj)

/-- Changing both compact-support presentations conjugates the specified relative
Hom bijection by the counit-compatible adjunction conjugate. All four displayed
Hom maps are bijective on the stated bounded-below domains. The comparison-class
datum retains its normalization equation, so its Hom map is the specified chain.
Source: blueprint main-20261015, thm-sf-ambient-adjoint-class.proof.md, Hom chain
(blueprint: lem-coef-relative-hom-change-of-presentation).

Proof:
1. G is bounded below, so S_X G is bounded below of etale origin with identity
   witness. The canonical compact-support comparison is invertible. Precomposition
   with B_G is therefore bijective. The comparison and etale adjunctions supply
   the next two bijections. Full faithfulness of comparison on D+ supplies the
   last, because I U_Y M is bounded below. The isomorphisms e and the conjugate r
   also put F_c G and I_c U_Y M in D+.
2. The normalization field of the given comparison-class datum writes Phi_c(h)
   as S_X(beta_c(a(h))), where a(h) = eta_Y ≫ U_Y(C_c inverse ≫ h).
   The identity witness introduces no extra conjugation.
3. Put h = q ≫ g and v = eta_Y ≫ U_Y(B_G ≫ g). The definition of B_G and
   naturality of the actual comparison unit give a(h) = e_G ≫ v.
4. The conjugate of e inverse satisfies F(r_N) ≫ epsilon_N =
   e inverse at I_c N ≫ epsilon_c,N. Transpose r_N after beta_c(a) using this
   equation and naturality of e inverse. Its inverse beta-transpose is
   e_G inverse ≫ a, hence beta_c(a) ≫ r_N = beta(e_G inverse ≫ a).
5. Substitute a(h) and apply S_X. This gives the displayed identity for every g.
   Every factor is natural: B is assembled from natural comparisons, the next
   two factors are adjunction Hom maps, and the last is the functor's Hom map.
   Only the bounded etale-origin relative adjunction is used. -/
theorem relativeHom_changeOfPresentation
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f) (d : ℕ)
    (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (Ic : DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) ⥤
      DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (adjc : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c ⊣ Ic)
    (Φ : ComparisonClassAdjunction (Padic.coefficientExtensionRing l E n) f c Ic adjc
      (DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X)
      DerivedCategory.TStructure.t.plus)
    (F : DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) ⥤
      DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (Q : DerivedCategory
        (Sheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) ⥤
      DerivedCategory
        (Sheaf (Scheme.ProEt.topology Y)
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (I : DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) ⥤
      DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (e : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c ≅ F)
    (q : rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c ≅ Q)
    (β : F ⊣ I)
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (M : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (_hFG : DerivedCategory.TStructure.t.plus (F.obj G.obj))
    (_hIU : DerivedCategory.TStructure.t.plus
      (I.obj ((comparisonLowerStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).rightDerivedFunctor.obj
          M.obj))) :
    (∀ g : Q.obj ((comparisonUpperStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X).mapDerivedCategory.obj
            G.obj) ⟶ M.obj,
      Φ.homEquiv c _
          (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj G.property) M.obj M.property
          (q.hom.app _ ≫ g) ≫
        (comparisonUpperStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X).mapDerivedCategory.map
            ((conjugateIsoEquiv adjc β e.symm).hom.app
              ((comparisonLowerStar
              (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).rightDerivedFunctor.obj
                M.obj)) =
      (comparisonUpperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X).mapDerivedCategory.map
          (β.homEquiv G.obj _
            ((derivedComparisonAdjunction
                (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).unit.app
                  (F.obj G.obj) ≫
              (comparisonLowerStar
              (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).rightDerivedFunctor.map
                  ((relativeHomPresentationComparison
                    (Padic.coefficientExtensionRing l E n) c F Q e q G).hom ≫ g)))) ∧
      Function.Bijective (fun g : Q.obj ((comparisonUpperStar
            (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X).mapDerivedCategory.obj
              G.obj) ⟶ M.obj ↦
        (relativeHomPresentationComparison
          (Padic.coefficientExtensionRing l E n) c F Q e q G).hom ≫ g) ∧
      Function.Bijective (fun b : (comparisonUpperStar
            (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).mapDerivedCategory.obj
              (F.obj G.obj) ⟶ M.obj ↦
        (derivedComparisonAdjunction
            (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).unit.app (F.obj G.obj) ≫
          (comparisonLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).rightDerivedFunctor.map b) ∧
      Function.Bijective (β.homEquiv G.obj
        ((comparisonLowerStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).rightDerivedFunctor.obj
            M.obj)) ∧
      Function.Bijective (fun a : G.obj ⟶ I.obj ((comparisonLowerStar
            (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) Y).rightDerivedFunctor.obj
              M.obj) ↦
        (comparisonUpperStar
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X).mapDerivedCategory.map
            a) := by
  sorry

end AlgebraicGeometry.ProEtale
