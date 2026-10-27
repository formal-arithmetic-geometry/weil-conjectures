module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Split Bruhat affine stratification over arbitrary fields

Source: Milne, Algebraic Groups (2017), Section 21h, Proposition 21.70,
Theorems 21.73, 21.80 and 21.84, printed pp.446--451; Theorems 5.28 and 17.9
for the represented quotient and its projective geometry.
(blueprint: lem-sfb-split-bruhat-affine-stratification).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The canonical projection onto a represented sheafification of right cosets.
It is the Yoneda preimage of the coequalizer projection followed by the given
sheafification map, so its base changes are specified without any choice of a map.
Source: Milne, Definition 5.20 and Theorem 5.28, pp.104--105
(blueprint: lem-sfb-split-bruhat-affine-stratification). -/
def splitFlagQuotientProjection {F : Type u} [Field F]
    (H B : Grp (Over (Spec (.of F)))) (iB : B ⟶ H)
    (Q : Over (Spec (.of F)))
    (ηQ : coequalizer (yoneda.map (fst H.X B.X))
      (yoneda.map (fst H.X B.X * (snd H.X B.X ≫ iB.hom.hom))) ⟶ yoneda.obj Q) :
    H.X ⟶ Q :=
  yoneda.preimage (coequalizer.π (yoneda.map (fst H.X B.X))
    (yoneda.map (fst H.X B.X * (snd H.X B.X ≫ iB.hom.hom))) ≫ ηQ)

/-- The split flag quotient is smooth projective geometrically integral and admits
an affine stratification with a unique dense open stratum. The same cells and dimensions
work after every field extension. The quotient after extension is characterized by the
sheafification universal property with its projection pinned to the pullback of the
original projection. The maximality hypothesis is over F itself, as in the node;
no algebraic closedness or perfectness is imposed. The last implication is the torus case.

Source: Milne, Section 21h, Proposition 21.70 and Theorems 21.73, 21.80 and 21.84,
pp.446--451; Theorems 5.28, 17.9 and 4.27 for quotient projectivity.
(blueprint: lem-sfb-split-bruhat-affine-stratification).

Proof plan, following the six steps of the node:
1. Apply lem-sfb-algebraic-group-homogeneous-quotient. The coset fibres and local
   lifts identify its quotient with Q by lem-weil-pbc-fpqc-representable-descent.
   The same kernel relation and lifts after extension identify the pulled-back
   projection with the sheaf quotient by B_L, giving the canonical identification.
2. By lem-sfb-split-flag-rational-fixed-scheme, B remains Borel over the algebraic
   closure. Apply lem-sfb-borel-quotient-proper-geometry, then descend smoothness
   and properness by lem-trf-smooth-fpqc-base-descent and
   lem-weil-pbc-proper-single-fpqc-descent. After every extension the quotient is
   smooth, hence regular by lem-weil-pbc-smooth-scheme-over-field-regular. Its
   surjective projection has connected source and contains the identity coset.
   Use lem-weil-pbc-surjective-base-change and lem-sc-regular-connected-integral.
3. By lem-sfb-chevalley-scheme-line-stabilizer choose a representation with line
   stabilizer B. Descend its orbit map to projective space by fpqc representable
   descent. Equality of lines means equality modulo B on every test algebra, so
   the map is mono. Projective space is separated by
   lem-weil-pbc-projective-space-proj-separated. By lem-weil-pbc-proper-over-separated
   and lem-pc-proper-monomorphism-closed it is a closed immersion. Quasi-compactness
   gives projectivity in def-pc-projective-morphism.
4. Apply lem-sfb-split-torus-representation-weight-decomposition and
   lem-sfb-projective-torus-fixed-weight-schemes to choose a separating cocharacter.
   By lem-sfb-split-flag-rational-fixed-scheme its fixed scheme is finite constant,
   with rational reduced points, including over finite and imperfect fields.
5. Apply lem-sfb-rational-projective-attracting-cells: its attracting schemes are
   locally closed affine spaces partitioning Q, with exactly one dense open cell
   and no other cell having closure Q. No closure-incidence assertion is needed.
6. The scalar-extension clause of that attracting-cell theorem gives precisely
   the pulled-back cells with the same dimensions and distinguished index.
   Smoothness persists by lem-pc-proper-base-change; base change the projective
   embedding for projectivity. Step 2 gives integrality over every extension.
   If H=T, then B=H, the quotient sheaf is terminal and Q is Spec F. The fixed-point
   index is a singleton and its sole cell has dimension zero. -/
theorem exists_split_bruhat_affine_stratification
    {F : Type u} [Field F]
    (H T B : Grp (Over (Spec (.of F))))
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (iT : T ⟶ H) (iB : B ⟶ H) (j : T ⟶ B) (hj : j ≫ iB = iT)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hTs : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hBclosed : IsClosedSubgroupScheme iB.hom.hom)
    (hBsplit : IsSplitSolvable B)
    (hBmax : ∀ (D : Grp (Over (Spec (.of F)))) (l : D ⟶ H),
      IsClosedSubgroupScheme l.hom.hom → Smooth D.X.hom → ConnectedSpace D.X.left →
      SolvableGroupStructure.IsSolvable D →
      (∃ f : B ⟶ D, f ≫ l = iB) → ∃ r : D ⟶ B, r ≫ iB = l)
    (Q : Over (Spec (.of F)))
    (ηQ : coequalizer (yoneda.map (fst H.X B.X))
      (yoneda.map (fst H.X B.X * (snd H.X B.X ≫ iB.hom.hom))) ⟶ yoneda.obj Q)
    (hηQ : ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηQ ≫ f)) :
    Smooth Q.hom ∧ IsProjective Q.hom ∧ GeometricallyIntegral Q.hom ∧
    ∃ (S : Scheme.FiniteLocallyClosedStratification Q.left)
      (n : Fin S.n → ℕ) (a₀ : Fin S.n),
      (∀ a, Nonempty (Over.mk (S.immersion a ≫ Q.hom) ≅
        (AffineSpace (ULift.{u} (Fin (n a))) (Spec (.of F))).asOver (Spec (.of F)))) ∧
      IsOpenImmersion (S.immersion a₀) ∧
      (∀ a, closure (S.stratum a) = Set.univ ↔ a = a₀) ∧
      (∀ (L : Type u) [Field L] [Algebra F L],
        Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q).hom ∧
        IsProjective ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj
          Q).hom ∧
        GeometricallyIntegral ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q).hom ∧
        (∀ a, IsImmersion (pullback.snd (S.immersion a)
          (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L)))))) ∧
        (∀ x : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q).left,
          ∃! a : Fin S.n, x ∈ Set.range (pullback.snd (S.immersion a)
            (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L)))))) ∧
        (∀ a, ∃ e : pullback (S.immersion a)
            (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L)))) ≅
            AffineSpace (ULift.{u} (Fin (n a))) (Spec (.of L)),
          e.hom ≫ (AffineSpace (ULift.{u} (Fin (n a))) (Spec (.of L))) ↘ Spec (.of L) =
            pullback.snd (S.immersion a)
              (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L)))) ≫
                ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q).hom) ∧
        IsOpenImmersion (pullback.snd (S.immersion a₀)
          (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))) ∧
        (∀ a, closure (Set.range (pullback.snd (S.immersion a)
          (pullback.fst Q.hom (Spec.map (CommRingCat.ofHom (algebraMap F L)))))) =
            Set.univ ↔ a = a₀) ∧
        ∃ ηL : coequalizer
            (yoneda.map (fst ((MultiplicativeType.baseChange (K := L)).obj H).X
              ((MultiplicativeType.baseChange (K := L)).obj B).X))
            (yoneda.map (fst ((MultiplicativeType.baseChange (K := L)).obj H).X
                ((MultiplicativeType.baseChange (K := L)).obj B).X *
              (snd ((MultiplicativeType.baseChange (K := L)).obj H).X
                ((MultiplicativeType.baseChange (K := L)).obj B).X ≫
                ((MultiplicativeType.baseChange (K := L)).map iB).hom.hom))) ⟶
            yoneda.obj ((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q),
          (coequalizer.π _ _ ≫ ηL = yoneda.map
            ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).map
              (splitFlagQuotientProjection H B iB Q ηQ))) ∧
          (∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of L))) (Type u),
            Function.Bijective (fun f : yoneda.obj ((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj Q) ⟶ Z.obj ↦ ηL ≫ f))) ∧
      (IsIso iT → S.n = 1 ∧ n a₀ = 0 ∧
        Nonempty (Q ≅ Over.mk (𝟙 (Spec (.of F))))) := by
  sorry

end AlgebraicGeometry
