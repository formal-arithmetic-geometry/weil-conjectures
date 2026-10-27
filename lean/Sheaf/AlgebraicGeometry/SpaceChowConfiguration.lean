/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Compactified distinct-tuple configuration of an affine étale atlas

Source: Stacks Project, spaces-cohomology.tex, Tag 089J, lemma-weak-chow, construction
of V, Z, Xprime and its glued map, and the coordinate-completeness paragraph
(blueprint: lem-sfb-space-chow-configuration).

The auxiliary definitions merely put a scheme and a scheme map over Spec Z. The theorem
specifies F by its sheaf-valued universal property, V by the equality diagonals, and Z
by Mathlib's scheme-theoretic image. Its final coproduct is a coproduct of schemes over
the field, with each injection specified by the corresponding coordinate, also after
an arbitrary field extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The absolute base Spec Z in the scheme universe.
Source: Stacks, Tag 089J (blueprint: lem-sfb-space-chow-configuration). -/
abbrev chowConfigurationBase : Scheme.{u} := Spec (.of (ULift.{u} ℤ))

/-- A scheme as a scheme over the absolute base, with its unique structure map.
Source: Stacks, Tag 089J (blueprint: lem-sfb-space-chow-configuration). -/
def chowAbsolute (T : Scheme.{u}) : Over chowConfigurationBase :=
  Over.mk (specULiftZIsTerminal.from T)

/-- A scheme morphism regarded over Spec Z; the underlying map is unchanged.
Source: Stacks, Tag 089J (blueprint: lem-sfb-space-chow-configuration). -/
def chowAbsoluteMap {T Q : Scheme.{u}} (a : T ⟶ Q) : chowAbsolute T ⟶ chowAbsolute Q :=
  Over.homMk a (specULiftZIsTerminal.hom_ext _ _)

/-- The compactified distinct-tuple configuration and its glued morphism.
Source: Stacks Project, spaces-cohomology.tex, Tag 089J, lemma-weak-chow
(blueprint: lem-sfb-space-chow-configuration).

Proof:
1. Induct on the number of factors, starting with W. Representable étale scheme tests
and the separated affine-chart overlap lemma give an affine next factor and its closed
immersion into the product over B. Base change and products of closed immersions give
F closed in W^d_B. The d=1 case is the identity.
2. The diagonal section W -> W x_X W is clopen: the projection is étale and separated,
so apply the étale-section clopen-immersion lemma. Pull these loci back along pairs of
projections. Their finite union is clopen, hence its complement V is clopen and compact.
3. The product W^d_B -> Y^d_B is open. The preceding closed immersion makes V -> Y^d_B
an immersion. Products of the given projective embedding and the binary Segre embeddings
embed Y^d_B into projective space with (m+1)^d homogeneous coordinates.
4. This product is proper and separated over the affine base. Quasi-compactness of V
and the qcqs morphism permanence lemma make its immersion quasi-compact. The immersion
open-in-image lemma identifies V with a quasi-compact schematically and topologically
dense open of its literal scheme-theoretic image Z. Compose closed immersions to embed Z.
5. Each projection Y^d_B -> Y is proper, by proper base change and composition (the
identity for d=1). Thus each g_i is proper. Its inverse image H_i of the compact open W
is compact by the preimage-of-compact-open lemma. The finite union H is compact and
contains V.
6. Pull back the closed diagonal of Z/B to show H/B separated, and likewise show H
absolutely separated. The qcqs permanence lemma gives quasi-compactness of H -> Z.
Write H=Z intersect O for an open O of projective space. The open fibre-product lemma
gives a closed immersion H -> O and hence a quasi-compact projective-space immersion.
7. Restrict the injective structure-sheaf map defining schematic density to any open
containing V; it remains injective on each open's sections. Topological density also
restricts. Apply this to H and the overlaps H_i intersect H_j.
8. On each overlap the two maps to X agree on V. Their equalizer is a closed immersion,
by the separated diagonal of X/B. Its ideal restricts to zero on V, hence is zero by
schematic density. Thus the maps agree. The fppf sheaf X glues them uniquely to p.
9. The quasi-compact open immersion H -> Z and proper Z/B make H/B finite type.
Space local-finite-type cancellation gives local finite type of p. X is quasi-separated
because its absolute diagonal factors through its closed relative diagonal over B and
the closed diagonal of B. Space qcqs permanence makes p quasi-compact. Its diagonal is
the pullback of the closed diagonal of H/B, so p is separated.
10. An étale fibre over K is a disjoint union of spectra of finite separable extensions.
A K-section selects a degree-one component. The d distinct coordinates select d distinct
such components. Over an algebraic closure the bound excludes any additional component.
The labelled coordinate maps therefore exhibit the fibre as the coproduct of d copies
of Spec K. Pull back this very coproduct along each field extension, retaining the labels.
11. Every geometric point of V supplies d distinct points in its fibre, so the bound
places its image in U. Open-subspace factorization gives the factor to U. Conversely a
geometric fibre over U is finite étale of degree d, hence is d copies of the algebraically
closed field. Enumerating them gives a point of V. Thus V surjects onto U, also when U
is empty. The finite étale rank condition is expressed equivalently by finite étale
scheme tests together with the stated geometric fibre cardinality d on U. -/
theorem exists_space_chow_configuration
    (A : CommRingCat.{u}) (X : AlgebraicSpace chowConfigurationBase)
    (s : X ⟶ schemeSpace (chowAbsolute (Spec A)))
    (hs : MapIsSeparated s) (hft : MapIsFiniteType s)
    (W : Over (Spec A)) (hWa : IsAffine W.left)
    (hWft : LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom)
    (f : schemeSpace (chowAbsolute W.left) ⟶ X)
    (hf : IsEtale f.hom.hom) (hfs : IsSurjective f.hom.hom)
    (hfsB : f.hom.hom ≫ s.hom.hom = yoneda.map (chowAbsoluteMap W.hom))
    (d : ℕ) (hd : 1 ≤ d)
    (hbound : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : X.obj.obj.obj (op (chowAbsolute (Spec (.of Ω))))),
      Finite {w : Spec (.of Ω) ⟶ W.left //
        f.hom.hom.app _ (chowAbsoluteMap w) = x} ∧
      Nat.card {w : Spec (.of Ω) ⟶ W.left //
        f.hom.hom.app _ (chowAbsoluteMap w) = x} ≤ d)
    (U : OpenSubspace X)
    (hU : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : X.obj.obj.obj (op (chowAbsolute (Spec (.of Ω))))),
      x ∈ U.val.obj _ ↔ Nat.card {w : Spec (.of Ω) ⟶ W.left //
        f.hom.hom.app _ (chowAbsoluteMap w) = x} = d)
    (hUfinite : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left ∧ Etale p.left)
      (pullback.snd f.hom.hom U.val.ι))
    (Y : Over (Spec A)) (j : W ⟶ Y) (hj : IsOpenImmersion j.left)
    (m : ℕ) (eY : Y.left ⟶ ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec A))
    (heY : IsClosedImmersion eY) (heYB : eY ≫ (ProjectiveSpace.over _ _).hom = Y.hom) :
    ∃ (F : Over (Spec A)) (π : Fin d → (F ⟶ W))
      (q : schemeSpace (chowAbsolute F.left) ⟶ X),
      (∀ i : Fin d, yoneda.map (chowAbsoluteMap (π i).left) ≫ f.hom.hom = q.hom.hom) ∧
      (∀ (T : Scheme.{u}) (x : yoneda.obj (chowAbsolute T) ⟶ X.obj.obj)
        (a : Fin d → (T ⟶ W.left)),
        (∀ i : Fin d, yoneda.map (chowAbsoluteMap (a i)) ≫ f.hom.hom = x) →
        ∃! l : T ⟶ F.left, (∀ i : Fin d, l ≫ (π i).left = a i) ∧
          yoneda.map (chowAbsoluteMap l) ≫ q.hom.hom = x) ∧
      IsAffine F.left ∧
      ∃ V : F.left.Opens,
        (V : Set F.left) =
          (⋃ (i : Fin d) (k : Fin d) (_ : i ≠ k),
            Set.range (equalizer.ι (π i).left (π k).left))ᶜ ∧
        IsClosed (V : Set F.left) ∧ CompactSpace V.toScheme ∧
        ∃ (T : Over (Spec A)) (ρ : Fin d → (T ⟶ Y))
          (a : Over.mk (V.ι ≫ F.hom) ⟶ T),
          Nonempty (IsLimit (Fan.mk T ρ)) ∧
          (∀ i : Fin d, a.left ≫ (ρ i).left = V.ι ≫ (π i).left ≫ j.left) ∧
          IsOpenImmersion a.left.toImage ∧ QuasiCompact a.left.toImage ∧
          IsSchemeTheoreticallyDominant a.left.toImage ∧ DenseRange a.left.toImage ∧
          (∀ i : Fin d, IsProper (a.left.imageι ≫ (ρ i).left)) ∧
          (∃ (N : ℕ)
            (eZ : a.left.image ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec A)),
            IsClosedImmersion eZ ∧
            eZ ≫ (ProjectiveSpace.over _ _).hom = a.left.imageι ≫ T.hom) ∧
          ∃ H : a.left.image.Opens,
            (H : Set a.left.image) =
              ⋃ i : Fin d, (a.left.imageι ≫ (ρ i).left) ⁻¹' Set.range j.left ∧
            CompactSpace H.toScheme ∧ H.toScheme.IsSeparated ∧
            (∃ (N : ℕ)
              (eH : H.toScheme ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec A)),
              IsImmersion eH ∧ QuasiCompact eH ∧
              eH ≫ (ProjectiveSpace.over _ _).hom = H.ι ≫ a.left.imageι ≫ T.hom) ∧
            ∃ (p : schemeSpace (chowAbsolute H.toScheme) ⟶ X)
              (k : ∀ i : Fin d,
                Limits.pullback (a.left.imageι ≫ (ρ i).left) j.left ⟶ H.toScheme)
              (r : V.toScheme ⟶ H.toScheme),
              p.hom.hom ≫ s.hom.hom =
                yoneda.map (chowAbsoluteMap (H.ι ≫ a.left.imageι ≫ T.hom)) ∧
              (∀ i : Fin d,
                k i ≫ H.ι = pullback.fst (a.left.imageι ≫ (ρ i).left) j.left ∧
                yoneda.map (chowAbsoluteMap (k i)) ≫ p.hom.hom =
                  yoneda.map (chowAbsoluteMap
                    (pullback.snd (a.left.imageι ≫ (ρ i).left) j.left)) ≫ f.hom.hom) ∧
              MapIsSeparated p ∧ MapIsFiniteType p ∧
              r ≫ H.ι = a.left.toImage ∧
              IsOpenImmersion r ∧ QuasiCompact r ∧
              IsSchemeTheoreticallyDominant r ∧ DenseRange r ∧
              ∃ vU : yoneda.obj (chowAbsolute V.toScheme) ⟶ U.val.toFunctor,
                vU ≫ U.val.ι = yoneda.map (chowAbsoluteMap r) ≫ p.hom.hom ∧
                pointImage vU = Set.univ ∧
                ∀ (K : Type u) [Field K] (v : Spec (.of K) ⟶ V.toScheme)
                  (L : Type u) [Field L] (b : K →+* L),
                  ∃ (P : Over (Spec (.of L))) (w : P.left ⟶ W.left)
                    (c : Fin d → (Over.mk (𝟙 (Spec (.of L))) ⟶ P)),
                    IsPullback (yoneda.map (chowAbsoluteMap w))
                      (yoneda.map (chowAbsoluteMap P.hom)) f.hom.hom
                      (yoneda.map (chowAbsoluteMap (Spec.map (CommRingCat.ofHom b) ≫ v ≫ r)) ≫
                        p.hom.hom) ∧
                    (∀ i : Fin d, (c i).left ≫ w =
                      Spec.map (CommRingCat.ofHom b) ≫ v ≫ V.ι ≫ (π i).left) ∧
                    Nonempty (IsColimit (Cofan.mk P c)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
