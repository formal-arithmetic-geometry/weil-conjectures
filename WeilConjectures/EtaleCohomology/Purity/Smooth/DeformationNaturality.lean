/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DeformationIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantBaseChangeCoherence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantEtale

/-!
# Naturality of the DNC isomorphism under base change and étale maps

Let `g : V ⟶ B` be smooth with a closed section `s`, and let
`α_{g,s} : 𝒞(g, s) ≅ 𝒞(π_N, 0_N)` be the comparison of section invariants given by a deformation
to the normal cone (`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.sectionInvariantIso`,
blueprint `lemma-section-normal-bundle`). Blueprint `lemma-naturality-under-base-change-etale`
states that `α` is natural:

* (1) under base change `h : B' ⟶ B`, through the base change isomorphisms of section
  invariants (`AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`):
  `Scheme.Hom.DeformationToNormalConeData.sectionInvariantIso_baseChange`;
* (2) under étale maps of pairs, through the identifications obtained by composing adjunctions
  (`AlgebraicGeometry.Etale.sectionInvariantEtaleIso`):
  `Scheme.Hom.DeformationToNormalConeData.sectionInvariantEtaleIso_sectionInvariantIso`.

Deformation data are carried as data
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`), so the geometric identifications
of the blueprint (`AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange`,
`AlgebraicGeometry.Scheme.Hom.exists_isPullback_normalCone_baseChange`) enter as maps of data
forming cartesian squares compatible with the sections and the fibres.

Both proofs follow the blueprint: the comparison over `𝔸¹_B` is unique once normalized at
`t = 1` (`DeformationToNormalConeData.eq_familyObjectIso`), the transported comparison is still
normalized at `t = 1`, and restricting to `t = 0` gives the claim.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
  {V B : Scheme.{u}} {d : ℕ} {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s}
  (D : DeformationToNormalConeData d g s N) [HasInvertibleExponent Λ B] [HasCompactification g]
  [HasCompactification N.proj] {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
  [LocallyOfFiniteType aB] [QuasiCompact D.proj]

/-- Blueprint `lemma-naturality-under-base-change-etale` (3): *naturality under base change.*
Let `h : B' ⟶ B` and let `D'` be a deformation datum for the base change `(g', s', N')`, related
to `D` by cartesian squares `hV : V' ⟶ V` over `h` (so `V' = V ×_B B'`), `hN : N' ⟶ N` over `h`
(`N_{s'} ≅ N_s ×_B B'`) and `hD : 𝒟' ⟶ 𝒟` over `𝔸¹_h` (`𝒟_{s'} V' ≅ 𝒟_s V ×_B B'`), compatible
with the sections and with the fibres over `t = 1` and `t = 0`. Then, through the exceptional base
change isomorphisms of section invariants
(`AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`), the square

`Lh^* 𝒞(g, s) ⟶ Lh^* 𝒞(π, 0)`, `𝒞(g', s') ⟶ 𝒞(π', 0')`

formed by `Lh^* α_{g,s}` and `α_{g',s'}` commutes. -/
theorem sectionInvariantIso_baseChange {V' B' : Scheme.{u}} {g' : V' ⟶ B'} {s' : B' ⟶ V'}
    {N' : NormalConeData d s'} (D' : DeformationToNormalConeData d g' s' N')
    [HasInvertibleExponent Λ B'] [HasCompactification g'] [HasCompactification N'.proj]
    {k' : Type u} [Field k'] (aB' : B' ⟶ Spec (.of k')) [IsSeparated aB']
    [LocallyOfFiniteType aB'] [QuasiCompact D'.proj] [QuasiCompact g'] [QuasiCompact N'.proj]
    (h : B' ⟶ B)
    (hV : V' ⟶ V) (sqV : IsPullback hV g' g h) (hs : s' ≫ hV = h ≫ s)
    (hN : N'.scheme ⟶ N.scheme) (sqN : IsPullback hN N'.proj N.proj h)
    (hz : N'.zeroSection ≫ hN = h ≫ N.zeroSection)
    (hD : D'.scheme ⟶ D.scheme) (sqD : IsPullback hD D'.proj D.proj (AffineSpace.map _ h))
    (hsect : D'.sect ≫ hD = AffineSpace.map _ h ≫ D.sect)
    (h₁ : D'.oneFibre ≫ hD = hV ≫ D.oneFibre) (h₀ : D'.zeroFibre ≫ hD = hN ≫ D.zeroFibre)
    [IsIso (dualizingComplexBaseChangeMap Λ sqV)] [IsIso (dualizingComplexBaseChangeMap Λ sqN)] :
    (L((h)^*[ModuleCat.{u + 1} Λ])).map (D.sectionInvariantIso Λ aB).hom ≫
        (sectionInvariantBaseChangeIso Λ sqN N.zeroSection N'.zeroSection hz).hom =
      (sectionInvariantBaseChangeIso Λ sqV s s' hs).hom ≫ (D'.sectionInvariantIso Λ aB').hom := by
  sorry

/-- Blueprint `lemma-naturality-under-base-change-etale` (7): *naturality under étale maps of
pairs.* Let `e : V' ⟶ V` be an étale `B`-morphism with `g' = e ≫ g` and `s' ≫ e = s`, and let
`D'` be a deformation datum for `(g', s', N')` related to `D` by an étale map `E : 𝒟' ⟶ 𝒟` over
`𝔸¹_B` and an étale map `ψ : N' ⟶ N` of normal cones (an isomorphism, blueprint (4)), compatible
with the sections and the fibres over `t = 1` and `t = 0`. Then the identifications
`𝒞(g', s') ≅ 𝒞(g, s)` and `𝒞(π', 0') ≅ 𝒞(π, 0)` obtained by composing adjunctions
(`AlgebraicGeometry.Etale.sectionInvariantEtaleIso`) carry `α_{g',s'}` to `α_{g,s}`. -/
theorem sectionInvariantEtaleIso_sectionInvariantIso [QuasiCompact g] [QuasiCompact N.proj]
    {V' : Scheme.{u}} {g' : V' ⟶ B} {s' : B ⟶ V'} {N' : NormalConeData d s'}
    (D' : DeformationToNormalConeData d g' s' N') [HasCompactification g']
    [HasCompactification N'.proj] [QuasiCompact D'.proj] [QuasiCompact g'] [QuasiCompact N'.proj]
    (e : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e]
    (hg : e ≫ g = g') (hs : s' ≫ e = s)
    (ψ : N'.scheme ⟶ N.scheme) [_root_.AlgebraicGeometry.Etale ψ] [HasCompactification ψ]
    (hπ : ψ ≫ N.proj = N'.proj) (hz : N'.zeroSection ≫ ψ = N.zeroSection)
    (E : D'.scheme ⟶ D.scheme) [_root_.AlgebraicGeometry.Etale E] [HasCompactification E]
    (hE : E ≫ D.proj = D'.proj) (hsect : D'.sect ≫ E = D.sect)
    (h₁ : D'.oneFibre ≫ E = e ≫ D.oneFibre) (h₀ : D'.zeroFibre ≫ E = ψ ≫ D.zeroFibre) :
    (sectionInvariantEtaleIso Λ e g g' hg s s' hs).hom ≫ (D.sectionInvariantIso Λ aB).hom =
      (D'.sectionInvariantIso Λ aB).hom ≫
        (sectionInvariantEtaleIso Λ ψ N.proj N'.proj hπ N.zeroSection N'.zeroSection hz).hom := by
  sorry

end Scheme.Hom.DeformationToNormalConeData

end AlgebraicGeometry
