module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine

/-! # Affine neighbourhoods on almost homogeneous schemes over a semi-trait

Source: Anantharaman, Schémas en groupes, espaces homogènes et espaces algébriques
sur une base de dimension 1, Definition 4.0.1 and Proposition 4.2.2, pp.53 and 57–59
(blueprint: lem-sfb-semitrait-almost-homogeneous-affine-neighbourhoods).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A separated flat finitely presented almost homogeneous scheme over a semi-trait has
an affine open neighbourhood of each finite set of points.
Source: Anantharaman, Definition 4.0.1 and Proposition 4.2.2, pp.53 and 57–59
(blueprint: lem-sfb-semitrait-almost-homogeneous-affine-neighbourhoods).

Proof:
1. Apply lem-sfb-almost-homogeneous-potential-smooth-cover to obtain a semi-trait T,
   a smooth group H with geometrically connected fibres, a smooth H-scheme Y and
   an integral surjection q : Y → X with finite underlying fibres. Finite presentation
   implies finite type, so lem-weil-pbc-finite-type-over-noetherian makes X Noetherian.
2. Apply lem-sfb-dedekind-smooth-fibre-dense-affine to Y → T to obtain an affine open U
   dense in every geometric fibre. Its additional Cartier divisor is not needed.
3. By lem-sfb-connected-action-affine-saturation-ample, the open saturation H.U admits
   an ample invertible module. Each geometric orbit is open, so fibrewise density makes
   U meet every orbit. After a common algebraically closed extension, the orbit condition
   carries such a point to any given geometric point. Thus H.U = Y, including empty fibres.
4. For a finite E in X, q⁻¹(E) is finite, since q has finite underlying fibres.
   Apply lem-sc-ample-finite-set-affine to obtain one affine open containing all of q⁻¹(E).
5. Apply lem-sfb-integral-finite-fibre-affine-neighbourhood-transfer to q and E.
   The target is locally Noetherian by step 1; no flatness or finiteness of q is used.
   It yields the required affine neighbourhood of E, including E empty.
-/
theorem exists_affineOpen_of_semitrait_almostHomogeneous
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 1) (hmax : Set.Finite {m : Ideal R | m.IsMaximal})
    (G X : Over (Spec (CommRingCat.of R))) [GrpObj G] [ModObj G X]
    [IsSeparated G.hom] [Flat G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (n : ℕ) (U : Fin n → X.left.Opens) (hcover : ⨆ j, U j = ⊤)
    (hinvariant : ∀ j : Fin n,
      (snd G X).left ⁻¹ᵁ U j ≤ (ModObj.smul (M := G) (X := X)).left ⁻¹ᵁ U j)
    (hhomogeneous : ∀ (j : Fin n) (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ X),
      Set.range x.left ⊆ (U j : Set X.left) →
      Set.range y.left ⊆ (U j : Set X.left) →
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left,
        ∀ i : 𝒰.I₀, ∃ g : Over.mk (𝒰.f i ≫ T.hom) ⟶ G,
          g • ((Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ x) =
            (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ y)
    (E : Set X.left) (hE : E.Finite) :
    ∃ V : X.left.Opens, IsAffineOpen V ∧ E ⊆ (V : Set X.left) := by
  sorry

end AlgebraicGeometry
