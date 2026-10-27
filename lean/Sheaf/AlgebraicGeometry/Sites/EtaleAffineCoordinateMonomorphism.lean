module

public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Yoneda

/-! # Finite coordinates for affine étale objects

Source: Stacks Project, morphisms.tex, Tag 04II; etale-cohomology.tex, Tag 04IJ,
first two proof paragraphs (blueprint: lem-sfb-etale-affine-coordinate-monomorphism).

The underlying set sheaf of `etaleAdditiveSheaf` is the structure sheaf with its sections
lifted to `Type (u + 1)`. Yoneda turns a section into its pullback-of-functions map.
The base-change functor uses `V ×_S X`, canonically the stated `X ×_S V` with
its factors interchanged. The projection to `V` is therefore `pullback.fst`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finite global coordinates of an affine étale object give monomorphisms after
all base changes, compatible with inverse image and the structure-sheaf map.
Source: Stacks Project, Tags 04II and 04IJ
(blueprint: lem-sfb-etale-affine-coordinate-monomorphism).

Here `β` is specified on every section as pullback along the projection. Its
adjunct is precisely `a^♯`. The isomorphism `ι` is normalized by specifying its
adjunct on every relative morphism. The arrows constructed with
`uliftYonedaEquiv.symm` send a relative morphism to the pullback of the indicated
section. `Pi.lift` assembles these coordinates, and `piComparison` is the
finite-product comparison via projections, including the empty product.

Proof:
1. An affine scheme is quasi-affine (lemma-nagata-affine-finite-type-is-quasi-affine).
Étaleness implies unramifiedness and local finite type (def-weil-etale-morphism,
def-weil-unramified-morphism, def-weil-finite-type-morphism).
2. Apply lemma-nagata-quasi-affine-immersion-affine-space-exists to obtain an
immersion into finite relative affine space. Pull back its coordinate functions.
By def-sbc-affine-space, def-pc-fibre-product and
lem-weil-pbc-morphism-into-affine-scheme, these coordinates distinguish maps into
relative affine space. Pullback of functions makes them natural. The representable
is a sheaf by lem-weil-pbc-small-etale-representable-presheaf-sheaf.
3. Factor the immersion into a closed immersion and an open immersion
(def-weil-closed-immersion). Both are monic (lem-pc-proper-monomorphism-closed,
lem-weil-pbc-open-immersion-monomorphism). Equal coordinate tuples after any base
change therefore give equal projections to V; the projections to X already agree.
Fibre-product uniqueness gives equal relative morphisms, hence a monic sheaf map.
4. Use lem-weil-pbc-etale-inverse-image-algebraic-structures, adjunction,
lem-galois-yoneda-hom-bijection and
lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection to obtain the comparison of
lem-galois-inverse-image-representable. The identity section corresponds to the
identity of the base change, so its adjunct is base change of each morphism.
5. Compare adjuncts of each coordinate. Both evaluate at u to pr_T^*(u^*c_j),
by pullback functoriality, naturality of the unit and the definition of a^♯.
Finite-limit preservation identifies the product via its projections. For n=0,
the maps to the terminal sheaf are unique. The equality and the monicity of the
coordinate map and of ι imply the last monicity assertion. No quasi-compactness
or separation of either base is used. -/
theorem exists_etaleAffineCoordinateMonomorphism
    (S : Scheme.{u}) (V : S.Etale) [IsAffine V.left] :
    ∃ (n : ℕ) (c : Fin n → Γ(V.left, ⊤)),
      ∀ (X : Scheme.{u}) (a : X ⟶ S),
        ∃ (β : (sheafForget (D := AddCommGrpCat.{u + 1}) S.smallEtaleTopology).obj
              S.etaleAdditiveSheaf ⟶
            (a.Etale.sheafPushforwardContinuous (Type (u + 1))
              S.smallEtaleTopology X.smallEtaleTopology).obj
              ((sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).obj
                X.etaleAdditiveSheaf))
          (ι : (Scheme.etaleSetPullback a).obj
              (S.smallEtaleTopology.uliftYoneda.{u + 1}.obj V) ≅
            X.smallEtaleTopology.uliftYoneda.{u + 1}.obj (a.Etale.obj V)),
          (∀ (T : S.Etale) (s : Γ(T.left, ⊤)),
            (β.hom.app (op T) ⟨s⟩).down = (pullback.fst T.hom a).appTop s) ∧
          (∀ (T : S.Etale) (z : T ⟶ V),
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              a.Etale (Type (u + 1)) S.smallEtaleTopology X.smallEtaleTopology).homEquiv
                _ _ ι.hom).hom.app (op T) ⟨z⟩).down = a.Etale.map z) ∧
          Mono (Pi.lift (fun j : Fin n ↦
            (X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}
                (X := a.Etale.obj V)
              (F := (sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).obj
                X.etaleAdditiveSheaf)).symm
              ⟨(pullback.fst V.hom a).appTop (c j)⟩)) ∧
          ι.hom ≫ Pi.lift (fun j : Fin n ↦
              (X.smallEtaleTopology.uliftYonedaEquiv.{u + 1}
                (X := a.Etale.obj V)
                (F := (sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).obj
                  X.etaleAdditiveSheaf)).symm
                ⟨(pullback.fst V.hom a).appTop (c j)⟩) =
            (Scheme.etaleSetPullback a).map
                (Pi.lift (fun j : Fin n ↦
                  (S.smallEtaleTopology.uliftYonedaEquiv.{u + 1}
                    (X := V)
                    (F := (sheafForget (D := AddCommGrpCat.{u + 1})
                      S.smallEtaleTopology).obj S.etaleAdditiveSheaf)).symm ⟨c j⟩)) ≫
              piComparison (Scheme.etaleSetPullback a)
                (fun _ : Fin n ↦ (sheafForget (D := AddCommGrpCat.{u + 1})
                  S.smallEtaleTopology).obj S.etaleAdditiveSheaf) ≫
              Limits.Pi.map (fun _ : Fin n ↦
                ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                  a.Etale (Type (u + 1)) S.smallEtaleTopology X.smallEtaleTopology).homEquiv
                    _ _).symm β) ∧
          Mono ((Scheme.etaleSetPullback a).map
              (Pi.lift (fun j : Fin n ↦
                (S.smallEtaleTopology.uliftYonedaEquiv.{u + 1}
                    (X := V)
                  (F := (sheafForget (D := AddCommGrpCat.{u + 1})
                    S.smallEtaleTopology).obj S.etaleAdditiveSheaf)).symm ⟨c j⟩)) ≫
            piComparison (Scheme.etaleSetPullback a)
              (fun _ : Fin n ↦ (sheafForget (D := AddCommGrpCat.{u + 1})
                S.smallEtaleTopology).obj S.etaleAdditiveSheaf) ≫
            Limits.Pi.map (fun _ : Fin n ↦
              ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                a.Etale (Type (u + 1)) S.smallEtaleTopology X.smallEtaleTopology).homEquiv
                  _ _).symm β)) := by
  sorry

end AlgebraicGeometry
