module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf
public import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Integer models preserving a marked residue-fibre torus

Source: Stacks Project, Limits, Tags 01ZM, 01ZP and 0C0C; the marked version of the
first reduction in Conrad, Proposition 3.1.6, printed p.84
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The coordinate-preserving map between split tori over a change of base. Both
models are pullbacks of the same integral Laurent Hopf algebra, and this map is the
identity on that algebra. Source: Stacks, Tag 022U; Conrad, Proposition 3.1.6, p.84
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model). -/
def residueMarkedTorusProjection {S T : Scheme.{u}} (f : T ⟶ S) (r : ℕ) :
    (RelativeSplitTorus.model T r).X.left ⟶ (RelativeSplitTorus.model S r).X.left :=
  pullback.map _ _ _ _ (𝟙 _) f (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (specULiftZIsTerminal.hom_ext _ _)

/-- The canonical residue-fibre functor on group schemes, with the pulled-back group law.
Source: Stacks, Tag 01ZM; Conrad, Proposition 3.1.6, p.84
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model). -/
def residueMarkedGroupFiber (S : Scheme.{u}) (p : S) :
    Grp (Over S) ⥤ Grp (Over (Spec (S.residueField p))) :=
  (Over.pullback (S.fromSpecResidueField p)).mapGrp

/-- The type of parametrized rank-r residue-fibre torus homomorphisms.
Source: Conrad, Proposition 3.1.6, p.84; Stacks, Tag 01ZM
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model). -/
def ResidueMarkedTorusHom (S : Scheme.{u}) (p : S) (G : Grp (Over S)) (r : ℕ) :=
  (RelativeSplitTorus.model (Spec (S.residueField p)) r).toGrp ⟶
    (residueMarkedGroupFiber S p).obj G

/-- Project a marked residue-fibre map to the total group scheme.
Source: Conrad, Proposition 3.1.6, p.84; Stacks, Tag 01ZM
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model). -/
def residueMarkedTorusMapToGroup (S : Scheme.{u}) (p : S) (G : Grp (Over S))
    (r : ℕ) (i : ResidueMarkedTorusHom S p G r) :
    (RelativeSplitTorus.model (Spec (S.residueField p)) r).X.left ⟶ G.X.left :=
  i.hom.hom.left ≫ pullback.fst G.X.hom (S.fromSpecResidueField p)

/-- Project a group scheme to a model through the specified base-change isomorphism.
Source: Conrad, Proposition 3.1.6, p.84; Stacks, Tag 01ZM
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model). -/
def residueMarkedModelProjection {S T : Scheme.{u}} (f : T ⟶ S)
    (G₀ : Grp (Over S)) (G : Grp (Over T))
    (α : (Over.pullback f).mapGrp.obj G₀ ≅ G) : G.X.left ⟶ G₀.X.left :=
  α.inv.hom.hom.left ≫ pullback.fst G₀.X.hom f

/-- Equality of the prescribed markings under the canonical residue-field extension.
Both sides land in G₀ after the canonical projections, so the pullback universal
property identifies this equation with α_k ∘ (i₀)_k = i.
Source: Conrad, Proposition 3.1.6, p.84; Stacks, Tag 01ZM
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model). -/
def ResidueMarkedModelCompatible {S T : Scheme.{u}} (f : T ⟶ S) (p : T)
    (G₀ : Grp (Over S)) (G : Grp (Over T)) (r : ℕ)
    (α : (Over.pullback f).mapGrp.obj G₀ ≅ G)
    (i₀ : ResidueMarkedTorusHom S (f p) G₀ r)
    (i : ResidueMarkedTorusHom T p G r) : Prop :=
  residueMarkedTorusProjection (Spec.map (f.residueFieldMap p)) r ≫
      residueMarkedTorusMapToGroup S (f p) G₀ r i₀ =
    residueMarkedTorusMapToGroup T p G r i ≫ residueMarkedModelProjection f G₀ G α

/-- Existence of the specified smooth affine group model with its marked residue torus.
This packages only the output data and the canonical marking equation.
Source: Conrad, Proposition 3.1.6, p.84; Stacks, Tags 01ZM and 01ZP
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model). -/
def HasResidueMarkedSmoothGroupModel {S T : Scheme.{u}} (f : T ⟶ S) (p : T)
    (G : Grp (Over T)) (r : ℕ) (i : ResidueMarkedTorusHom T p G r) : Prop :=
  ∃ G₀ : Grp (Over S),
    IsAffine G₀.X.left ∧ Smooth G₀.X.hom ∧ LocallyOfFinitePresentation G₀.X.hom ∧
      ∃ α : (Over.pullback f).mapGrp.obj G₀ ≅ G,
        ∃ i₀ : ResidueMarkedTorusHom S (f p) G₀ r,
          IsClosedImmersion i₀.hom.hom.left ∧
            ResidueMarkedModelCompatible f p G₀ G r α i₀ i

/-- A smooth affine finitely presented group scheme, with a specified parametrized
split torus in one residue fibre, descends to a finitely generated integer subring.
The last equation compares the two marked maps after projection to the model G₀;
by the pullback universal property it is precisely α_k ∘ (i₀)_k = i. The residue
extension is the canonical residueFieldMap of Spec(A) → Spec(A₀).

Source: Stacks Project, Limits, Tags 01YW, 01ZM, 01ZP and 0C0C; Conrad,
Proposition 3.1.6, first reduction, printed p.84
(blueprint: lem-sfb-residue-marked-smooth-group-integer-model).

Proof:
1. Write G = Spec B. The smooth affine dictionary and
   lem-weil-pbc-smooth-algebra-finite-type-model give a smooth algebra model over a
   finitely generated integer subring. The tensor pushout and affine fibre-product
   formula identify its base change with G as a scheme.
2. Order the finitely generated subrings containing this subring by inclusion.
   They are directed and have union A. Their affine spectra are qcqs and have
   affine transitions; lem-weil-pbc-limit-affine-transition identifies their limit.
   Tensor presentations give finite presentation of the model and its finite powers.
   Smoothness persists by lem-pc-proper-base-change, clause (2).
3. Apply thm-pd-spreading-out to descend multiplication, inverse and identity,
   and choose a common upper stage for these three maps.
4. Apply its equality clause to associativity, the two unit identities and the two
   inverse identities. At a common upper stage they define a group structure,
   and the fixed comparison is now an isomorphism of group schemes.
5. For each remaining subring C contract p. Its residue field is Frac(C/(C∩p)).
   The inclusions induce canonical field embeddings. Every fraction in κ(p)
   belongs to one such field, by adjoining its numerator and denominator to C.
   Thus κ(p) is their filtered union, and the affine limit theorem applies again.
6. Descend the specified torus map using thm-pd-spreading-out over this field
   system, with its fixed Laurent coordinates; no torus automorphism is introduced.
7. Descend its multiplication, inverse and identity compatibilities by the
   equality clause, using finite presentation of the torus and its square.
8. Apply lem-weil-pbc-descend-closed-immersion. The initial map is locally of finite
   type since the Laurent generators generate its source ring over the target
   ring, and the limit map is the given closed immersion. Group identities persist.
9. Take the resulting subring A₀ and its smooth affine group model. All prescribed
   operations and maps have retained their pullbacks, giving the displayed marked
   equality. The empty list of Laurent generators also covers rank zero. -/
theorem exists_residueMarkedSmoothGroup_integerModel
    (A : Type u) [CommRing A] (p : Spec (.of A))
    (G : Grp (Over (Spec (.of A)))) [IsAffine G.X.left]
    [Smooth G.X.hom] [LocallyOfFinitePresentation G.X.hom] (r : ℕ)
    (i : ResidueMarkedTorusHom (Spec (.of A)) p G r)
    [IsClosedImmersion i.hom.hom.left] :
    ∃ A₀ : Subalgebra ℤ A, A₀.FG ∧
      HasResidueMarkedSmoothGroupModel (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) p G r i := by
  sorry

end AlgebraicGeometry
