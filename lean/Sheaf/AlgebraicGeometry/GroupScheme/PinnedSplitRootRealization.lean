module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.Algebra.DirectSum.Module

/-! # Pinned split realizations of root data

Source: Conrad, Reductive group schemes, Definitions 1.3.3, 5.1.1 and 6.1.1,
printed pp.27, 136 and 186 (blueprint: def-sfb-pinned-split-root-realization).

Root data use Mathlib's root pairings, without the root-spanning condition.
All geometric roots and coroots are constant monomials under the specified splitting.
Weights over a ring are tested on every algebra, including nonreduced algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped MonObj DirectSum

namespace AlgebraicGeometry.PinnedSplit

/-- A finite reduced root datum with the actual integral dual as coweight lattice.
The evaluation pairing, finite free lattice, and finite root index are explicit.
No spanning condition is imposed, and the root index may be empty.
Source: Conrad, Definition 1.3.3 (blueprint: def-sfb-pinned-split-root-realization). -/
structure ReducedDatum (M : Type u) [AddCommGroup M] where
  free : Module.Free ℤ M
  finite : Module.Finite ℤ M
  Index : Type u
  finiteIndex : Fintype Index
  pairing : RootDatum Index M (Module.Dual ℤ M)
  evaluation : ∀ (m : M) (y : Module.Dual ℤ M), pairing.toLinearMap m y = y m
  reduced : pairing.IsReduced

attribute [instance] ReducedDatum.finiteIndex ReducedDatum.reduced

/-- A specified base of a finite reduced datum, using the existing root-pairing base.
Source: Conrad, Definitions 1.4.1 and 6.1.1
(blueprint: def-sfb-pinned-split-root-realization). -/
structure BasedDatum (M : Type u) [AddCommGroup M] extends ReducedDatum M where
  base : pairing.Base

/-- The positive roots determined by the specified base, using Mathlib's height sign.
Source: Conrad, Definitions 1.4.1 and 6.1.1
(blueprint: def-sfb-pinned-split-root-realization). -/
def positiveRoots {M : Type u} [AddCommGroup M] (D : BasedDatum M) : Set M :=
  D.pairing.root '' {α | D.base.IsPos α}

/-- An isomorphism of based data: a lattice isomorphism preserving roots, their
corresponding coroots contragrediently, and the specified bases.
Source: Conrad, Section 6.1 (blueprint: def-sfb-pinned-split-root-realization). -/
structure BasedDatumIso {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (D : BasedDatum M) (E : BasedDatum N) where
  lattice : M ≃+ N
  roots : D.Index ≃ E.Index
  root_eq : ∀ α : D.Index, lattice (D.pairing.root α) = E.pairing.root (roots α)
  coroot_eq : ∀ (α : D.Index) (m : M),
    E.pairing.coroot (roots α) (lattice m) = D.pairing.coroot α m
  base_eq : ∀ α : D.Index, α ∈ D.base.support ↔ roots α ∈ E.base.support

/-- Scalar extension from a ring to a field is the pullback of group objects.
Source: Conrad, Definition 3.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
abbrev geometricBaseChange (A Ω : Type u) [CommRing A] [Field Ω] [Algebra A Ω] :
    Grp (Over (Spec (.of A))) ⥤ Grp (Over (Spec (.of Ω))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).mapGrp

/-- Reductivity over a ring: smooth affine finite presentation and reductive
geometric fibres. The recorded field predicate includes connectedness and exclusion
of smooth connected normal unipotent subgroups in all characteristics.
Source: Conrad, Definition 3.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
def IsReductive {A : Type u} [CommRing A] (G : Grp (Over (Spec (.of A)))) : Prop :=
  Smooth G.X.hom ∧ IsAffineHom G.X.hom ∧ LocallyOfFinitePresentation G.X.hom ∧
    QuasiCompact G.X.hom ∧ QuasiSeparated G.X.hom ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
      ReductiveTorusCentralizer.IsReductive ((geometricBaseChange A Ω).obj G)

/-- The constant monomial character, whose coordinate map sends t to e_m.
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
abbrev character {A M : Type u} [CommRing A] [AddCommGroup M]
    {T : Grp (Over (Spec (.of A)))} (e : T ≅ ringDiagonalizableGroup A M) (m : M) :
    T ⟶ RingGroupSchemes.multiplicative A :=
  e.hom ≫ (hopfSpec (.of A)).map
    (CommHopfAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom A (zmultiplesHom M m))).op

/-- The constant monomial cocharacter, whose coordinate map sends e_m to t^(y m).
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
abbrev cocharacter {A M : Type u} [CommRing A] [AddCommGroup M]
    {T : Grp (Over (Spec (.of A)))} (e : T ≅ ringDiagonalizableGroup A M)
    (y : Module.Dual ℤ M) : RingGroupSchemes.multiplicative A ⟶ T :=
  (hopfSpec (.of A)).map
    (CommHopfAlgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom A y.toAddMonoidHom)).op ≫ e.inv

/-- Evaluation of the basis monomial e_m at a torus point. The point may come
from a geometric fibre, via its projection to T.
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
def monomialValue {A M R : Type u} [CommRing A] [AddCommGroup M] [CommRing R]
    {T : Grp (Over (Spec (.of A)))} (e : T ≅ ringDiagonalizableGroup A M)
    (m : M) (p : Spec (.of R) ⟶ T.X.left) : R :=
  (Scheme.ΓSpecIso (.of R)).hom
    ((p ≫ e.hom.hom.hom.left).appTop
      ((Scheme.ΓSpecIso (.of (AddMonoidAlgebra A M))).inv (AddMonoidAlgebra.single m (1 : A))))

/-- The actual differential on the existing Lie modules: postcompose infinitesimal
points and use the canonical infinitesimal-point/Lie equivalence.
Source: Conrad, Definition 6.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
def differential {A : Type u} [CommRing A] {G H : Grp (Over (Spec (.of A)))}
    (f : G ⟶ H) (v : GrpObj.Lie G.X) : GrpObj.Lie H.X :=
  GrpObj.lieEquiv H.X (GrpObj.infPointsMap f.hom.hom ((GrpObj.lieEquiv G.X).symm v))

/-- A tangent vector has weight m when conjugation equals scaling by e_m on every
algebra's dual-number points. Scaling means ε ↦ e_m(t) ε, so no differential of a
character is used. Source: Conrad, Definition 5.1.1
(blueprint: def-sfb-pinned-split-root-realization). -/
def HasWeight {A M : Type u} [CommRing A] [AddCommGroup M]
    {G T : Grp (Over (Spec (.of A)))} (i : T ⟶ G)
    (e : T ≅ ringDiagonalizableGroup A M) (m : M) (v : GrpObj.Lie G.X) : Prop :=
  ∀ (R : CommAlgCat.{u} A) (t : points T.X R),
    points.map G.X (TrivSqZeroExt.inlAlgHom A R R) (t ≫ i.hom.hom) *
        points.map G.X (DualNumber.mapAlgebraMap R) (GrpObj.tangentPoint v) *
          (points.map G.X (TrivSqZeroExt.inlAlgHom A R R) (t ≫ i.hom.hom))⁻¹ =
      points.map G.X
        ((DualNumber.scale (monomialValue e m t.left)).restrictScalars A)
        (points.map G.X (DualNumber.mapAlgebraMap R) (GrpObj.tangentPoint v))

/-- The character weight submodule. The defining equations are linear: the tangent
kernel's multiplication is addition, and conjugation and ε-scaling preserve its module
operations. Thus the span has exactly the vectors satisfying HasWeight.
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
def weightSpace {A M : Type u} [CommRing A] [AddCommGroup M]
    {G T : Grp (Over (Spec (.of A)))} (i : T ⟶ G)
    (e : T ≅ ringDiagonalizableGroup A M) (m : M) : Submodule A (GrpObj.Lie G.X) :=
  Submodule.span A {v | HasWeight i e m v}

/-- A geometric character is the specified constant monomial, tested on all algebra
points of the fibre and projected to T. Source: Conrad, Definition 5.1.1
(blueprint: def-sfb-pinned-split-root-realization). -/
def IsConstantCharacter {A M Ω : Type u} [CommRing A] [AddCommGroup M]
    [Field Ω] [Algebra A Ω] {T : Grp (Over (Spec (.of A)))}
    (e : T ≅ ringDiagonalizableGroup A M) (m : M)
    (χ : RankOneRoots.Character ((geometricBaseChange A Ω).obj T)) : Prop :=
  ∀ (R : CommAlgCat.{u} Ω)
    (t : StandardGroupSchemes.affine Ω R ⟶ ((geometricBaseChange A Ω).obj T).X),
    RankOneRoots.multiplicativeValue R (t ≫ χ.hom.hom) =
      monomialValue e m (t.left ≫
        pullback.fst T.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A Ω))))

/-- A geometric cocharacter is the specified constant monomial: e_m maps to
 t^(y m). Powers are taken on multiplicative-group points, retaining negative exponents.
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
def IsConstantCocharacter {A M Ω : Type u} [CommRing A] [AddCommGroup M]
    [Field Ω] [Algebra A Ω] {T : Grp (Over (Spec (.of A)))}
    (e : T ≅ ringDiagonalizableGroup A M) (y : Module.Dual ℤ M)
    (ν : RankOneRoots.Cocharacter ((geometricBaseChange A Ω).obj T)) : Prop :=
  ∀ (R : CommAlgCat.{u} Ω)
    (z : StandardGroupSchemes.affine Ω R ⟶ StandardGroupSchemes.multiplicative Ω) (m : M),
    monomialValue e m ((z ≫ ν.hom.hom).left ≫
        pullback.fst T.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))) =
      RankOneRoots.multiplicativeValue R (z ^ (y m))

/-- The geometric roots are exactly the prescribed monomials, and each prescribed
coroot gives the actual Weyl reflection. Normalizer elements are actual geometric
points normalizing T on every algebra; the reflection is tested on every character.
The rank-one reflection theorem identifies its unique cocharacter with the SL2 coroot.
Source: Conrad, Definitions 1.3.3 and 5.1.1; Milne, Theorem 21.11
(blueprint: def-sfb-pinned-split-root-realization). -/
def HasGeometricRootDatum {A M Ω : Type u} [CommRing A] [AddCommGroup M]
    [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] (D : ReducedDatum M)
    {G T : Grp (Over (Spec (.of A)))} (i : T ⟶ G)
    (e : T ≅ ringDiagonalizableGroup A M) : Prop :=
  ∃ a : ModObj ((geometricBaseChange A Ω).obj T).X
      ((geometricBaseChange A Ω).obj G).X,
    a.smul = RankOneRoots.adjointMap ((geometricBaseChange A Ω).map i) ∧
    (∀ α : D.Index,
      ∃ χ : RankOneRoots.Character ((geometricBaseChange A Ω).obj T),
        IsConstantCharacter e (D.pairing.root α) χ) ∧
    (∀ χ : RankOneRoots.Character ((geometricBaseChange A Ω).obj T),
      χ ∈ RankOneRoots.roots _ _ a ↔
        ∃ α : D.Index, IsConstantCharacter e (D.pairing.root α) χ) ∧
    ∀ (α : D.Index) (χ : RankOneRoots.Character ((geometricBaseChange A Ω).obj T)),
      IsConstantCharacter e (D.pairing.root α) χ →
      ∃ ν : RankOneRoots.Cocharacter ((geometricBaseChange A Ω).obj T),
        IsConstantCocharacter e (D.pairing.coroot α) ν ∧
        ∃ n : RankOneRoots.normalizer ((geometricBaseChange A Ω).map i),
          ∀ x : RankOneRoots.Character ((geometricBaseChange A Ω).obj T),
            ∃ k : ℤ,
              ν.hom.hom ≫ x.hom.hom = (𝟙 (StandardGroupSchemes.multiplicative Ω)) ^ k ∧
              ∀ (R : CommAlgCat.{u} Ω)
                (t : StandardGroupSchemes.affine Ω R ⟶ ((geometricBaseChange A Ω).obj T).X),
                ∃ s : StandardGroupSchemes.affine Ω R ⟶ ((geometricBaseChange A Ω).obj T).X,
                  s ≫ ((geometricBaseChange A Ω).map i).hom.hom =
                    (CategoryTheory.CartesianMonoidalCategory.toUnit _ ≫ n.val) *
                      (t ≫ ((geometricBaseChange A Ω).map i).hom.hom) *
                        (CategoryTheory.CartesianMonoidalCategory.toUnit _ ≫ n.val)⁻¹ ∧
                  s ≫ x.hom.hom = (t ≫ x.hom.hom) / (t ≫ χ.hom.hom) ^ k

open Classical in
/-- A split realization with constant roots and coroots and free rank-one root modules.
The canonical sum map, not an arbitrary module equivalence, gives the Lie decomposition.
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
structure SplitRealization (A M : Type u) [CommRing A] [Nontrivial A] [AddCommGroup M]
    (D : ReducedDatum M) where
  G : Grp (Over (Spec (.of A)))
  T : Grp (Over (Spec (.of A)))
  inclusion : T ⟶ G
  closed : IsClosedImmersion inclusion.hom.hom.left
  splitting : T ≅ ringDiagonalizableGroup A M
  reductive : IsReductive G
  maximal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    ReductiveTorusCentralizer.IsMaximalTorus ((geometricBaseChange A Ω).map inclusion)
  geometricRoots : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    HasGeometricRootDatum (Ω := Ω) D inclusion splitting
  rootLines : ∀ α : D.Index,
    Nonempty (A ≃ₗ[A] weightSpace inclusion splitting (D.pairing.root α))
  decomposition : Function.Bijective
    (fun v : GrpObj.Lie T.X ×
      (⨁ α : D.Index, weightSpace inclusion splitting (D.pairing.root α)) ↦
      differential inclusion v.1 +
        DirectSum.toModule A D.Index (GrpObj.Lie G.X)
          (fun α ↦ (weightSpace inclusion splitting (D.pairing.root α)).subtype) v.2)

/-- A pinning specifies a generator in each simple-root module. Forgetting these
vectors and the base leaves the split realization above. No existence is asserted.
Source: Conrad, Definition 6.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
structure PinnedRealization (A M : Type u) [CommRing A] [Nontrivial A] [AddCommGroup M]
    (D : BasedDatum M) extends SplitRealization A M D.toReducedDatum where
  pinning : ∀ α : D.base.support, weightSpace inclusion splitting (D.pairing.root α.val)
  generates : ∀ α : D.base.support, Submodule.span A {pinning α} = ⊤

/-- An isomorphism inducing the specified based-datum isomorphism. Its torus map is
D_A(u⁻¹), and its actual differential carries every specified generator to the
corresponding generator. Source: Conrad, Definition 6.1.1 and p.187
(blueprint: def-sfb-pinned-split-root-realization). -/
structure PinnedIso {A M N : Type u} [CommRing A] [Nontrivial A]
    [AddCommGroup M] [AddCommGroup N] {D : BasedDatum M} {E : BasedDatum N}
    (u : BasedDatumIso D E) (P : PinnedRealization A M D) (Q : PinnedRealization A N E) where
  groupIso : P.G ≅ Q.G
  torusIso : P.T ≅ Q.T
  inclusion_eq : P.inclusion ≫ groupIso.hom = torusIso.hom ≫ Q.inclusion
  torus_eq : P.splitting.hom ≫ ringDiagonalizableGroupMap A u.lattice.symm.toAddMonoidHom =
    torusIso.hom ≫ Q.splitting.hom
  pinning_eq : ∀ α : D.base.support,
    differential groupIso.hom (P.pinning α).val =
      (Q.pinning ⟨u.roots α.val, (u.base_eq α.val).mp α.prop⟩).val

/-- A split reductive group admits split-realization data, with no chosen base or
pinning. This predicate asserts admission of the data, not an existence theorem.
Source: Conrad, Definition 5.1.1 (blueprint: def-sfb-pinned-split-root-realization). -/
def IsSplitReductive {A : Type u} [CommRing A] [Nontrivial A]
    (G : Grp (Over (Spec (.of A)))) : Prop :=
  ∃ (M : Type u) (hM : AddCommGroup M),
    ∃ (D : @ReducedDatum M hM) (P : SplitRealization A M D), Nonempty (P.G ≅ G)

end AlgebraicGeometry.PinnedSplit
