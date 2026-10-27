module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Flat horizontal closure of a group algebraic space over a trait

Source: Anantharaman, Schemas en groupes, espaces homogenes et espaces algebriques
sur une base de dimension 1, 1.2.0, 1.2.5(b), 1.3.1(c), printed pp.15, 18-20;
Stacks Project, Tags 03MB, 07ZP, 03LZ, 03LY, 0AUW and 01U5
(blueprint: lem-sfb-space-trait-flat-group-closure).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine chart characterization of the horizontal closed subspace. The upper
left corner is the actual quotient by the kernel of localization at the image of pi;
the lower horizontal arrow is the given etale chart. All arrows retain their maps to
Spec R, and the square is a pullback of presheaves.
Source: Anantharaman 1.2.0 and 1.3.1(c); Stacks Tag 03MB
(blueprint: lem-sfb-space-trait-flat-group-closure). -/
def HasTraitClosureCharts (R : Type u) [CommRing R] (π : R)
    (G : AlgebraicSpace (Spec (.of R))) (C : ClosedSubspace G) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra R B]
    (a : yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ⟶ G.obj.obj),
    IsEtale a →
    ∃ c : yoneda.obj (Over.mk
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (RingHom.ker (algebraMap B (Localization.Away (algebraMap R B π)))))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R B)))) ⟶
        (C.val : AlgebraicSpace (Spec (.of R))).obj.obj,
      IsPullback c
        (yoneda.map (Over.homMk
          (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (RingHom.ker (algebraMap B (Localization.Away (algebraMap R B π))))))) rfl))
        C.val.arrow.hom.hom a

/-- The horizontal closure is the unique closed subspace with its affine localization
kernel charts. It has the same generic fibre, its group operations are restrictions,
and it is separated, flat, locally of finite type and locally of finite presentation.
Every map from an arbitrary flat scheme over the trait has a unique factorization.
No commutativity, quasi-compactness, reducedness or smoothness is imposed.

Source: Anantharaman 1.2.0, 1.2.5(b), 1.3.1(c), printed pp.15, 18-20
(blueprint: lem-sfb-space-trait-flat-group-closure).

Proof:
1. On every etale chart U, take sections of O_U supported on V(pi). Its complementary
principal open is retrocompact. Lem-trf-supported-sections-quasi-coherent makes this
a quasi-coherent ideal; the localization zero criterion identifies its affine sections
with the kernel of B -> B[1/pi].
2. Maps between etale charts are etale by lem-trf-space-chartwise-etale-permanence,
hence flat. Lem-trf-supported-kernel-flat-pullback identifies the pulled-back ideals,
compatibly with inclusions. Their monicity gives the cocycle identities. Transport by
lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and descend by
lem-sfb-space-qcoh-cartesian-chart-family; inclusions and the ideal property are local.
3. Lem-sfb-space-ideal-closed-subspace-correspondence constructs C with exactly these
quotient charts. Equal chart ideals give equality as closed subspaces. Localizing the
kernel gives zero, so localization of B/J is B[1/pi]; this proves the generic isomorphism.
4. B/J injects into B[1/pi], a K-algebra, and is R-torsion-free. Its localizations remain
torsion-free. The local rings of Spec R are R and K; apply
lem-weil-pbc-pid-torsion-free-module-flat to obtain flatness on each chart.
Lemma lem-trf-space-fibre-products-etale-covers supplies the covering pulled-back charts.
5. Quotients of finite-type R-algebras are finite type without finite generation of J.
A DVR is Noetherian, hence Spec R locally Noetherian. Apply pqf-lem-lft-fp-locnoeth to
the quotient charts to obtain local finite presentation, with no quasi-compactness claim.
6. Pull charts back to a flat scheme T. Their etale scheme covers are flat over R by
composition of flat tensor functors. By lem-weil-pbc-flat-morphism-affine-criterion
and lem-trf-flat-module-torsionfree-domain, their affine rings are R-torsion-free.
The pi-power torsion ideal therefore maps to zero. The factorization criterion of
lem-sfb-space-ideal-closed-subspace-correspondence gives unique local lifts; monicity
makes them agree on overlaps, and the sheaf condition glues them without a finiteness
assumption on T.
7. The same assertion holds for a space with flat etale scheme charts: factor on its
charts, and glue the unique lifts as sections of the subfunctor C.
8. Products of flat charts of C cover C times C by the etale covering permanence nodes.
Lemma lem-weil-pbc-fibre-product-affine-spectra identifies their rings with tensor
products of flat R-algebras, which are flat. Step 7 restricts multiplication and inverse;
step 6 restricts the identity from Spec R. Cancel the monic inclusion in each group
identity. Thus C is a group and its inclusion preserves operations, without commutativity.
9. The diagonal of C is the pullback of the diagonal of G: two C-valued points agree
in G precisely when they agree in C. Closedness of the representable diagonal is
therefore inherited, proving separatedness and all the stated assertions. -/
theorem exists_trait_flat_group_closure
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (G : AlgebraicSpace (Spec (.of R))) [GrpObj G.obj.obj]
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 G.obj.obj) (𝟙 G.obj.obj)))
    (hlft : ∀ U : G.EtaleSite, LocallyOfFiniteType U.obj.left.hom) :
    ∃ C : ClosedSubspace G,
      HasTraitClosureCharts R π G C ∧
      (∀ D : ClosedSubspace G, HasTraitClosureCharts R π G D → D = C) ∧
      IsIso (Functor.whiskerLeft
        (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))).op C.val.arrow.hom.hom) ∧
      (∃ _ : GrpObj (C.val : AlgebraicSpace (Spec (.of R))).obj.obj,
        IsMonHom C.val.arrow.hom.hom) ∧
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (prod.lift (𝟙 (C.val : AlgebraicSpace (Spec (.of R))).obj.obj)
          (𝟙 (C.val : AlgebraicSpace (Spec (.of R))).obj.obj)) ∧
      (∀ U : (C.val : AlgebraicSpace (Spec (.of R))).EtaleSite,
        Flat U.obj.left.hom ∧ LocallyOfFiniteType U.obj.left.hom ∧
          LocallyOfFinitePresentation U.obj.left.hom) ∧
      ∀ (T : Over (Spec (.of R))) (a : yoneda.obj T ⟶ G.obj.obj),
        Flat T.hom → ∃! l : yoneda.obj T ⟶ (C.val : AlgebraicSpace (Spec (.of R))).obj.obj,
          l ≫ C.val.arrow.hom.hom = a := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
