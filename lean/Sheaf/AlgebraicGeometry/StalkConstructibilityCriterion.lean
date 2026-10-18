/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.Constructible
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.GeometricStalkComparisonConstant
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.EtaleGenericIrreducibleNeighbourhood
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Constructibility from finite geometric stalk cardinalities

Source: SGA 4, Exposé IX, Proposition 2.13(iii), and the blueprint lemma
`fin4-lem-stalk-constructibility-criterion`
(blueprint: fin4-lem-stalk-constructibility-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A constant chart computes every geometric stalk in its image. -/
private theorem abelian_stalk_iso_of_chart {X V : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : V ⟶ X) [Etale f] (A : AddCommGrpCat.{u + 1})
    (e : (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj F ≅
      (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range f) :
    Nonempty (((pointSmallEtale s).sheafFiber.obj F) ≅ A) := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨v, hv⟩ := hs
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed f s v
    (hv.trans (congrArg s (Subsingleton.elim _ _)))
  rw [← ht]
  exact ⟨((AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
    AddCommGrpCat.{u + 1} f t).app F).symm ≪≫
    (pointSmallEtale t).sheafFiber.mapIso e ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso A⟩

/-- Trivializations make stalk isomorphism classes locally constant on the base. -/
private theorem abelian_stalk_iso_near {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Cover.{u} etalePrecoverage X)
    (hV : ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1},
      Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj F ≅
        (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) (x : X) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ A : AddCommGrpCat.{u + 1},
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        s (IsLocalRing.closedPoint Ω) ∈ O →
          Nonempty (((pointSmallEtale s).sheafFiber.obj F) ≅ A) := by
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨i, v, rfl⟩ := V.exists_eq x
  have : Etale (V.f i) := V.map_prop i
  obtain ⟨A, ⟨e⟩⟩ := hV i
  exact ⟨Set.range (V.f i), (V.f i).isOpenMap.isOpen_range, ⟨v, rfl⟩, A,
    fun Ω _ _ s hs ↦ abelian_stalk_iso_of_chart F (V.f i) A e s hs⟩

/-- The cardinality loci of a sheaf with constant charts are open. -/
private theorem abelian_cardinality_locus_isOpen {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Cover.{u} etalePrecoverage X)
    (hV : ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1},
      Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj F ≅
        (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) (n : ℕ) :
    IsOpen {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F) = n} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨O, hO, hxO, A, hA⟩ := abelian_stalk_iso_near F V hV x
  refine ⟨O, fun y hy ↦ ?_, hO, hxO⟩
  obtain ⟨e⟩ := hA _ (X.algClosurePoint x) (by simpa using hxO)
  obtain ⟨e'⟩ := hA _ (X.algClosurePoint y) (by simpa using hy)
  exact (Nat.card_congr (e' ≪≫ e.symm).addCommGroupIsoToAddEquiv.toEquiv).trans hx

/-- A constant-chart restriction identifies cardinalities along an immersion. -/
private theorem abelian_cardinality_immersion {X T : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ι : T ⟶ X) [IsImmersion ι]
    (V : Cover.{u} etalePrecoverage T)
    (hV : ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1},
      Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj
        ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} ι).obj F) ≅
          (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) (t : T) :
    Nat.card (((pointSmallEtale (X.algClosurePoint (ι t))).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj F) =
    Nat.card (((pointSmallEtale (T.algClosurePoint t)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} ι).obj F)) := by
  obtain ⟨s, hs⟩ := IsImmersion.exists_comp_eq_of_field ι (X.algClosurePoint (ι t))
    ⟨t, by simp⟩
  have hst : s (IsLocalRing.closedPoint _) = t := ι.isEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hs, algClosurePoint_base])
  let G := (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} ι).obj F
  obtain ⟨O, -, htO, A, hA⟩ := abelian_stalk_iso_near G V hV t
  obtain ⟨e⟩ := hA _ s (by simpa [hst] using htO)
  obtain ⟨e'⟩ := hA _ (T.algClosurePoint t) (by simpa using htO)
  rw [← hs]
  let eTotal := ((AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
    AddCommGrpCat.{u + 1} ι s).app F).symm ≪≫ e ≪≫ e'.symm
  exact Nat.card_congr eTotal.addCommGroupIsoToAddEquiv.toEquiv

/-- Finite stratifications with constant charts have constructible cardinality loci. -/
private theorem abelian_constructible_cardinality {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf F) (n : ℕ) :
    Topology.IsConstructible {x : X | Nat.card
      (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) = n} := by
  classical
  obtain ⟨S, hS, hloc⟩ := hF
  let C := {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
    (A := AddCommGrpCat.{u + 1})).obj F) = n}
  have heq : C = ⋃ i, (S.stratum i ∩ C) := by
    rw [← Set.iUnion_inter, S.iUnion_stratum_eq_univ, Set.univ_inter]
  change Topology.IsConstructible C
  rw [heq]
  refine Topology.IsConstructible.iUnion fun i ↦ ?_
  obtain ⟨V, hV⟩ := hloc i
  have hV' : ∀ j : V.I₀, ∃ A : AddCommGrpCat.{u + 1},
      Nonempty ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (V.f j)).obj
        ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).obj F) ≅
          (constantSheaf (V.X j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) := by
    intro j
    obtain ⟨A, -, e⟩ := hV j
    exact ⟨A, e⟩
  obtain ⟨O, hO, hOe⟩ := (S.immersion i).isEmbedding.isInducing.isOpen_iff.mp
    (abelian_cardinality_locus_isOpen _ V hV' n)
  have hinter : S.stratum i ∩ C = S.stratum i ∩ O := by
    rw [← S.range_immersion]
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion i) ⁻¹' O
      rw [hOe]
      exact (abelian_cardinality_immersion F (S.immersion i) V hV' t).symm.trans hx
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion i) ⁻¹' O at hx
      rw [hOe] at hx
      exact (abelian_cardinality_immersion F (S.immersion i) V hV' t).trans hx
  rw [hinter]
  exact (hS i).inter hO.isConstructible_of_noetherianSpace

/-- Stalk cardinality is independent of the chosen geometric point. -/
private theorem abelian_cardinality_eq_of_same_point {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω') ⟶ X)
    (hst : s (IsLocalRing.closedPoint Ω) = t (IsLocalRing.closedPoint Ω')) :
    Nat.card (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) =
      Nat.card (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F) := by
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let U := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  let M := (sheafCompose X.smallEtaleTopology E).obj F
  let eAb : (sheafCompose X.smallEtaleTopology U).obj M ≅ F :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerLeft F.obj
        (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.counitIso ≪≫
          Functor.rightUnitor F.obj)
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u} U :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨β, -⟩ := exists_geometricStalkComparison_constant
    (Λ := ULift.{u + 1} ℤ) s t hst
  let e := ((pointSmallEtale s).sheafFiber.mapIso eAb).symm ≪≫
    ((pointSmallEtale s).sheafFiberCompIso U).app M ≪≫ U.mapIso (β.app M) ≪≫
      (((pointSmallEtale t).sheafFiberCompIso U).app M).symm ≪≫
        (pointSmallEtale t).sheafFiber.mapIso eAb
  exact Nat.card_congr e.addCommGroupIsoToAddEquiv.toEquiv

/-- Pullback reads a cardinality locus as the preimage of the original locus. -/
private theorem abelian_cardinality_pullback {X Y : Scheme.{u}}
    (f : Y ⟶ X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (y : Y) :
    Nat.card (((pointSmallEtale (Y.algClosurePoint y)).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)) =
      Nat.card (((pointSmallEtale (X.algClosurePoint (f y))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) := by
  let e := (AlgebraicGeometry.Etale.upperStarCompSheafFiberIso
    AddCommGrpCat.{u + 1} f (Y.algClosurePoint y)).app F
  exact (Nat.card_congr e.addCommGroupIsoToAddEquiv.toEquiv).trans
    (abelian_cardinality_eq_of_same_point F (Y.algClosurePoint y ≫ f)
      (X.algClosurePoint (f y)) (by simp))

/-- Constructibility of all cardinality loci is preserved by every pullback. -/
private theorem abelian_cardinality_loci_pullback {X Y : Scheme.{u}}
    (f : Y ⟶ X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
      {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) = n}) :
    ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
      {y : Y | Nat.card (((pointSmallEtale (Y.algClosurePoint y)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
          ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)) = n} := by
  intro n hn
  have h := f.isConstructible_preimage (hF n hn)
  convert h using 1
  ext y
  exact iff_of_eq (congrArg (· = n) (abelian_cardinality_pullback f F y))

/-- Converse constructibility criterion from cardinality loci.

This is the Noetherian-induction converse of SGA 4, Exposé IX, Proposition 2.13(iii).
The proof uses the finite-stalk constant-cardinality open construction on an irreducible
Noetherian open, followed by Noetherian induction on closed complements.
(blueprint: fin4-lem-stalk-constructibility-criterion-converse) -/
theorem isConstructibleAbelianSheaf_of_constructible_stalk_cardinality_loci
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X),
      Finite (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F))
    (hloci : ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
      {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) = n}) :
    IsConstructibleAbelianSheaf F := by
  sorry

/-- An abelian étale sheaf with finite geometric stalks on a Noetherian scheme is
constructible exactly when every positive stalk-cardinality locus is constructible.
The geometric point over `x` used for the locus is the spectrum of an algebraic closure
of its residue field. Constructibility means a single finite locally closed partition
with finite locally constant abelian restrictions, as in `IsConstructibleAbelianSheaf`.

Source: SGA 4, Exposé IX, Proposition 2.13(iii), and the blueprint lemma
`fin4-lem-stalk-constructibility-criterion`.

Proof plan:
1. Suppose F is constructible in the abelian sense [def-weil-pbc-constructible-abelian-sheaf].
Fix one of its finitely many locally closed strata S. On an etale trivializing cover V_i of S
the restriction is the constant abelian sheaf with finite value A_i. The inverse-image stalk
isomorphism [lem-weil-pbc-inverse-image-stalk-germ] and the constant stalk theorem [lem-weil-
pbc-constant-sheaf-geometric-stalk] identify its stalks with A_i. Every geometric point over a
point of the image of V_i lifts to V_i [lem-weil-pbc-etale-cover-geometric-point-lift], so
cardinality equals |A_i| on that entire image. Etale morphisms are flat and locally of finite
presentation [def-weil-etale-morphism], so these images are open by [lem-weil-pbc-flat-lfp-
open]. For each n their union with |A_i|=n is C_n intersect S, and the union with |A_i| unequal
to n is its complement in S. Hence C_n intersect S is clopen in S, thus locally closed in X.
There are only finitely many strata; their union is constructible by the Noetherian
characterization in [def-weil-constructible-subset]. This does not presume a finite etale cover
or globally constant cardinality on a stratum.

2. For the converse perform Noetherian induction on the closed subsets T of X, giving each its
reduced induced closed subscheme structure supplied by [lem-weil-pbc-reduced-induced-closed-
subscheme]. On an affine Noetherian chart Spec(R) of X this structure is Spec(R/I); any
ascending chain of ideals of R/I lifts to an ascending chain of ideals of R containing I, so R/I
is Noetherian. Its underlying closed subset is quasi-compact, hence this is a Noetherian scheme.
The induction assertion is that the abelian inverse image F_T has a finite locally closed
partition with finite locally constant abelian restrictions. The empty closed subset has the
empty partition. At T assume the assertion for every proper closed subset. By [lem-weil-pbc-
inverse-image-stalk-germ] the stalks of F_T are those of F at the corresponding geometric
points, so they are finite, and its cardinality level sets are C_n intersect T. These are
constructible in T by [def-weil-constructible-subset]. By [lem-weil-pbc-noetherian-scheme-
closed-subsets-minimal], the closed subsets of X satisfy the minimal condition, giving the
stated Noetherian induction. A chain of subsets closed in a fixed closed T is also a chain of
closed subsets of X, so the same condition holds in T. It therefore suffices to construct one
nonempty open W of a nonempty T where F_T is finite locally constant; its complement is proper
closed, to which the induction hypothesis applies. In the next steps write X and F for T and
F_T.

3. Choose an irreducible component of the nonempty X and its generic point eta, whose existence
is supplied by [lem-sc-scheme-sober]. There are finitely many irreducible components by [lem-
weil-pbc-noetherian-finite-components]. Remove all components other than the chosen one. The
resulting open X_0 contains eta and is irreducible. Let M=F_bar_eta and m=|M|, which is at least
1 for an abelian group. The constructible set C_m intersect X_0 is a finite union of locally
closed subsets [def-weil-constructible-subset] and contains eta. One of those subsets contains
eta. In an expression O intersect Z for that subset, Z is closed in X_0 and contains eta, so
Z=X_0. Thus it contains a nonempty open U of X_0 on which every stalk has exactly m elements.

4. The stalk is the colimit of sections on pointed etale neighbourhoods [def-weil-pbc-geometric-
stalks]. Its index is filtered by [lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered]; use a
small skeleton of affine pointed objects, with all their lifts, supplied by [lem-weil-pbc-
affine-etale-essentially-small-cover]. Affine open refinement retains the marked point, so this
subsystem is cofinal for stalks. Apply the elementwise filtered-colimit theorem [lem-weil-pbc-
filtered-colimit-modules-elementwise] with R=Z (abelian groups are Z-modules) to lift every a in
the finite group M to a section s_a on a common pointed etale neighbourhood V_0 of bar_eta in U.
Each of the finitely many relations s_0=0 and s_a+s_b=s_(a+b) has zero germ. The same theorem
kills each relation after a further refinement, and cofilteredness gives one common pointed
refinement on which all hold. The table a maps to s_a is now a group homomorphism M to F(V_0).
Restricting these sections to each etale object over V_0 gives a natural map from the constant
abelian presheaf to F restricted to V_0. By [def-weil-pbc-constant-sheaf] and the sheafification
universal property [def-weil-pbc-sheafification] it extends uniquely to phi:constant M to F
restricted to V_0. Restriction and inverse image agree by [lem-weil-pbc-etale-inverse-image-
restriction]. The constant stalk theorem identifies its marked stalk map with the identity of M.

5. Apply [lem-weil-pbc-etale-generic-irreducible-neighbourhood] to V_0 to U and the underlying
point of its marked lift over eta. Here U is Noetherian and irreducible, eta is its component
generic point, and V_0 to U is etale; no reducedness or normality is assumed. It gives an
irreducible open V retaining the marked lift whose underlying point is generic in V. Restrict
each section s_a to V. Restriction is a homomorphism, so s_0=0 and s_a+s_b=s_(a+b) still hold.
For each etale object E over V, send a to s_a restricted to E; these homomorphisms commute with
restriction and define a morphism from the constant abelian presheaf with value M to F
restricted to V. The universal property [def-weil-pbc-sheafification] extends this to
phi:constant M to F restricted to V, with the source defined by [def-weil-pbc-constant-sheaf].
The restriction sheaf agrees with abelian inverse image by [lem-weil-pbc-etale-inverse-image-
restriction]. Germ compatibility in [lem-weil-pbc-inverse-image-stalk-germ] identifies the
retained germs of these sections with their original germs, namely a; [lem-weil-pbc-constant-
sheaf-geometric-stalk] identifies the source stalk with M through these same constant sections.
Hence the newly defined phi induces the identity on M at the retained point.

6. For a nonzero a in M let Z_a be the set of points of V where the section phi(a)=s_a has zero
geometric germ. The elementwise stalk-colimit criterion [lem-weil-pbc-filtered-colimit-modules-
elementwise], with the pointed neighbourhood and smallness results of step 4, says that a zero
germ vanishes as a section on a further pointed etale neighbourhood. Conversely vanishing as a
section gives zero germs throughout that neighbourhood; the germ identification [lem-weil-pbc-
inverse-image-stalk-germ] makes this assertion independent of restriction notation. Its image in
V is open by [def-weil-etale-morphism] and [lem-weil-pbc-flat-lfp-open], and geometric points
over every point of that image lift by [lem-weil-pbc-etale-cover-geometric-point-lift]. Thus Z_a
is precisely a union of open images. It omits the generic point: if any vanishing neighbourhood
had that point in its image, the retained geometric generic point would lift to that
neighbourhood by [lem-weil-pbc-etale-cover-geometric-point-lift], forcing s_a to have zero germ
at the retained lift, contrary to the identity marked stalk map. Thus no choice-independence
theorem for germs is being assumed. Every nonempty open of irreducible V contains its generic
point, so Z_a is empty. The constant stalk theorem [lem-weil-pbc-constant-sheaf-geometric-stalk]
identifies every source stalk with M; consequently phi is injective on all stalks. The inverse-
image stalk theorem identifies every target stalk with a stalk of F at a point of U, hence both
source and target have m elements. An injective map of finite sets of the same cardinality is
bijective. By [lemma-weil-pbc-geometric-stalk-conservative], phi is an isomorphism of abelian
sheaves on V.

7. The image W of V to X is a nonempty open by [def-weil-etale-morphism] and [lem-weil-pbc-flat-
lfp-open]. The same map V to W is an etale surjection and its restriction of F is constant with
finite abelian value M by step 6 and [lem-weil-pbc-etale-inverse-image-restriction]. This is the
required finite locally constant condition in [def-weil-pbc-constructible-abelian-sheaf]; the
inverse-image composition isomorphism [lem-weil-pbc-inverse-image-composition] identifies the
iterated restriction with the original one. The induction hypothesis of step 2 gives a finite
lisse partition on X minus W. Regard those strata as strata of X through the closed immersion,
and adjoin W. Locally closed subsets of a closed subset remain locally closed in X; by [def-
weil-constructible-subset] they are constructible since X is Noetherian. The composition
isomorphism identifies their abelian inverse images with the restrictions provided by induction.
This proves the induction assertion and the converse. For empty X the empty partition already
proves both directions. The obtained finite partition, with finitely many constant cardinalities
on each Noetherian stratum after a finite subcover of the open trivializing images, also yields
a finite image of the cardinality function; an infinite union of constructible sets was never
used to infer a bound.

(blueprint: fin4-lem-stalk-constructibility-criterion). -/
theorem isConstructibleAbelianSheaf_iff_constructible_stalk_cardinality_loci
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X),
      Finite (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)) :
    IsConstructibleAbelianSheaf F ↔
      ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible
        {x : X | Nat.card (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj F) = n} := by
  constructor
  · intro hF n _
    exact abelian_constructible_cardinality F hF n
  · intro hloci
    exact isConstructibleAbelianSheaf_of_constructible_stalk_cardinality_loci
      X F hfinite hloci

end AlgebraicGeometry.Scheme
