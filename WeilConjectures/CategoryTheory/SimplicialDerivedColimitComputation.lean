/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedColimitBar
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedAboveAcyclicComputation
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-!
# Simplicial computations of derived colimits

Source: Stacks Project, Cohomology on Sites, Tags 08Q9, 08PG, 08PH and 08PD
(blueprint: lem-trf-simplicial-derived-colimit-computation).

We write `E = Dᵒᵖ`, so a covariant diagram on `D` is a presheaf on `E`.
The derived colimit and all its bar maps are those of `CategoryColimitBarSystem`.
Signed bar generators translate its reversed face order to the first-vertex order.
The comparison is fixed by the projective-resolution roof of Stacks 08Q9, rather
than an unspecified isomorphism. No definition chooses data from the theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.SimplicialDerivedColimit

/-- The representable contractibility condition, allowing finite zigzags of cylinder
homotopies, as in Stacks 08Q9 and Simplicial, Definition 019K
(blueprint: lem-trf-simplicial-derived-colimit-computation). -/
def IsResolution {E : Type u} [SmallCategory E] (Q : SimplicialObject Eᵒᵖ) : Prop :=
  ∀ T : E, ∃ (f : Q ⋙ yoneda.obj T ⟶ (SimplicialObject.const (Type u)).obj PUnit)
    (g : (SimplicialObject.const (Type u)).obj PUnit ⟶ Q ⋙ yoneda.obj T),
    Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b)) (f ≫ g) (𝟙 _) ∧
    Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b)) (g ≫ f) (𝟙 _)

/-- Evaluate on `Q`, take alternating faces, and extend `n` to cochain degree `-n`.
Source: Stacks 08Q9 (blueprint: lem-trf-simplicial-derived-colimit-computation). -/
abbrev evaluationComplex {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (Q : SimplicialObject Eᵒᵖ) :
    (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (Functor.whiskeringLeft _ _ _).obj Q ⋙
    AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} R) ⋙
      ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)

/-- The canonical term coordinates of the alternating evaluation complex.
Source: Stacks 08Q9 (blueprint: lem-trf-simplicial-derived-colimit-computation). -/
def evaluationTerm {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (Q : SimplicialObject Eᵒᵖ) (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ) :
    ((evaluationComplex Q).obj F).X (-(n : ℤ)) ≅ F.obj (Q.obj (op ⦋n⦌)) :=
  ((AlgebraicTopology.alternatingFaceMapComplex _).obj (Q ⋙ F)).extendXIso
    ComplexShape.embeddingDownNat (i := n) rfl

/-- The actual double complex `P^p(Q_q)`, with second cochain index `-q`.
Source: Stacks 08Q9 (blueprint: lem-trf-simplicial-derived-colimit-computation). -/
abbrev resolutionDoubleComplex {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (Q : SimplicialObject Eᵒᵖ) (P : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((evaluationComplex Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- Derived colimit of a degree-zero presheaf, using the recorded universal left
 derived functor. Source: Stacks 08PG and 08Q9
(blueprint: lem-trf-simplicial-derived-colimit-computation). -/
def derivedColimit (B : CategoryColimitBarSystem.{u}) {E : Type u} [SmallCategory E]
    {R : Type u} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{u} R) :=
  (B.models E R).derived.obj
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F))

/-- The first-vertex bar coordinates. Reverse an `E` string to obtain a `D` string;
multiplication by `(-1)^(n(n+1)/2)` converts the alternating-face conventions.
Source: Stacks 08PG (blueprint: lem-trf-simplicial-derived-colimit-computation). -/
def forwardGenerator (B : CategoryColimitBarSystem.{u}) {E : Type u} [SmallCategory E]
    {R : Type u} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (c : ComposableArrows E n) : F.obj (op c.right) ⟶ ((B.models E R).bar.obj F).X (-↑n) :=
  (-1 : ℤ) ^ (n * (n + 1) / 2) • (B.models E R).generator F n c

/-- The canonical reindexing map, including the localization comparison for degreewise
restriction of scalars. Source: Stacks 08PH and 08PD
(blueprint: lem-trf-simplicial-derived-colimit-computation). -/
def derivedMap (B : CategoryColimitBarSystem.{u}) {E D : Type u}
    [SmallCategory E] [SmallCategory D] {R S : Type u} [CommRing R] [CommRing S]
    (u : E ⥤ D) (φ : R →+* S) {F : Eᵒᵖ ⥤ ModuleCat.{u} R}
    {G : Dᵒᵖ ⥤ ModuleCat.{u} S} (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ) :
    derivedColimit B F ⟶
      (ModuleCat.restrictScalars φ).mapDerivedCategory.obj (derivedColimit B G) :=
  (B.models E R).model.hom.app F ≫ DerivedCategory.Q.map (B.map u φ t) ≫
    (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app ((B.models D S).bar.obj G) ≫
      (ModuleCat.restrictScalars φ).mapDerivedCategory.map ((B.models D S).model.inv.app G)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The Stacks 08Q9 roof for a specified projective resolution. The two maps are fixed on
all total summands: the augmentation on the `p=0` edge, and the colimit cocone on the
`q=0` edge. Thus its derived roof specifies the canonical comparison.
Source: Stacks 08Q9 (blueprint: lem-trf-simplicial-derived-colimit-computation). -/
structure ResolutionRoof (B : CategoryColimitBarSystem.{u}) {E : Type u} [SmallCategory E]
    {R : Type u} [CommRing R] (F : Eᵒᵖ ⥤ ModuleCat.{u} R)
    (Q : SimplicialObject Eᵒᵖ) (P : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (a : P ⟶ (CochainComplex.singleFunctor _ 0).obj F) [QuasiIso a]
    (comparison : DerivedCategory.Q.obj ((evaluationComplex Q).obj F) ≅ derivedColimit B F)
    where
  toEvaluation : (resolutionDoubleComplex Q P).total (.up ℤ) ⟶ (evaluationComplex Q).obj F
  toColimit : (resolutionDoubleComplex Q P).total (.up ℤ) ⟶
    ((colim : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex (.up ℤ)).obj P
  evaluationEdge : ∀ n : ℕ,
    (resolutionDoubleComplex Q P).ιTotal (.up ℤ) 0 (-↑n) (-↑n) (by simp) ≫
        toEvaluation.f (-↑n) =
      (evaluationTerm Q (P.X 0) n).hom ≫ (a.f 0).app (Q.obj (op ⦋n⦌)) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom.app (Q.obj (op ⦋n⦌)) ≫
          (evaluationTerm Q F n).inv
  evaluationOffEdge : ∀ (p q i : ℤ), p ≠ 0 →
    (resolutionDoubleComplex Q P).ιTotalOrZero (.up ℤ) p q i ≫ toEvaluation.f i = 0
  colimitEdge : ∀ p : ℤ,
    (resolutionDoubleComplex Q P).ιTotal (.up ℤ) p 0 p (by simp) ≫ toColimit.f p =
      (evaluationTerm Q (P.X p) 0).hom ≫ colimit.ι (P.X p) (Q.obj (op ⦋0⦌))
  colimitOffEdge : ∀ (p q i : ℤ), q ≠ 0 →
    (resolutionDoubleComplex Q P).ιTotalOrZero (.up ℤ) p q i ≫ toColimit.f i = 0
  evaluationQuasiIso : QuasiIso toEvaluation
  colimitQuasiIso : QuasiIso toColimit
  canonical : comparison.hom ≫
      inv ((B.models E R).derived.map (DerivedCategory.Q.map a)) ≫
        (B.models E R).comparison.app P =
    inv (DerivedCategory.Q.map toEvaluation) ≫ DerivedCategory.Q.map toColimit

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Simultaneous, canonically normalized comparisons and all semilinear reindexing squares.
No hypothesis is imposed on the intermediate simplicial object `Q ⋙ u.op`.
Source: Stacks 08Q9, 08PG, 08PH and 08PD
(blueprint: lem-trf-simplicial-derived-colimit-computation). -/
structure Computation (B : CategoryColimitBarSystem.{u}) where
  comparison : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (Q : SimplicialObject Eᵒᵖ) (_hQ : IsResolution Q),
    DerivedCategory.Q.obj ((evaluationComplex Q).obj F) ≅ derivedColimit B F
  projectiveResolution : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R),
    ∃ (P : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
      (a : P ⟶ (CochainComplex.singleFunctor _ 0).obj F),
      P.IsStrictlyLE 0 ∧ (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso a
  computation : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (Q : SimplicialObject Eᵒᵖ) (hQ : IsResolution Q)
    (P : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (a : P ⟶ (CochainComplex.singleFunctor _ 0).obj F) [QuasiIso a],
    P.IsStrictlyLE 0 → (∀ i : ℤ, Projective (P.X i)) →
      Nonempty (ResolutionRoof B F Q P a (comparison F Q hQ))
  forwardDifferential : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ) (c : ComposableArrows E (n + 1)),
    forwardGenerator B F (n + 1) c ≫ ((B.models E R).bar.obj F).d (-↑(n + 1)) (-↑n) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        (categoryBarFaceCoefficient F c j.rev ≫
          forwardGenerator B F n (categoryBarDelete c j.rev))
  forwardMap : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (u : E ⥤ D) (φ : R →+* S)
    {F : Eᵒᵖ ⥤ ModuleCat.{u} R} {G : Dᵒᵖ ⥤ ModuleCat.{u} S}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ)
    (n : ℕ) (c : ComposableArrows E n) (x : F.obj (op c.right)),
    (B.map u φ t).f (-↑n) (forwardGenerator B F n c x) =
      forwardGenerator B G n (c ⋙ u) (t.app (op c.right) x)
  evaluationMap : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (u : E ⥤ D) (φ : R →+* S)
    {F : Eᵒᵖ ⥤ ModuleCat.{u} R} {G : Dᵒᵖ ⥤ ModuleCat.{u} S}
    (_t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ)
    {Q : SimplicialObject Eᵒᵖ} {Q' : SimplicialObject Dᵒᵖ} (_k : Q ⋙ u.op ⟶ Q'),
    (evaluationComplex Q).obj F ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
        ((evaluationComplex Q').obj G)
  evaluationFormula : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (u : E ⥤ D) (φ : R →+* S)
    {F : Eᵒᵖ ⥤ ModuleCat.{u} R} {G : Dᵒᵖ ⥤ ModuleCat.{u} S}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ)
    {Q : SimplicialObject Eᵒᵖ} {Q' : SimplicialObject Dᵒᵖ} (k : Q ⋙ u.op ⟶ Q')
    (n : ℕ) (x : F.obj (Q.obj (op ⦋n⦌))),
    (evaluationTerm Q' G n).hom
      ((evaluationMap u φ t k).f (-↑n) ((evaluationTerm Q F n).inv x)) =
        G.map (k.app (op ⦋n⦌)) (t.app (Q.obj (op ⦋n⦌)) x)
  naturality : ∀ {E D : Type u} [SmallCategory E] [SmallCategory D]
    {R S : Type u} [CommRing R] [CommRing S] (u : E ⥤ D) (φ : R →+* S)
    {F : Eᵒᵖ ⥤ ModuleCat.{u} R} {G : Dᵒᵖ ⥤ ModuleCat.{u} S}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ)
    {Q : SimplicialObject Eᵒᵖ} {Q' : SimplicialObject Dᵒᵖ}
    (hQ : IsResolution Q) (hQ' : IsResolution Q') (k : Q ⋙ u.op ⟶ Q'),
    DerivedCategory.Q.map (evaluationMap u φ t k) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app
          ((evaluationComplex Q').obj G) ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map (comparison G Q' hQ').hom =
      (comparison F Q hQ).hom ≫ derivedMap B u φ t
  identity : ∀ {E : Type u} [SmallCategory E] {R : Type u} [CommRing R]
    (F : Eᵒᵖ ⥤ ModuleCat.{u} R),
    derivedMap B (𝟭 E) (RingHom.id R) (𝟙 F) ≫
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsId R) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app (derivedColimit B F) = 𝟙 _
  composition : ∀ {E D H : Type u} [SmallCategory E] [SmallCategory D] [SmallCategory H]
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (u : E ⥤ D) (v : D ⥤ H) (φ : R →+* S) (ψ : S →+* T)
    {F : Eᵒᵖ ⥤ ModuleCat.{u} R} {G : Dᵒᵖ ⥤ ModuleCat.{u} S}
    {N : Hᵒᵖ ⥤ ModuleCat.{u} T}
    (t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars φ)
    (s : G ⟶ v.op ⋙ N ⋙ ModuleCat.restrictScalars ψ)
    (a : F ⟶ (u ⋙ v).op ⋙ N ⋙ ModuleCat.restrictScalars (ψ.comp φ)),
    (∀ (U : Eᵒᵖ) (x : F.obj U), a.app U x = s.app (u.op.obj U) (t.app U x)) →
    derivedMap B (u ⋙ v) (ψ.comp φ) a ≫
      (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp φ ψ) ≪≫
        Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars ψ)
          (ModuleCat.restrictScalars φ)).hom.app (derivedColimit B N) =
      derivedMap B u φ t ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map
        (derivedMap B v ψ s)

/-- Contractible representable evaluations compute derived colimits, canonically and
naturally under reindexing and coefficient restriction. Source: Stacks 08Q9, 08PG,
08PH and 08PD (blueprint: lem-trf-simplicial-derived-colimit-computation).

Proof: (1) Use lem-trf-derived-colimit-bar and the sign change `(-1)^(n(n+1)/2)`
to identify its reversed bar convention with first-vertex coordinates. Free representables
are projective, and their sum over all sections surjects onto any presheaf. Apply
lem-trf-bounded-above-acyclic-derived-computation to identify the universal derived
colimit with computation on any projective resolution.
(2) Form the two-sided bar modules indexed by strings ending at `Q_q`, with commuting
horizontal and vertical faces and total differential `d_h + (-1)^p d_v`. The horizontal
augmentation applies `F` to the last arrow; the vertical augmentation forgets that arrow.
(3) Appending the identity of `Q_q`, with sign `(-1)^(p+1)`, contracts the augmented
horizontal rows, including the augmentation degree.
(4) For each fixed string, the vertical complex is the free chain complex of
`Hom(T_p,Q)` tensored with `F(T_0)`. Apply
lem-weil-pbc-simplicial-homotopy-free-chain-homotopy to the homotopy inverse and its
finite homotopy zigzags. The singleton complex contracts to its degree-zero augmentation
with homotopy identity in odd degrees and zero in even degrees. Tensoring this identity
requires no flatness. Direct sums give all vertical augmentation quasi-isomorphisms.
(5) Apply lem-pc-bounded-above-double-complex-total-comparison in both directions.
All diagonals are finite; transposition changes signs by `(-1)^(pq)`, which is one
on the augmentation edge. Both augmentation maps are quasi-isomorphisms.
(6) Invert the evaluation augmentation and compose with the bar augmentation and
its canonical derived comparison. This roof is independent of the contractions.
The same augmented-resolution comparison applied to a projective resolution gives
precisely `ResolutionRoof.canonical`: its two edge maps are the Stacks 08Q9 maps.
(7) Reindex strings by `u`, apply `t` to coefficients, and postcompose the last arrow
with `k`. Naturality of `t`, simpliciality of `k` and functoriality of `u` give both
augmentation squares. Inverting them gives `Computation.naturality`. Only `Q` and `Q'`
need representable contractibility, never `Q ⋙ u.op`.
(8) Restriction of scalars preserves the underlying additive groups, direct sums,
kernels, images, and quasi-isomorphisms. All displayed maps and inverse comparisons
therefore restrict degreewise. The bar generator formula proves identity and composition,
with exactly the canonical restriction and localization identifications displayed above. -/
theorem computation_exists (B : CategoryColimitBarSystem.{u}) : Nonempty (Computation B) := by
  sorry

end CategoryTheory.SimplicialDerivedColimit
