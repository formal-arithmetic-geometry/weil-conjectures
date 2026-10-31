/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.EtaleGenericImmersionProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Bounded-below Hom continuity for a perfect etale stratum

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14,
Remark 6.3.15 and the filtered-colimit argument of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-etale-stratum-hom-continuity).

The filtered colimit is formed on compatible complex representatives, not in the
ordinary triangulated category. A functorial model E and its natural identification e
specify all transition maps. The comparison is Q(colimit.post N E) followed by e at
colimit N. The second assertion gives all shifted Hom groups without choosing E.
Local constancy with perfect values is written out using the recorded perfect-ring
predicate and the existing derived constant and inverse-image functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Global derived Hom from a locally closed perfect stratum commutes with exact
filtered colimits of target representatives with a common cohomological lower bound.
The integer n includes every shift of P, and e identifies the entire functorial model.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-etale-stratum-hom-continuity).

Proof:
1. Factor the immersion as the supplied closed i followed by open j. Noetherianity
makes U and S qcqs and j quasi-compact (lem-weil-pbc-noetherian-open-subscheme-noetherian,
lem-weil-pbc-locally-noetherian-quasi-separated, lem-sfb-noetherian-open-immersion-qc).
Grothendieck exact filtered colimits commute with homology, preserving the common bound
and compatible quasi-isomorphisms (lem-pur-ringed-site-grothendieck-abelian,
src-weil-homology-preserves-exact-colimits). Use good truncations below r.
2. Exact constant-coefficient open inverse image preserves colimits and lower bounds
(lem-pe-constant-left-module-inverse-image, lem-weil-pbc-left-adjoint-preserves-colimits).
Apply lem-per-etale-closed-costalk-filtered-continuity on U to Ri! j* N.
This also identifies closed Ri* with exact termwise direct image and its colimit map.
3. Perfect duality (lem-sfb-ringed-site-perfect-duality) identifies local internal Hom
with tensor by the dual bounded finite-projective model. Finite sums, summands and finite
totalization commute with filtered colimits. Exact slice restriction and local detection
of isomorphisms globalize this (lem-weil-pbc-ringed-internal-hom-exact-restriction).
A finite trivializing cover (lem-weil-pbc-etale-qcqs-cofinal-finite-coverings) gives a
common upper degree b of the source models, hence lower bound r-b for these Homs.
4. The natural formula lem-weil-stratum-ambient-hom identifies ambient internal Hom
with Rj* i* of these internal Homs, including every original cocone leg.
5. The abelian higher direct images preserve filtered colimits
(lem-sbc-higher-direct-image-large-filtered-colimit); transport to module sheaves using
lem-weil-pbc-module-sheaves-colimits-forgetful. Apply
lem-per-right-derived-uniform-filtered-continuity to j*, using the bound r-b.
6. Apply the same theorem to global sections, whose higher functors preserve these
colimits by lem-weil-pbc-cohomology-filtered-colimit. The colimit universal property
identifies the composite with the displayed cocone-induced comparison. All operations
are natural. Shifts of P are still locally constant perfect and bounded, so the argument
applies to every n. Exact homology colimits and lem-sfb-global-rhom-coefficient-model
identify all shifted Hom groups. The empty stratum and zero coefficient ring give zero. -/
theorem isIso_etaleStratumGlobalHomColimitComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_ha : Topology.IsConstructible (Set.range (i ≫ j)))
    (P : DerivedCategoryModule A S)
    (_hPb : ∃ a b : ℤ, P.IsGE a ∧ P.IsLE b)
    (_hP : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ k : 𝒰.I₀,
      ∃ C : _root_.DerivedCategory (ModuleCat.{u + 1} A),
        _root_.DerivedCategory.IsPerfectRingComplex C ∧
        Nonempty ((ExternalRHom.pull A (𝒰.f k)).obj P ≅
          (ExternalRHom.constant A (𝒰.X k)).obj C))
    (n : ℤ)
    (E : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (e : E ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (ExternalRHom.globalHom A X).obj (op ((immersionLowerShriek A i j).obj (P⟦n⟧))))
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (r : ℤ) (_hN : ∀ k : J, (_root_.DerivedCategory.Q.obj (N.obj k)).IsGE r) :
    IsIso (_root_.DerivedCategory.Q.map (colimit.post N E) ≫ e.hom.app (colimit N)) := by
  sorry

/-- Every shifted derived Hom group carries the colimit cocone induced by the original
representatives. No choice of a global-Hom complex model is required in this assertion.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-etale-stratum-hom-continuity).
Proof: Follow steps 1--6 above, including the shifts n of P. The natural coefficient-model
cohomology identification of lem-sfb-global-rhom-coefficient-model identifies degree q
with Hom(a!(P[n]),N[q]). Exact filtered colimits commute with homology by
src-weil-homology-preserves-exact-colimits. The original cocone therefore becomes a
colimit cocone of abelian groups, with its original postcomposition maps. This also
includes negative q, n=0, the zero ring and the empty stratum. -/
theorem etaleStratum_shiftedHom_isColimit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_ha : Topology.IsConstructible (Set.range (i ≫ j)))
    (P : DerivedCategoryModule A S)
    (_hPb : ∃ a b : ℤ, P.IsGE a ∧ P.IsLE b)
    (_hP : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ k : 𝒰.I₀,
      ∃ C : _root_.DerivedCategory (ModuleCat.{u + 1} A),
        _root_.DerivedCategory.IsPerfectRingComplex C ∧
        Nonempty ((ExternalRHom.pull A (𝒰.f k)).obj P ≅
          (ExternalRHom.constant A (𝒰.X k)).obj C))
    (n : ℤ)
    {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
    (N : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (r : ℤ) (_hN : ∀ k : J, (_root_.DerivedCategory.Q.obj (N.obj k)).IsGE r) (q : ℤ) :
    Nonempty (IsColimit
      ((_root_.DerivedCategory.Q ⋙ shiftFunctor (DerivedCategoryModule A X) q ⋙
        preadditiveCoyoneda.obj (op ((immersionLowerShriek A i j).obj (P⟦n⟧)))).mapCocone
          (colimit.cocone N))) := by
  sorry

/-- Naturality of the cocone-induced comparison in both the source and target diagram.
The compatibility equation on η says that it models exactly precomposition by f.
Apply this with K=a!(P[n]), K'=a!(P'[n]) and f=a!(g[n]) for naturality in P.
Source: Bhatt--Scholze, Lemmas 6.3.14 and 6.3.16, pp. 47--48
(blueprint: lem-per-etale-stratum-hom-continuity).
Proof: Precompose with each colimit injection. The defining colimit.post equation
reduces the square to naturality of η and e, the compatibility with f, and bifunctoriality
of derived Hom. Uniqueness in the colimit universal property gives the asserted equality.
This is the naturality assertion in step 6, valid without the continuity hypotheses. -/
theorem etaleStratumGlobalHomColimitComparison_naturality
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K K' : DerivedCategoryModule A X) (f : K' ⟶ K)
    (E E' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (e : E ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (ExternalRHom.globalHom A X).obj (op K))
    (e' : E' ⋙ _root_.DerivedCategory.Q ≅ _root_.DerivedCategory.Q ⋙
      (ExternalRHom.globalHom A X).obj (op K'))
    (η : E ⟶ E')
    (_hη : Functor.whiskerRight η _root_.DerivedCategory.Q ≫ e'.hom =
      e.hom ≫ Functor.whiskerLeft _root_.DerivedCategory.Q
        ((ExternalRHom.globalHom A X).map f.op))
    {J : Type (u + 1)} [SmallCategory J]
    (N N' : J ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (α : N ⟶ N') :
    _root_.DerivedCategory.Q.map
        (colim.map (Functor.whiskerLeft N η ≫ Functor.whiskerRight α E')) ≫
      _root_.DerivedCategory.Q.map (colimit.post N' E') ≫ e'.hom.app (colimit N') =
    (_root_.DerivedCategory.Q.map (colimit.post N E) ≫ e.hom.app (colimit N)) ≫
      ((ExternalRHom.globalHom A X).map f.op).app
        (_root_.DerivedCategory.Q.obj (colimit N)) ≫
      ((ExternalRHom.globalHom A X).obj (op K')).map
        (_root_.DerivedCategory.Q.map (colim.map α)) := by
  have hpost :
      colim.map (Functor.whiskerLeft N η ≫ Functor.whiskerRight α E') ≫
        colimit.post N' E' =
      colimit.post N E ≫ η.app (colimit N) ≫ E'.map (colim.map α) := by
    apply colimit.hom_ext
    intro k
    simp only [colimit.ι_map_assoc, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc, colimit.ι_post]
    rw [← E'.map_comp, ← colimit.ι_map]
    rw [E'.map_comp, colimit.ι_post_assoc, η.naturality_assoc]
  rw [← Category.assoc, ← _root_.DerivedCategory.Q.map_comp, hpost]
  simp only [_root_.DerivedCategory.Q.map_comp, Category.assoc]
  have he := e'.hom.naturality (colim.map α)
  simp only [Functor.comp_map] at he
  change _root_.DerivedCategory.Q.map (E'.map (colim.map α)) ≫
    e'.hom.app (colimit N') = e'.hom.app (colimit N) ≫
      ((ExternalRHom.globalHom A X).obj (op K')).map
        (_root_.DerivedCategory.Q.map (colim.map α)) at he
  rw [he]
  have hη := NatTrans.congr_app _hη (colimit N)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hη
  rw [← Category.assoc (_root_.DerivedCategory.Q.map (η.app (colimit N)))
    (e'.hom.app (colimit N)), hη]
  simp only [Category.assoc]

end AlgebraicGeometry.Etale
