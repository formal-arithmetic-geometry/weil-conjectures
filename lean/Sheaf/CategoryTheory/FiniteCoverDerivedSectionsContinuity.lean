module

public import Sheaf.CategoryTheory.FiniteCoverDerivedSectionsData
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit
import Mathlib.Algebra.Category.Grp.AB

/-! # Derived global sections on a filtered colimit of finite-cover sites

Source: Stacks Project, Cohomology on Sites, 0EXZ and 09YP; Derived Categories,
013K, 013P, 013S and 015E
(blueprint: lem-per-finite-cover-derived-sections-continuity).

The map is a morphism in the ordinary derived category of abelian groups. Its
source is the exact filtered derived colimit, represented by the termwise colimit
of compatible resolved section complexes. Its target is global sections of the
receiving K-injective resolution, hence precisely total right derived sections
in the shared K-injective bridge. No cohomological-dimension bound occurs.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FiniteCoverDerivedSections

/-- The actual inverse-image colimit diagram exists, with the prescribed transitions.
Source: Stacks, Sites 0A35; Cohomology on Sites 09YP
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof: apply the actual inverse-image functor at every projection. Transpose the
system transitions by the projection adjunctions, using the strict Cat cocone
relations. The unit equations and the system cocycle equations give the diagram
identity and composition laws. Abelian sheaves have all small colimits, and
complex colimits are computed termwise. Choose such a colimit cocone with its
universal-property proof; this gives precisely System.Colimit. -/
theorem exists_coefficient_colimit (S : Sites.{u}) (K : System S) :
    Nonempty K.Colimit := by
  sorry

/-- Compatible resolution presentations exist for every uniformly bounded-below system.
Source: Stacks 0EXZ, 013K, 070J, 013P
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof: form the abelian category of systems with the exact inverse-image transitions.
Evaluation has an exact left adjoint, given by sums of inverse images over arrows,
and a right adjoint, given by products of direct images. The right adjoints give
embeddings into injective systems; the exact left adjoints show that their values
at every site are injective. Resolve the system complex monomorphically in this
category, retaining b, as in lem-per-varying-site-system-injective-resolutions.
Resolve the actual colimit complex monomorphically at the limit site. Exact inverse
image and filtered colimits make the induced map from the original colimit to the
resolved colimit a monomorphic quasi-isomorphism. Lift it into the receiving
injective resolution (013P), giving the compatible extension legs. Adjunction-unit
sections at terminal objects supply the section diagram and the receiving cocone.
All these complexes have bound b; bounded-below injective complexes are K-injective
by lem-sp-kinjective-computes. -/
theorem exists_model (S : Sites.{u}) (K : System S) (C : K.Colimit)
    (b : ℤ) (hbelow : ∀ (i : S.Index) (n : ℤ), n < b → IsZero ((K.complex i).X n)) :
    Nonempty (Model K C b) := by
  sorry

/-- The canonical derived comparison is invertible, and its maps in every integer
cohomological degree exhibit the canonical filtered colimit.
Source: Stacks 09YP, 09YN, 015E
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof:
1. Resolve the system compatibly as in lem-per-varying-site-system-injective-resolutions.
   Every stage resolution computes derived sections by lem-sp-kinjective-computes and
   def-sfb-right-derived-functor. Its transition maps are the adjunction-unit section
   maps followed by the actual coefficient transitions.
2. Form L, the termwise colimit of the inverse images of the resolved complexes.
   Exact inverse image and exact filtered colimits of abelian sheaves preserve the
   kernels, images and quotients defining homology, so K to L is a monomorphic
   quasi-isomorphism. Every term of L is section-acyclic by
   lem-weil-pbc-cohomology-colimit-of-sites applied to stage injectives at terminal
   objects and lemma-weil-pbc-leray-acyclicity. L retains the lower bound b.
3. Degree-zero continuity (lem-weil-pbc-colimit-of-sites-sections) identifies the
   termwise colimit of the stage section complexes with sections of L. The under-
   category at a fixed stage is final: common refinements and equalization in the
   filtered category extend its cocones uniquely. The degreewise identifications
   commute with differentials because they come from the actual coprojections.
4. Filtered colimits of abelian groups are exact, hence preserve quasi-isomorphisms.
   Thus this source is the exact filtered derived colimit. The acyclic-complex
   theorem sk-thm-acyclicity inverts the derived unit on L. Together with the
   inverse of K to L it gives the required isomorphism of derived objects.
5. Extend L into the receiving injective resolution by the lift-along-injective-
   quasi-iso theorem. Unit naturality identifies the preceding isomorphism with
   the localized chain map M.comparison. Its legs are exactly the projection
   pullbacks followed by the actual coprojections, by Model.extension and the
   section normalizations. Consequently its homology maps are the prescribed
   filtered-colimit maps. Exactness of filtered colimits commutes homology with
   the source colimit, giving the last universal-property clause.
6. Lifts are unique up to homotopy (013S); sections and termwise colimits preserve
   those homotopies. This proves independence of all resolution choices.
7. For a compatible change of finite-cover site systems, resolve once over the
   combined index category. Ordinary adjunction-unit section maps commute with
   the connecting functors and coprojections. Receiving lifts and homotopy
   uniqueness identify this square with the canonical derived pullback square.
8. Final reindexing preserves termwise colimits and their coprojections. Exact
   inverse image and filtered colimit commute with canonical upper truncations,
   since their only altered term is a kernel. Apply coefficient naturality to
   every truncation inclusion and every map between two such truncations. This
   uses only the lower bound, with no bound on cohomological dimensions. -/
theorem continuity {S : Sites.{u}} {K : System S} {C : K.Colimit} {b : ℤ}
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (M : Model K C b) :
    IsIso (DerivedCategory.Q.map M.comparison) ∧
      ∀ n : ℤ, Nonempty (IsColimit
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
          (ComplexShape.up ℤ) n).mapCocone M.sectionCocone.cocone)) := by
  sorry

/-- Naturality holds for every compatible lift, including changes of sites and index.
Source: Stacks 08J6, 013P, 013S, 09YP
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof: the difference between the two maps from the resolved system to the
pushforward of the receiving resolution vanishes on the original system, by the
coefficient and coprojection equations. The colimit inverse-image functor is exact,
so its right adjoint sends the receiving injective complex to a K-injective system.
The lift uniqueness theorem 013S makes this difference null-homotopic in the system
category. Apply sections and filtered colimit to that homotopy and localize. This
is precisely the displayed square, because all its chain legs are normalized by
the ordinary adjunction units. This also applies to identities and composites. -/
theorem naturality {S T : Sites.{u}} {U : SiteChange S T}
    {K : System S} {C : K.Colimit} {L : System T} {D : L.Colimit}
    {h : Change U K C L D} {b c : ℤ} {M : Model K C b} {N : Model L D c}
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (v : h.Lift M N) : v.Commutes := by
  sorry

/-- Compatible site and coefficient changes have simultaneous resolution lifts.
Source: Stacks 0EXZ, 013K, 013P
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof: put the two diagrams and their connecting functors in the small combined
index category, with the given coherent squares. Resolve their coefficient complex
once in its abelian system category, with lower bound b. Restriction gives stage
injective resolutions on both diagrams and strictly compatible connecting maps.
Resolve their actual colimits, extending the coefficient map to receiving injective
resolutions by 013P. The normalized section maps form the natural transformation
and receiving section map required in Change.Lift. Naturality identifies its square
with the canonical derived pullback square. -/
theorem exists_change_lift {S T : Sites.{u}} (U : SiteChange S T)
    (K : System S) (C : K.Colimit) (L : System T) (D : L.Colimit)
    (h : Change U K C L D) (b : ℤ)
    (hK : ∀ (i : S.Index) (n : ℤ), n < b → IsZero ((K.complex i).X n))
    (hL : ∀ (i : T.Index) (n : ℤ), n < b → IsZero ((L.complex i).X n)) :
    ∃ (M : Model K C b) (N : Model L D b), Nonempty (h.Lift M N) := by
  sorry

/-- Ordinary coefficient maps have compatible resolution lifts and commute with
continuity. The map g is fixed on every actual colimit coprojection.
Source: Stacks 013P, 013S, 09YP
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof: resolve a single coefficient map in the system category, using the arrow
category to make its lifts compatible at every stage. Resolve the corresponding
colimit map in the same manner. On the original coefficient system the two legs
into the receiving resolution agree by the coprojection equation. Homotopy
uniqueness (013S) makes their difference null-homotopic on the resolved system.
Sections and filtered colimit preserve the homotopy equation. Localization gives
the required square. This applies to every compatible lift; hence all choices,
identities and composites give the same derived map. -/
theorem coefficient_naturality {S : Sites.{u}} (K L : System S)
    (C : K.Colimit) (D : L.Colimit) (h : K.Map L)
    (g : C.cocone.pt ⟶ D.cocone.pt)
    (hg : ∀ (i : S.Index) (n : ℤ),
      C.legAt i n ≫
        ((S.cocone.ι.app i).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).map (g.f n) =
        (h.map i).f n ≫ D.legAt i n)
    (b : ℤ)
    (hK : ∀ (i : S.Index) (n : ℤ), n < b → IsZero ((K.complex i).X n))
    (hL : ∀ (i : S.Index) (n : ℤ), n < b → IsZero ((L.complex i).X n))
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    (∃ (M : Model K C b) (N : Model L D b), Nonempty (h.Lift g M N)) ∧
    (∀ (M : Model K C b) (N : Model L D b) (v : h.Lift g M N), v.Commutes) := by
  sorry

/-- Changing compatible resolutions gives commuting squares and common refinements.
Source: Stacks 013P, 013S
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof: take a system-injective resolution dominating both augmentations, by lifting
along their monomorphic quasi-isomorphisms. Choose a receiving injective resolution
dominating the two receiving resolutions. The resulting stage and receiver maps
are quasi-isomorphisms by their augmentation equations. Their section complexes
compute the same derived sections, so the section maps and their exact filtered
colimit are quasi-isomorphisms. Homotopy uniqueness in the system category, followed
by sections and colimit, proves both continuity squares. Thus both source and target
identifications transport the same arrow, proving independence of choices. -/
theorem common_refinement {S : Sites.{u}} {K : System S} {C : K.Colimit} {b c : ℤ}
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (M : Model K C b) (N : Model K C c) :
    ∃ (P : Model K C (min b c)) (v : M.Refinement P) (z : N.Refinement P),
      v.Commutes ∧ z.Commutes ∧
      IsIso (DerivedCategory.Q.map (colim.map v.sections)) ∧
      IsIso (DerivedCategory.Q.map (colim.map z.sections)) ∧
      IsIso (DerivedCategory.Q.map ((S.limitSections).map v.receiver)) ∧
      IsIso (DerivedCategory.Q.map ((S.limitSections).map z.receiver)) := by
  sorry

private theorem quasiIso_colim_map {I : Type u} [SmallCategory I] [IsFiltered I]
    {A B : I ⥤ CochainComplex AddCommGrpCat.{u} ℤ} (f : A ⟶ B)
    (hf : ∀ i : I, QuasiIso (f.app i)) : QuasiIso (colim.map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) n
  have (i : I) : IsIso ((Functor.whiskerRight f H).app i) := by
    let := hf i
    exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap (f.app i) n))
  have : IsIso (Functor.whiskerRight f H) := NatIso.isIso_of_isIso_app _
  have heq : colimit.post A H ≫ H.map (colim.map f) =
      colim.map (Functor.whiskerRight f H) ≫ colimit.post B H :=
    colimit.map_post f H
  have : IsIso (colimit.post A H ≫ H.map (colim.map f)) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimit.post A H) (H.map (colim.map f))

/-- The source identification for final reindexing is the actual colimit.pre map.
For literal restriction the stage maps are identities; changing resolutions replaces
these by quasi-isomorphisms, which the statement also allows.
Source: Stacks, Categories, final-functor colimit theorem; exact filtered colimits
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof: exact filtered colimit preserves the objectwise quasi-isomorphism v.sections.
The final-functor theorem makes colimit.pre invertible, with its prescribed legs.
Their composite is v.sourceMap, so its localization is invertible. The naturality
square above therefore supplies exactly the reindexing compatibility. -/
theorem cofinal_reindexing {S T : Sites.{u}} {U : SiteChange S T}
    {K : System S} {C : K.Colimit} {L : System T} {D : L.Colimit}
    {h : Change U K C L D} {b c : ℤ} {M : Model K C b} {N : Model L D c}
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] [U.index.Final] (v : h.Lift M N)
    (hv : ∀ i : S.Index, QuasiIso (v.sections.app i)) :
    IsIso (DerivedCategory.Q.map v.sourceMap) ∧ v.Commutes := by
  have : QuasiIso (colim.map v.sections) := quasiIso_colim_map v.sections hv
  have : IsIso (DerivedCategory.Q.map (colim.map v.sections)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  constructor
  · dsimp only [Change.Lift.sourceMap]
    rw [Functor.map_comp]
    infer_instance
  · exact naturality v

/-- Every canonical upper truncation has the same continuity construction, compatible
with its inclusion into the original complex and with all inclusions r to s.
Source: Stacks, Homology, canonical truncations; Derived Categories 015E
(blueprint: lem-per-finite-cover-derived-sections-continuity).

Proof: exact inverse image and filtered colimit preserve the kernels defining good
upper truncations, hence identify their actual coefficient colimits with the upper
truncation of the original colimit. The canonical inclusions and their unique
factorizations define the tower. Resolve the whole countable diagram of these
systems, its original object, and all its inclusions at once, with common bound b.
For r below b the truncation is zero. The lift and homotopy uniqueness arguments
013P and 013S give each square after applying sections and filtered colimit, exactly
as for coefficient naturality. Apply continuity to every resolution model. -/
theorem truncation_compatibility (S : Sites.{u}) (K : System S) (C : K.Colimit)
    (b : ℤ) (hbelow : ∀ (i : S.Index) (n : ℤ), n < b → IsZero ((K.complex i).X n))
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    ∃ (V : Truncations K C) (M : V.Models b),
      IsIso (DerivedCategory.Q.map M.original.comparison) ∧
      (∀ r : ℤ, IsIso (DerivedCategory.Q.map (M.truncation r).comparison)) ∧
      (∀ r : ℤ, (M.inclusion r).Commutes) ∧
      (∀ (r s : ℤ) (hrs : r ≤ s), (M.transition r s hrs).Commutes) := by
  sorry

end CategoryTheory.FiniteCoverDerivedSections
