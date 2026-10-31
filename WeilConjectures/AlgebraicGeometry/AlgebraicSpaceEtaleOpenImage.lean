/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.SpaceInvariantOpenQuotient
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Mathlib.AlgebraicGeometry.Limits

/-!
# Open images of representable étale morphisms of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03BX, 03BZ, 03IR, 03H4, 03H5, 03E4
(blueprint: lem-a1-space-etale-open-image).

The open subspace is an actual subfunctor, so pullback is its literal subfunctor preimage.
All image equalities refer to field-valued point classes. Surjectivity is tested on schemes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped Topology

namespace AlgebraicGeometry.AlgebraicSpace

private theorem pointImage_eq_range {S : Scheme.{u}}
    {E F : (Over S)ᵒᵖ ⥤ Type u} (f : E ⟶ F) :
    pointImage f = Set.range (mapPoint f) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Quot.mk _ a, rfl⟩
  · rintro ⟨a, rfl⟩
    induction a using Quot.inductionOn with
    | h a => exact ⟨a, rfl⟩

private theorem mapPoint_comp {S : Scheme.{u}} {E F G : (Over S)ᵒᵖ ⥤ Type u}
    (f : E ⟶ F) (g : F ⟶ G) : mapPoint (f ≫ g) = mapPoint g ∘ mapPoint f := by
  funext x
  induction x using Quot.inductionOn with
  | h x => rfl

private theorem pointImage_range {S : Scheme.{u}}
    {E F : (Over S)ᵒᵖ ⥤ Type u} (f : E ⟶ F) :
    pointImage (Subfunctor.range f).ι = pointImage f := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := a.value.property
    refine ⟨⟨a.K, a.base, b⟩, ?_⟩
    change Quot.mk _ (⟨a.K, a.base, f.app _ b⟩ : PointRepresentative F) =
      Quot.mk _ (⟨a.K, a.base, a.value.val⟩ : PointRepresentative F)
    rw [hb]
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.K, a.base, ⟨f.app _ a.value, ⟨a.value, rfl⟩⟩⟩, rfl⟩

/-- The topology is the quotient topology of any representable surjective étale scheme
atlas. Source: Stacks, Tag 03BX (blueprint: lem-a1-space-etale-open-image).
Proof: refine two atlases by their scheme fibre product using
lem-trf-space-fibre-products-etale-covers. Its projections are étale and surjective,
hence open quotient maps of schemes. The common-field point calculation (Tag 03H4)
identifies inverse images, so the two atlas quotient topologies agree. Every étale
scheme-source map is continuous for this topology by the same comparison, hence the
final topology for all such maps is exactly the topology of a single atlas. This is
step 2 of the node, using lem-a1-space-affine-etale-cover. -/
theorem points_atlas_isOpen_iff {S : Scheme.{u}} (F : AlgebraicSpace S)
    (T : Over S) (a : yoneda.obj T ⟶ F.obj.obj)
    (he : IsEtale a) (hs : IsSurjective a) (O : Set (Point F.obj.obj)) :
    IsOpen O ↔ IsOpen (schemePointMap a ⁻¹' O) := by
  obtain ⟨W, w, I, B, ι, hc, hB, hb, hr, hs', he', hsur, τ, hτ, hatlas, hcont⟩ :=
    exists_affine_etale_cover_and_point_topology F
  have hr' : IsRepresentable a := by
    intro V v
    obtain ⟨R, p, q, h, _⟩ := he V v
    exact ⟨R, p, q, h, trivial⟩
  change IsOpen[⨆ (V : Over S) (b : yoneda.obj V ⟶ F.obj.obj) (_ : IsEtale b),
    TopologicalSpace.coinduced (schemePointMap b) inferInstance] O ↔ _
  constructor
  · intro h
    exact isOpen_coinduced.mp
      (isOpen_iSup_iff.mp (isOpen_iSup_iff.mp (isOpen_iSup_iff.mp h T) a) he)
  · intro h
    refine isOpen_iSup_iff.mpr fun V ↦ isOpen_iSup_iff.mpr fun v ↦
      isOpen_iSup_iff.mpr fun _ ↦ isOpen_coinduced.mpr ?_
    have hO : IsOpen[τ] O := by
      rw [hatlas T a hr' hs he]
      exact isOpen_coinduced.mpr h
    exact (hcont V v).1.isOpen_preimage O hO

/-- Open subspaces correspond to open subsets, preserving and reflecting inclusion.
Source: Stacks, Tag 03BZ (blueprint: lem-a1-space-etale-open-image).
Proof (steps 1--5): the common-field calculation identifies point images under fibre
products (lem-trf-space-fibre-products-etale-covers). An open subspace pulls back along
an atlas to an open subscheme, and its points have the subspace topology by the quotient
criterion (lem-a1-space-affine-etale-cover). For an open subset `O`, pull it back to an
invariant open `V` of an atlas `U`. In the presentation `R = U ×_F U` of
lem-a1-etale-atlas-presentation, the opens `s⁻¹(V)` and `t⁻¹(V)` agree. Restrict the
relation to `V`; its projections remain étale by lem-weil-pbc-etale-scheme-base-change.
The quotient of this relation is an algebraic space by lem-trf-etale-relation-quotient,
and its map to `F` is an open immersion by lem-trf-etale-relation-finding-opens (open
immersions are étale by lem-weil-pbc-etale-composition-cancellation). Its point image
is `O`. Finally, inclusion of point subsets forces inclusion of subfunctors: on any
scheme test, the relevant open immersion has full point image and is an isomorphism.
This proves uniqueness and both directions of the order correspondence. -/
theorem openSubspace_points_orderIso {S : Scheme.{u}} (F : AlgebraicSpace S) :
    ∃ e : OpenSubspace F ≃o Opens (Point F.obj.obj),
      ∀ A : OpenSubspace F, (e A : Set (Point F.obj.obj)) = pointImage A.val.ι := by
  classical
  have hcal := point_open_calculus (S := S)
  let f : OpenSubspace F → Opens (Point F.obj.obj) := fun A ↦
    ⟨pointImage A.val.ι, by
      rw [pointImage_eq_range]
      exact (hcal.2.2.2.2.1 F A).1.isOpen_range⟩
  have hord (A B : OpenSubspace F) : f A ≤ f B ↔ A ≤ B :=
    hcal.2.2.2.2.2.1 F A B
  have hsur : Function.Surjective f := by
    intro O
    obtain ⟨U, p, hp, hs⟩ := F.property.2
    obtain ⟨R, t, s, hR, _⟩ := hp U p
    have hR' : IsPullback (yoneda.map t) (yoneda.map (yoneda.preimage s)) p p := by
      simpa only [yoneda.map_preimage] using hR.flip
    obtain ⟨V, i, hi, hiO, RV, r, sV, tV, hsV, htV, hm, heq, heS, heT,
      J, η, hη, hJ, he, hsur, j, hj, hjo, hjO, hji, A, hA⟩ :=
      space_invariant_open_quotient F U p hp hs O O.isOpen R t (yoneda.preimage s) hR'
    refine ⟨A, Opens.ext ?_⟩
    change pointImage A.val.ι = (O : Set (Point F.obj.obj))
    rw [hA, pointImage_range, hjO]
  let emb : OpenSubspace F ↪o Opens (Point F.obj.obj) :=
    { toFun := f
      inj' := fun A B h ↦ le_antisymm ((hord A B).1 h.le) ((hord B A).1 h.ge)
      map_rel_iff' := hord _ _ }
  exact ⟨OrderIso.ofSurjective emb hsur, fun _ ↦ rfl⟩

/-- The open point image of a representable étale map is an open subspace, with a
representable surjective étale factorization; its open image commutes with arbitrary
base change, and is quasi-compact when the source point space is quasi-compact.
Source: Stacks, Tags 03IR, 03H4, 03H5, 03E4
(blueprint: lem-a1-space-etale-open-image).
Proof (steps 6--9): compose `q` with an atlas of `E`. The composite is representable
étale by lem-weil-pbc-etale-composition-cancellation, and its open point image equals
that of `q` by the point-surjectivity of the atlas (lem-a1-space-affine-etale-cover).
The open-subspace correspondence constructs `A`. Its pullback to `E` is an open
subspace with full point image, hence is all of `E`; this gives the factorization.
Since `A → F` is monic, each scheme test of the factor is the corresponding scheme
test of `q`, so it is étale. Surjectivity follows by the common-field calculation
and scheme tests (Tags 03H4, 03H5). For arbitrary `g`,
lem-trf-space-fibre-products-etale-covers supplies the algebraic-space pullback;
its point image is the inverse image of the point image of `q`, as is the open
subfunctor preimage of `A`. Uniqueness of open subspaces proves the asserted identity.
Finally the continuous surjection from `|E|` to `|A|` sends a finite subcover of the
pulled-back open cover to a finite subcover, proving quasi-compactness. -/
theorem etale_open_image {S : Scheme.{u}} (E F : AlgebraicSpace S) (q : E ⟶ F)
    (hq : IsEtale q.hom.hom) :
    IsOpen (pointImage q.hom.hom) ∧
      ∃ A : OpenSubspace F,
        pointImage q.hom.hom = pointImage A.val.ι ∧
        (∃ qI : E.obj.obj ⟶ A.val.toFunctor,
          qI ≫ A.val.ι = q.hom.hom ∧ IsEtale qI ∧ IsSurjective qI) ∧
        (∀ (G : AlgebraicSpace S) (g : G ⟶ F),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
            (A.val.preimage g.hom.hom).ι ∧
          pointImage (Limits.pullback.snd q.hom g.hom).hom =
            pointImage (A.val.preimage g.hom.hom).ι) ∧
        (CompactSpace (Point E.obj.obj) → CompactSpace (Point A.val.toFunctor)) := by
  have hcal := point_open_calculus (S := S)
  have hopen : IsOpen (pointImage q.hom.hom) := by
    rw [pointImage_eq_range]
    exact (hcal.2.2.2.1 E F q hq).isOpen_range
  obtain ⟨e, he⟩ := openSubspace_points_orderIso F
  let A := e.symm ⟨pointImage q.hom.hom, hopen⟩
  have hA : pointImage q.hom.hom = pointImage A.val.ι := by
    rw [← he A]
    exact congrArg (fun O : Opens (Point F.obj.obj) ↦ (O : Set (Point F.obj.obj)))
      (e.apply_symm_apply ⟨pointImage q.hom.hom, hopen⟩).symm
  obtain ⟨_, qI, hqI, _, _, htests⟩ :=
    openSubspace_factor_schemeTests F E A q hA.subset
  obtain ⟨het, hsur⟩ := htests hq
  refine ⟨hopen, A, hA, ⟨qI, hqI, het, hsur hA⟩, ?_, ?_⟩
  · intro G g
    exact ⟨(openSubspace_preimage_schemeTests F G A g).1,
      openSubspace_pullback_image F E G A q g hA⟩
  · intro hE
    have hcomp : mapPoint A.val.ι ∘ mapPoint qI = mapPoint q.hom.hom := by
      rw [← mapPoint_comp, hqI]
    have hj := (hcal.2.2.2.2.1 F A).1
    have hcont : Continuous (mapPoint qI) := hj.isEmbedding.continuous_iff.2
      (hcomp.symm ▸ hcal.2.2.1 E F q)
    have honto : Function.Surjective (mapPoint qI) := by
      intro y
      have hy : mapPoint A.val.ι y ∈ pointImage q.hom.hom := by
        rw [hA, pointImage_eq_range]
        exact ⟨y, rfl⟩
      rw [pointImage_eq_range] at hy
      obtain ⟨x, hx⟩ := hy
      refine ⟨x, hj.injective ?_⟩
      exact (congrFun hcomp x).trans hx
    exact Function.Surjective.compactSpace hcont honto

/-- Topological quasi-compactness is equivalent to the existence of a quasi-compact
scheme atlas. Source: Stacks, Tag 03E4 (blueprint: lem-a1-space-etale-open-image).
Proof (steps 9--10): an atlas gives a continuous surjection on point spaces, so
quasi-compactness descends by pulling back open covers. Conversely refine an atlas to
a disjoint union of affine schemes using lem-a1-space-affine-etale-cover and
lem-weil-pbc-scheme-coproduct-family. The images of the affine components are open
and cover. Select finitely many by quasi-compactness; their union is quasi-compact by
lem-weil-pbc-affine-scheme-qcqs and is still an étale scheme-source map by
lem-weil-pbc-etale-composition-cancellation. It is point-surjective, hence surjective
on scheme tests by Tag 03H5. If the space is empty, take the empty finite union. -/
theorem points_compactSpace_iff {S : Scheme.{u}} (Z : AlgebraicSpace S) :
    CompactSpace (Point Z.obj.obj) ↔
      ∃ (U : Over S) (a : yoneda.obj U ⟶ Z.obj.obj),
        CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a := by
  constructor
  · intro hZ
    obtain ⟨U, p, I, B, ι, ⟨hc⟩, hB, hb, hr, hs, hp, hsur, htop⟩ :=
      exists_affine_etale_cover_and_point_topology Z
    let e : (∐ B) ≅ U.left := (colimit.isColimit _).coconePointUniqueUpToIso hc
    have he (i : I) : Sigma.ι B i ≫ e.hom = ι i :=
      (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
    have hi (i : I) : IsOpenImmersion (ι i) := by
      rw [← he i]
      infer_instance
    let V : I → U.left.Opens := fun i ↦ (ι i).opensRange
    have hV (i : I) : IsAffineOpen (V i) := by
      have := hB i
      exact isAffineOpen_opensRange (ι i)
    have hd : Pairwise (fun i j : I ↦ Disjoint (V i) (V j)) := by
      intro i j hij
      rw [← Opens.coe_disjoint]
      apply Set.disjoint_iff_forall_ne.2
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      have hxy' : Sigma.ι B i x = Sigma.ι B j y := by
        apply e.hom.homeomorph.injective
        change (Sigma.ι B i ≫ e.hom) x = (Sigma.ι B j ≫ e.hom) y
        simpa only [he] using hxy
      have hd' : Disjoint (Set.range (Sigma.ι B i)) (Set.range (Sigma.ι B j)) :=
        Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι B i j hij)
      exact (Set.disjoint_iff_forall_ne.1 hd') ⟨x, rfl⟩ ⟨y, rfl⟩ hxy'
    have hcover : (⨆ i : I, V i) = ⊤ := by
      apply Opens.ext
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, y, hy⟩ := (sigmaOpenCover B).exists_eq (e.inv x)
      have hix : ι i y = x := by
        rw [← he i]
        change e.hom (Sigma.ι B i y) = x
        change Sigma.ι B i y = e.inv x at hy
        rw [hy]
        exact Scheme.Hom.comp_apply e.inv e.hom x |>.symm.trans (by simp)
      exact Opens.mem_iSup.2 ⟨i, ⟨y, hix⟩⟩
    obtain ⟨D₀, W, hD₀, hW, hcomp, het, hsur'⟩ :=
      exists_finite_affine_subatlas Z hZ U p hp hs V hV hd hcover
    exact ⟨Over.mk (W.ι ≫ U.hom), _, hcomp, het, hsur'⟩
  · rintro ⟨U, p, hU, hp, hs⟩
    exact compactSpace_points_of_scheme_atlas Z U p hp hs hU

end AlgebraicGeometry.AlgebraicSpace
