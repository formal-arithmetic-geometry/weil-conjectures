module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.Paper.SiteCoveringIsomorphicFamily

@[expose] public section

universe u
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Definition 00VH (site axioms) and Definition 00VU
(isomorphic covering families), https://stacks.math.columbia.edu/tag/00VH and
https://stacks.math.columbia.edu/tag/00VU. This is the covering-reflection step of
lem-weil-pbc-etale-cohomology-invariance-under-site-equivalence, proof step 1.
(blueprint: cohomology-site-equivalence-covering-iff)

Proof: Fix an object W and presieve R. The forward implication is hcover W R.
For the reverse implication, suppose R.map e.functor covers e(W). Apply hcover_inv
at e(W) to this presieve: (R.map e.functor).map e.inverse covers e.inverse(e(W)).
Write R as Presieve.ofArrows Y f using Presieve.exists_eq_ofArrows; this represents
all its arrows with their domains, so no indexing or finiteness assumption is added.
Twice using Presieve.map_ofArrows identifies the last covering with the family
of arrows e.inverse.map (e.functor.map (f i)). Let eta = e.unitIso.hom. Its components
eta.app W and eta.app (Y i) are isomorphisms, and its naturality says
eta.app (Y i) followed by e.inverse.map (e.functor.map (f i)) equals
f i followed by eta.app W. Thus site_covering_isomorphic_family for J applies with
g i = e.inverse.map (e.functor.map (f i)), phi = eta.app W, sigma i = eta.app (Y i),
and the original f as the new family. Its final covering clause gives
Presieve.ofArrows Y f in J W, hence R in J W. The lemma uses the four site axioms
of J to transport the covering along these isomorphisms; the K axioms are retained
for the common site context. This proves both implications for every W and R. -/
theorem covering_iff_of_equivalence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange]
    [K.HasPullbacks] (e : C ≌ D)
    (hcover : ∀ (W : C) (R : Presieve W), R ∈ J W →
      R.map e.functor ∈ K (e.functor.obj W))
    (hcover_inv : ∀ (V : D) (R : Presieve V), R ∈ K V →
      R.map e.inverse ∈ J (e.inverse.obj V)) :
    ∀ (W : C) (R : Presieve W), R ∈ J W ↔
      R.map e.functor ∈ K (e.functor.obj W) := by
  intro W R
  refine ⟨hcover W R, ?_⟩
  intro hR
  have h := hcover_inv _ _ hR
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, Presieve.map_ofArrows] at h
  exact (site_covering_isomorphic_family J
    (fun i ↦ e.inverse.map (e.functor.map (f i))) h (e.unitIso.hom.app W)
    f (fun i ↦ e.unitIso.hom.app (Y i)) (fun i ↦ inferInstance)
    (fun i ↦ (e.unitIso.hom.naturality (f i)).symm)).2

end CategoryTheory
