module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Category.TopCat.Limits.Konig
import Sheaf.Topology.Spectral.ConstructibleTopologyHausdorff
import Sheaf.Topology.SpectralMapConstructibleContinuous

/-!
# Compatible points in constructibly closed subsets of spectral spaces

Source: literature/stacks-project/topology.tex, Topology, Lemma Tag 0A2W
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-nonempty)
-/

@[expose] public section

universe u

open Set Topology

/--
Source: literature/stacks-project/topology.tex, Topology, Lemma Tag 0A2W, part (1)
(blueprint: lem-weil-pbc-spectral-limit-constructible-closed-nonempty).
The proof constructs the constructible subspaces of the `Z k`, applies the
nonempty inverse-limit theorem for compact Hausdorff spaces, and reads the
resulting compatible family as points of the original subsets.
-/
theorem exists_compatible_point_of_spectral_constructible_closed
    {K : Type u} [Preorder K] [Nonempty K]
    [IsDirected K (fun k k' => k ≤ k')]
    (Y : K → Type u) [∀ k, TopologicalSpace (Y k)]
    [∀ k, SpectralSpace (Y k)]
    (g : ∀ k k', k ≤ k' → Y k' → Y k)
    (hg : ∀ k k' (h : k ≤ k'), IsSpectralMap (g k k' h))
    (hgid : ∀ k, g k k (le_rfl) = id)
    (hcomp : ∀ k k' k'' (h : k ≤ k') (h' : k' ≤ k''),
      (g k k' h) ∘ (g k' k'' h') = g k k'' (le_trans h h'))
    (Z : ∀ k, Set (Y k))
    (hZne : ∀ k, (Z k).Nonempty)
    (hZclosed : ∀ k, @IsClosed (Y k) (constructibleTopology (Y k)) (Z k))
    (hZmap : ∀ k k' (h : k ≤ k'), Set.MapsTo (g k k' h) (Z k') (Z k)) :
    ∃ z : ∀ k, Y k, (∀ k, z k ∈ Z k) ∧
      ∀ k k' (h : k ≤ k'), g k k' h (z k') = z k := by
  classical
  have hcompact (k : K) : @CompactSpace (Y k) (constructibleTopology (Y k)) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology (Y k)) (Y k) _
      (constructibleTopology (Y k)) WithTopology.ofTopology
      (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _)
  have ht2 := fun k ↦ t2Space_constructibleTopology (Y k)
  have hcontinuous := fun k k' h ↦ (hg k k' h).continuous_constructibleTopology
  let : ∀ k, TopologicalSpace (Y k) := fun k ↦ constructibleTopology (Y k)
  let : ∀ k, CompactSpace (Y k) := hcompact
  let : ∀ k, T2Space (Y k) := ht2
  let (k : K) : CompactSpace (Z k) := isCompact_iff_compactSpace.mp (hZclosed k).isCompact
  let (k : K) : Nonempty (Z k) := (hZne k).to_subtype
  let F : CategoryTheory.Functor Kᵒᵖ TopCat.{u} :=
    { obj := fun k ↦ TopCat.of (Z k.unop)
      map := fun {k k'} f ↦ TopCat.ofHom
        { toFun := fun z ↦
            ⟨g k'.unop k.unop (CategoryTheory.leOfHom f.unop) z.val,
              hZmap _ _ _ z.property⟩
          continuous_toFun :=
            ((hcontinuous _ _ _).comp continuous_subtype_val).subtype_mk _ }
      map_id := by
        intro k
        ext z
        exact congrFun (hgid k.unop) z.val
      map_comp := by
        intro k k' k'' f f'
        ext z
        exact (congrFun
          (hcomp k''.unop k'.unop k.unop
            (CategoryTheory.leOfHom f'.unop) (CategoryTheory.leOfHom f.unop)) z.val).symm }
  obtain ⟨z⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system F
  refine ⟨fun k ↦ (z.val (Opposite.op k)).val, fun k ↦ (z.val (Opposite.op k)).property,
    ?_⟩
  intro k k' h
  exact congrArg Subtype.val (z.property (CategoryTheory.homOfLE h).op)
