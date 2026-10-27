## Worker report

The module `Sheaf.RingTheory.HenselianColimitStageRoot` states
`CommRingCat.exists_monic_simple_root_stage`. Its sole theorem has proof `sorry`.
The node is unchanged except for `lean`. No definition, new node, dependency repair,
or statement correction is required.

Source checked: `literature/stacks-project/algebra.tex`, Tag 04GI,
`lemma-colimit-henselian`, especially the paragraph beginning “Suppose that f … is
monic” through the stage solution. This is exactly the portion specified by the
node, not the stronger final permanence theorem.

Hypothesis and clause correspondence:

- The nonempty small directed poset is `{I : Type u} [PartialOrder I]
  [Nonempty I] [IsDirected I (· ≤ ·)]`. The index and rings share universe `u`,
  as required by the project's filtered-colimit convention.
- The direct system of commutative rings and its compatible transition maps is
  `F : I ⥤ CommRingCat.{u}`. Each ring is henselian local via
  `[∀ i : I, HenselianLocalRing (F.obj i)]`; this class extends `IsLocalRing`.
- The maximal ideals are Mathlib's `IsLocalRing.maximalIdeal`. The condition
  `u_ij⁻¹(m_j) = m_i` is exactly `hlocal`, using `Ideal.comap` and
  `(F.map (homOfLE hij)).hom`. Injectivity of ring transitions is not assumed.
- The specified ring colimit `(A, α)` is the arbitrary `c : Cocone F`, with
  `hc : IsColimit c`. Thus `A` is `c.pt`, and `α_i` is `(c.ι.app i).hom`.
  This does not specialize the node to the chosen colimit object.
- Locality of `A` is `[IsLocalRing c.pt]`. The equality `α_i⁻¹(m) = m_i`
  is `hlegs`, again exactly an equality of ideals under `comap`.
- The residue fields `k_i` and `k` are `ResidueField (F.obj i)` and
  `ResidueField c.pt`, defined in Mathlib as the quotients by their maximal
  ideals; `residue` is precisely the quotient ring homomorphism.
- `ρ` consists of ring homomorphisms between these residue fields, characterized
  on every residue representative by `hρ`. Because `residue` is surjective,
  `hρ` uniquely determines each map as `[x] ↦ [α_i(x)]`. This presentation
  does not allow an arbitrary residue map or add any freedom to the node.
- The assumption that `(k, ρ)` is a ring colimit of the induced residue diagram
  is `hrescolim`. It says every compatible family `β_i : k_i →+* B` to a
  commutative ring has a unique factoring `g : k →+* B`, with
  `g.comp (ρ i) = β i`. The compatibility premise is written on representatives:
  `β_j([u_ij(x)]) = β_i([x])`. Surjectivity of each `A_i → k_i` makes this
  equivalent to compatibility with the entire induced residue-field transition
  map. Locality ensures those induced maps exist. The cocone condition for `ρ`
  follows from `hρ` and the original cocone naturality. Thus this is exactly
  the universal property in `def-weil-pbc-category-colimit`, expanded inline,
  without inventing a residue-diagram definition or assuming extra structure.
  `B : CommRingCat.{u}` tests all objects of the stated ring category.
- The polynomial is `f : Polynomial c.pt`; monicity is `hf`; its degree `n`
  is `hdegree : f.natDegree = n`. Monic polynomials over the nonzero local
  ring are nonzero, so this equals the usual finite polynomial degree.
- The prescribed residue element is `a₀ : ResidueField c.pt`. Its root
  condition is `hroot : (f.map (residue c.pt)).eval a₀ = 0`; its simplicity
  condition is `hsimple : (f.derivative.map (residue c.pt)).eval a₀ ≠ 0`.
  The derivative is Mathlib's formal derivative, including reduction in every
  characteristic; there is no characteristic restriction.
- The existential witnesses are the stage `i`, polynomial `fᵢ`, residue root
  `a₀ᵢ`, and actual root `aᵢ`, in exactly the node's respective rings.
- Monicity and degree at the stage are `fᵢ.Monic ∧ fᵢ.natDegree = n`.
- The polynomial image is `fᵢ.map (c.ι.app i).hom = f`.
- The residue-root image is `ρ i a₀ᵢ = a₀`.
- The two stage simple-root conditions are
  `(fᵢ.map (residue (F.obj i))).eval a₀ᵢ = 0` and
  `(fᵢ.derivative.map (residue (F.obj i))).eval a₀ᵢ ≠ 0`.
- The actual root and prescribed residue are the final two conjuncts
  `fᵢ.eval aᵢ = 0` and `residue (F.obj i) aᵢ = a₀ᵢ`.

Dependency declarations read and used:

- `def-weil-pbc-henselian-terminology`: its recorded module
  `WeilConjectures.Mathlib.RingTheory.Henselian` is publicly imported;
  `HenselianLocalRing` is the relevant recorded declaration (Mathlib).
  The record expressly uses this class for the henselian local-ring clause.
  Its strict-henselian class is not imposed here.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and
  `CategoryTheory.Limits.IsColimit` from
  `Mathlib.CategoryTheory.Limits.HasLimits`, available through the public ring
  colimit import. The residue colimit is its universal property written out.
- Proof dependency `lemma-nagata-filtered-colimit-finite-data`:
  `Sheaf.RingTheory.FilteredColimitFiniteData`,
  `CommRingCat.exists_finite_data_stage`, privately imported.
- Proof dependency `lem-pc-filtered-colimit-commrings-elementwise`:
  `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`,
  `CategoryTheory.Limits.Concrete.isColimit_exists_rep` and
  `CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists`, with
  `Mathlib.Algebra.Category.Ring.FilteredColimits` for preservation by the
  forgetful functor. Both modules are privately imported.
- Proof dependency `lem-weil-pbc-henselian-local-root-lifting`:
  `WeilConjectures.RingTheory.HenselianLocalRootLifting`,
  `IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`, privately
  imported. The complete five-step node proof is reproduced in the theorem
  docstring, including coefficient descent, residue descent, locality-based
  zero reflection, and the final Hensel lift.

Edge cases checked mathematically before writing:

- `n = 0` is permitted by the signature, but its hypotheses are impossible:
  the monic polynomial is 1, which has no residue root. No positive-degree
  assumption was added.
- A singleton index set reduces to ordinary Hensel lifting. The empty index
  set is excluded exactly as in the node by `Nonempty I`.
- The zero ring cannot be local in Mathlib's convention; this matches the
  proper maximal ideal and residue field required by the node.
- Non-injective local transitions, such as a dual-number ring mapping onto
  its residue field, are permitted. Only residue maps reflect zero, via the
  exact contraction assumptions; no ring-map injectivity is used.
- In positive characteristic the formal derivative may vanish; `hsimple`
  excludes precisely such non-simple roots, without excluding that characteristic.
- The arbitrary cocone and its `IsColimit` witness include every specified
  colimit and every compatible family of colimit legs.

Searches for an existing statement:

- `msearch.py ... leansearch "simple residue root at a stage of a filtered
  colimit of henselian local rings"`: eight hits, including
  `HenselianLocalRing`, `.is_henselian`, `.TFAE`, and `IsLocalRing.residue`.
  They give ordinary root lifting or the residue construction, not simultaneous
  finite-stage descent in a ring and residue-field colimit.
- `msearch.py ... leanfinder "A monic polynomial and simple residue root over
  a directed colimit of henselian local rings descend and lift at one stage"`:
  eight hits, headed by `HenselianLocalRing.TFAE`, `.is_henselian`, and
  `HenselianRing.is_henselian`; no exact statement.
- `msearch.py ... loogle "HenselianLocalRing, DirectLimit"`: zero hits.
- `msearch.py ... grep
  "(henselian|simple.root|monic).*(colimit|DirectLimit|directLimit)|(colimit|DirectLimit|directLimit).*(henselian|simple.root)"
  RingTheory`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for residue-field maps,
  henselian colimits, and the node id: no existing declaration of this node.
  `FilteredColimitHenselianPair` states pair permanence;
  `FilteredColimitStrictlyHenselianLocal` states final strict-local permanence.
  Neither states this finite-stage witness theorem. The required node-id search
  in `lean/WeilConjectures` returned no hits.
- Focused searches in Mathlib's residue-field source found `ResidueField.map`,
  `map_comp`, `map_residue` and the quotient definitions. These confirm the
  interpretation of the canonical maps; no residue-diagram helper was needed.
- Exact-name searches for `exists_monic_simple_root_stage` and
  `HenselianColimitStageRoot` in the source ring-theory directories and
  `dag/lean_names_upstream.json` returned no pre-existing declaration.

No STATEMENT-DISPUTED issue or source discrepancy was found. The example
`Sheaf.CategoryTheory.CompactObject` is withdrawn in this snapshot; its node's
current upstream module was read for the public-module conventions instead.

Validation: `scompile.py N7 lem-sfb-henselian-colimit-stage-root` compiled the
module in sandbox and library modes successfully, with no errors or unexpected
warnings. No global build or direct repository mutation was performed.

## Second reading by N7

I reread the actual node and completed Lean file after compilation, as a separate
self-audit. Per the dispatcher's instruction I did not start another agent;
independent delivery review belongs to the maintainer.

The complete binder list preserves the directed poset, henselian stages, local
transition maps, specified ring-colimit cocone, local colimit ring, local cocone
legs, canonical residue maps, and residue colimit assumption. In particular,
`hrescolim` is a universal property, not merely surjectivity of the residue maps;
its compatibility on ring representatives is equivalent to compatibility on
residue classes. `hρ` constrains every residue element, because every such element
has a ring representative. These are presentations of the given objects and
hypotheses, rather than stronger assumptions.

Reading the conclusion in order gives monicity, degree n, polynomial image,
residue-root image, vanishing, nonvanishing derivative, an actual root, and its
specified residue. Each matches the corresponding node clause. No equation was
replaced by a weaker existence or by equality only after further transition.
The degree-zero and positive-characteristic cases remain included. There are no
new definitions, hidden let-binders, private notation, or auto-bound implicits.
No mismatch or change was found in this pass.
