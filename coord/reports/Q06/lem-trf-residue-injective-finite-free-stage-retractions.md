## Worker report

The module `Sheaf.RingTheory.ResidueInjectiveFiniteFreeStageRetractions` states
`IsLocalRing.exists_finite_free_stage_retractions_of_residue_injective`, with its whole
proof `sorry`. It defines no new notion. The node is unchanged except for `lean`.
There is no repair note for this item.

Source read: `literature/stacks-project/flat.tex`, Tag 05FQ,
`lemma-universally-injective-local`, especially the proof's factorization through `N_i`,
persistence of residue injectivity at all `i' ≥ i`, and splitting sentence. The assigned
node isolates precisely this argument, taking the finite free presentation as data.
The module docstring carries all four proof steps of the node, including the quotient to
residue-field comparison and transport back from localization at a unit.

Hypotheses and clauses, matched individually:

- The commutative local ring `(R, 𝔪)` is `{R : Type u} [CommRing R] [IsLocalRing R]`;
  its unique maximal ideal is Mathlib's `IsLocalRing.maximalIdeal R`.
- The small nonempty directed partially ordered set is `{I : Type v} [PartialOrder I]
  [Nonempty I] [IsDirected I (· ≤ ·)]`. No total order or finiteness of `I` is assumed.
- The system is `(F : I ⥤ ModuleCat.{v} R)`. Its module at `i` is `F.obj i`, and its
  transition `tᵢⱼ` is `(F.map (homOfLE hij)).hom`. `Functor.map_id` and `map_comp`,
  together with the preorder-category identity and composition laws, are precisely
  `tᵢᵢ = 1` and `tⱼₖ tᵢⱼ = tᵢₖ`.
- Each stage is finite free by `[∀ i : I, Module.Finite R (F.obj i)]` and
  `[∀ i : I, Module.Free R (F.obj i)]`. These mean finite generation and existence
  of a basis, respectively; neither finite cardinality nor a chosen coordinate system
  is imposed.
- The module `N` and compatible maps `qᵢ` are the point `c.pt` and the linear maps
  `(c.ι.app i).hom` of `(c : Cocone F)`. Naturality of `c.ι` supplies all the cocone
  identities. `(hc : IsColimit c)` asserts the universal property for this given
  cocone, without identifying `N` with an arbitrarily chosen colimit.
- The finite free source is `(P : Type w) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Free R P]`.
- The given map is `(v : P →ₗ[R] c.pt)`.
- The exact quotient hypothesis is
  `(hv : Function.Injective (v.reduceModIdeal (maximalIdeal R)))`.
  `LinearMap.reduceModIdeal` has source `P ⧸ (𝔪 • ⊤)` and target
  `c.pt ⧸ (𝔪 • ⊤)`, and sends the class of `x` to the class of `v x`.
  Thus this is the node's quotient map itself, with no extra tensor hypothesis.
- The first existential is `∃ (i : I) (vᵢ : P →ₗ[R] F.obj i)`.
- The factorization is `(c.ι.app i).hom.comp vᵢ = v`.
- For each later stage the conclusion is `∀ (j : I) (hij : i ≤ j),
  ∃ sⱼ : F.obj j →ₗ[R] P, sⱼ.comp ((F.map (homOfLE hij)).hom.comp vᵢ) = LinearMap.id`.
  The existential is inside the universal quantifier, so no compatibility among the
  `sⱼ` is asserted. It includes `j = i`.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic` (class and docstring read). Finiteness uses
  `Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs` (class and docstring read).
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and `IsColimit`,
  exposed through its recorded module `Mathlib.CategoryTheory.Limits.HasLimits`.
  Their full structures and docstrings were read in `Cones.lean` and `IsLimit.lean`,
  as was the generated chosen-colimit interface in `HasLimits.lean`.
- Proof-only: `Concrete.isColimit_exists_rep` and `Concrete.isColimit_rep_eq_iff_exists`
  from `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
  `ModuleCat.FilteredColimits.forget_preservesFilteredColimits` from
  `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`.
- `lem-weil-pbc-local-ring-unit-criterion`: `IsLocalRing.notMem_maximalIdeal`,
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`; this module is also a public
  statement import for the maximal ideal.
- `lem-pc-finite-free-map-residue-localization-strong`:
  `Module.finiteFreeMap_residue_localization_strong`, imported privately from its
  recorded upstream module `WeilConjectures.RingTheory.FiniteFreeMapResidueLocalizationStrong`.
  Its full signature and source/proof docstring were read. No retired Sheaf twin is imported.
- The canonical quotient construction `LinearMap.reduceModIdeal` and its formula
  `reduceModIdeal_apply` were read in `Mathlib.RingTheory.AdicCompletion.Functoriality`;
  this existing definition is used directly.

Edge cases checked before writing: `P = 0` is allowed (empty basis); nonemptiness of
`I` then supplies a stage and all retraction equations are valid. Zero finite free
stages are allowed. Over a field the maximal ideal is zero, so the hypothesis is
ordinary injectivity, as expected. `N = 0` forces `P = 0` by finite generation and
Nakayama, consistent with the conclusion. No transition map is required to be
injective. No flatness assumption is added on `N`: a filtered colimit of free
modules is already flat. No rank, characteristic, Noetherianity, or positivity
assumption is imposed. The index and stage/colimit module carriers share universe
`v`, as required by the project's colimit size convention; the ring and source use
explicit independent universes `u` and `w`. No implicit universe or variable is bound
automatically.

Searches performed with the prescribed `msearch.py Q06 <item>` wrapper:

- LeanFinder: "A finite free module map to a directed colimit of finite free modules
  over a local ring injective modulo the maximal ideal factors through a stage and
  splits at every later stage". Eight hits, including
  `IsLocalRing.split_injective_iff_lTensor_residueField_injective`,
  `Module.free_of_lTensor_residueField_injective`, and
  `Module.FinitePresentation.exists_notMem_bijective`. None states the common-stage
  factorization with retractions at every later stage.
- Loogle: `Module.Free, IsLocalRing`. Twelve hits; the local-ring splitting criterion
  applies to a single map into a finite free module and has no directed presentation
  or eventual-stage conclusion. Its full signature/docstring were read.
- Mathlib grep: `split_injective_iff_lTensor_residueField_injective|reduceModIdeal|mapQ`
  in `RingTheory/LocalRing`. Two hits, the overview and single-map splitting theorem.
- LeanSearch: "A finite free map into a directed colimit of finite free modules over
  a local ring injective modulo the maximal ideal factors through a stage with left
  inverses at all later stages". Eight hits, including `Module.DirectLimit.lift_injective`,
  `ModuleCat.directLimitIsColimit`, and the local-ring splitting criterion; no exact match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `residue.*stage|stage.*retraction|finite_free.*[Ll]ift|reduceModIdeal` found unrelated
  geometric/formal-completion declarations and existing uses of `reduceModIdeal`,
  but no theorem with this statement. The prescribed `grep -rn` of the node id in
  `lean/WeilConjectures` found no declaration.
- Exact proposed declaration-name search in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf` found no collision. Direct Mathlib search
  found the existing `LinearMap.reduceModIdeal`, so no quotient-map helper was added.

Validation: prescribed `scompile.py` compiled the delivered file in both sandbox
and library module modes, with no errors or warnings. All theorem proofs are `sorry`.
No new nodes, dependency repairs, statement corrections, or disputed statements.

## Second reading by Q06

Single-worker rereading of the node and finished file; the dispatcher explicitly
forbids starting another agent, and the maintainer supplies the independent review.
The rereading checked the actual functor, cocone and reduction-map interfaces against
each clause above: partial rather than total order; nonempty and directed separately;
finite generation and freeness separately at every stage and at `P`; the supplied
cocone's colimit property; injectivity of the actual quotient map; one common lift;
and all later retractions including the same stage. In particular `hc` is a hypothesis
on the given `c`, and the factorization refers to that cocone's maps. The nested
quantifiers do not choose mutually compatible splittings. No mismatch was found and
no node statement or dependency was changed. All bound variables and universes are
explicit, and the delivered file contains no diagnostic commands or local notation.
