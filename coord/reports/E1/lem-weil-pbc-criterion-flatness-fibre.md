## Worker report

The module `Sheaf.RingTheory.FlatOfFlatClosedFiber` states
`Module.flat_of_flat_closedFiber`, with its sole proof `sorry`. No definitions
are introduced. The item node changes only in `lean`.

Source checked: Stacks Project, Algebra, Tag 00R7,
https://stacks.math.columbia.edu/tag/00R7 (Lemma 10.128.8,
lemma-criterion-flatness-fibre). The local literature checkout is absent on this
machine, so the actual tag was opened and read online. Its five assumptions
and two conclusions agree with the node. The declaration docstring carries
all eleven proof steps of the node, including its corrections to the source's
last sentence: the final models are related by localization after base change.

Hypothesis and conclusion correspondence:

- The local commutative rings are `(R : Type u) (S : Type v) (S' : Type w)`
  with `CommRing` and `IsLocalRing` instances for all three. Distinct explicit
  universes impose no common-universe restriction.
- The two homomorphisms are `algebraMap R S` and `algebraMap S S'`.
  An algebra structure on commutative rings specifies exactly a ring map.
  Both have `IsLocalHom` instances, equivalent for local rings to carrying
  the maximal ideal into the maximal ideal. `IsScalarTower R S S'` says the
  `R`-algebra structure on `S'` is their composite.
- `M : Type t`, `AddCommGroup M`, and `Module S' M` give the module.
  `Module S M`, `Module R M`, `IsScalarTower S S' M`, and
  `IsScalarTower R S M` express precisely restriction of scalars. These
  compatibility conditions provide the stated actions, rather than independent
  additional restrictions on the original module.
- Assumption (1) is rendered by witness rings `P : Type p` and `Q : Type q`,
  their commutative-ring and `R`-algebra instances, and
  `Algebra.FinitePresentation R P` and `Algebra.FinitePresentation R Q`.
  The maps to `S` and `S'` and `IsScalarTower R P S` / `IsScalarTower R Q S'`
  ensure the localization maps respect exactly the original base actions.
  `W : Submonoid P`, `V : Submonoid Q`, `IsLocalization W S` and
  `IsLocalization V S'` say these are the required localizations. Mathlib's
  `IsLocalization` is the universal-property formulation of being isomorphic
  to the localization; it does not demand literal equality of ring types.
  The existential witnesses in the node are introduced as arbitrary parameters:
  the theorem works for every witness. Applying it after choosing witnesses is
  equivalent to assuming their existence, and yields the same conclusion.
  This follows the explicit-witness convention documented in
  `Mathlib.RingTheory.Smooth.Fiber`, immediately before
  `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`.
  All constituent notions already exist in Mathlib; no new definition is needed.
- Assumption (2) is `Module.FinitePresentation S' M`: finitely many generators
  with finitely generated kernel, equivalently the displayed finite-free cokernel.
- Assumption (3) is `Nontrivial M`, exactly that the additive module is not zero.
- For assumption (4), write `I = Ideal.map (algebraMap R S)
  (IsLocalRing.maximalIdeal R)`. This is `m_R S`. The binder `h_fibre` is
  `Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] M)`, using the canonical left-factor
  action of `S ⧸ I`. This tensor module is canonically `M / I M`, hence
  `M / m_R M`, with exactly the quotient-ring action in the node.
  See `TensorProduct.quotTensorEquivQuotSMul` in
  `Mathlib.LinearAlgebra.TensorProduct.Quotient`; on simple tensors it sends
  `s_bar ⊗ m` to the class of `s • m`. Its `S`-linear equivalence is also
  quotient-ring linear under these canonical actions.
- Assumption (5) is `Module.Flat R M` for the compatible restricted action.
- The two conclusions, in the node's order, are the conjunction
  `Module.Flat R S ∧ Module.Flat S M`.

Dependency declarations used and read:

- `def-weil-pbc-finitely-presented-algebra` is a Mathlib leaf with
  `mathlib_match` pointing to `Algebra.FinitePresentation`, imported from
  `Mathlib.RingTheory.FinitePresentation`; its signature, class field and
  docstring give the finite polynomial presentation with finitely generated kernel.
- `def-weil-pbc-flat-ring-map` records `RingHom.Flat` and `Module.Flat`, from
  `Mathlib.RingTheory.RingHom.Flat` / `Mathlib.RingTheory.Flat.Basic`.
  The latter is the flat-module notion used in all four flatness occurrences;
  the former is defined using precisely `Module.Flat` on the target with the
  action specified by the ring map. Their signatures and docstrings were read.

Edge cases checked before writing: `M = 0` is excluded exactly by the node's
nonzero hypothesis, needed for the conclusion about `S`. Zero rings are excluded
by the local-ring convention, consistently with the source. `R` a field gives
`m_R = 0`, so the fibre assumption is already flatness over `S`; `S` is then
flat over the field. Identity homomorphisms and trivial multiplicative subsets
are allowed. Finite-free presentations allow either rank to be zero. All
characteristics are allowed, and no Noetherian hypothesis has been added.
The witness rings and module each have their own explicitly bound universe.

Searches (actual remote-tool records are in `searches.jsonl`):

- `msearch.py leansearch`: "local rings R S S prime finite presentation module
  flat over R and closed fibre flat implies flat over S". Service returned
  Internal Server Error, recorded as unavailable; no search verdict claimed.
- `msearch.py leanfinder`: "critere de platitude par fibres local rings
  essentially finite presentation". Eight hits, including
  `RingHom.Flat.propertyIsLocal`, localization criteria and
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`; none states this fibre criterion.
- `msearch.py loogle`: `Module.Flat, IsLocalRing`. Eight hits, for local freeness,
  length base change and smoothness over the residue field; no match.
- `msearch.py grep`: `EssentiallyFinitePresentation|criterion.*flat|flat.*criterion`
  in `RingTheory`. Equational-flatness criteria only, no matching declaration.
- `rg` of the source `WeilConjectures` and `lean/Sheaf` for
  `EssentiallyFinitePresentation|criterion.*flat` and the item id found local
  flatness and smoothness criteria, but no statement of this node.
- `rg` for `flat_of_flat_closedFiber` in Mathlib, the source,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no collision.
- Mathlib's `Smooth/Fiber.lean` explicitly confirms there is no essentially
  finite presentation typeclass and uses the same localization witnesses.

No statement correction, disputed statement, missing dependency module, or new
node. The server compilation of the module succeeded cleanly in 1.6 seconds.

## Second reading by E1

I reread the node statement, Stacks Tag 00R7, and the complete Lean signature.
The objects and clauses match item by item:

- The three local rings are `R : Type u`, `S : Type v`, and `S' : Type w`,
  with `CommRing` and `IsLocalRing` instances.  The maps are the algebra maps
  `algebraMap R S` and `algebraMap S S'`, with `IsLocalHom` instances; the
  `Algebra R S'` and `IsScalarTower R S S'` instances identify the composite
  with the stated `R`-algebra structure.
- The `S'`-module `M : Type t` is rendered by `AddCommGroup M` and
  `Module S' M`; `Module S M`, `Module R M`, and the two scalar-tower
  instances express restriction of scalars exactly.
- Essential finite presentation of `S` and `S'` over `R` is rendered by the
  witnesses `P`, `Q`, their `R`-algebra structures, finite-presentation
  instances, multiplicative subsets `W`, `V`, localization instances
  `IsLocalization W S` and `IsLocalization V S'`, and the corresponding
  scalar towers.  No Noetherian or finiteness hypothesis is added.
- Finite presentation of `M` is `[Module.FinitePresentation S' M]`, and its
  nonzero condition is `[Nontrivial M]`.
- The closed-fibre condition is exactly the `Module.Flat` hypothesis on
  `(S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M`,
  the canonical tensor realization of `M / m_R M` over `S / m_R S`.
- `[Module.Flat R M]` is the fifth assumption, and the conclusion is the
  conjunction `Module.Flat R S ∧ Module.Flat S M`, in the node's order.

The source page confirms the same five assumptions and two conclusions.  Edge
cases are covered: arbitrary universes, zero/empty multiplicative subsets,
identity maps, field characteristic (where the maximal ideal may be zero),
and `n = 0` finite presentations.  `Nontrivial M` excludes the zero-module
case required by the source; local-ring instances impose no extra Noetherian
condition.

I searched Mathlib, the slopmaster2 source, project `lean/Sheaf`, and the DAG
name index with LeanSearch, LeanFinder/Loogle, and `rg` for the item and for
local flatness-fibre criteria.  No existing declaration states this result;
the dependency declarations `Algebra.FinitePresentation` and `Module.Flat`
are the exact notions required.  The worker module already compiles cleanly,
has no hollow definitions, and its statement docstring carries the source and
all proof steps.  I found no mismatch and made no changes.
