## Worker report

The module `Sheaf.Algebra.Homology.LocalDerivedTensorNonvanishing` states
`DerivedCategory.local_derivedTensor_boundedAbove_finite_nonvanishing`, with proof
`sorry`. No definition is introduced, no existing statement is changed, and the node
copy changes only `lean`.

The statement was checked against the whole node. The correspondence is:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` |
| Noetherian | `[IsNoetherianRing R]` |
| Local, with its unique maximal ideal m | `[IsLocalRing R]`; m is its determined maximal ideal, and is not separately used in the assertion |
| Ordinary module derived category D(R) | `[HasDerivedCategory.{w} (ModuleCat.{u} R)]` and `U V : DerivedCategory (ModuleCat.{u} R)` |
| Cohomology of U bounded above | `hU : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj U)` |
| Cohomology of V bounded above | The corresponding `hV`, with independently quantified bound b |
| Every cohomology module of U finite | `hUfg : ∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj U)` |
| Every cohomology module of V finite | The corresponding `hVfg` |
| Derived tensor, with signed direct-sum total computation | `U ⊗ V`, the upstream K-flat derived monoidal tensor, not ordinary tensor of arbitrary representatives |
| Tensor has cohomology bounded above | First conclusion: `∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj (U ⊗ V))` |
| Tensor has finite cohomology in every degree | Second conclusion: `∀ i : ℤ, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj (U ⊗ V))` |
| Tensor zero iff either factor zero | Third conclusion: `IsZero (U ⊗ V) ↔ IsZero U ∨ IsZero V` |
| No finite Tor-dimension assumption | There is no Tor-amplitude, perfectness, lower-bound, flatness, or projectivity hypothesis on U or V |

`IsZero` is categorical vanishing, the meaning of '=0' for an object of D(R).
The ring and its ordinary module category use the common ambient universe u, as in
the upstream module-derived tensor interface; the localization's morphism universe w
is independent. Both universes are explicitly bound. Bounds are arbitrary integers,
not natural numbers. No representative or resolution is supplied as an extra hypothesis.

Dependency declarations read in full and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the recorded declaration
  of `def-weil-pbc-noetherian-ring` (Noetherian/Defs.lean, lines 192–199).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, the recorded declarations of `def-weil-abstract-derived-category`.
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` supplies
  `DerivedCategory.homologyFunctor` and its factorization through Q.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, the recorded declaration
  of `def-weil-finitely-generated-module` (Finiteness/Defs.lean, lines 115–120).

The tensor is obtained from the existing upstream
`DerivedCategory.hasDerivedMonoidalCategory` in
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, using
`ModuleCat.hasFunctorialFlatResolution` from
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`.
Their signatures and docstrings were read. This tensor is the left derived tensor
bifunctor on the localization of the homotopy category at quasi-isomorphisms.
The existing `DerivedCategory.QObjTensorQObjIsoOfKFlatLeft` in
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` was also read; it identifies
`Q.obj P ⊗ Q.obj L` with `Q.obj (P ⊗ L)` whenever P is K-flat, exactly the ordinary-module
signed direct-sum total tensor requested by the node. Thus no new tensor definition
or missing-notion node is needed.

All four currently stated proof dependencies are imported without `public`:
`Sheaf.RingTheory.RingPseudoCoherent` (`DerivedCategory.IsPseudoCoherent`),
`Sheaf.Algebra.Homology.BoundedFlatKFlat`
(`CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`),
`Sheaf.RingTheory.ProjectiveOverLocalFree`
(`Module.free_of_projective_of_isLocalRing`), and
`Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`
(`DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`).
The other three proof dependencies, `lem-trf-local-finite-module-tensor-nonzero`,
`lem-trf-local-top-degree-tensor`, and `lem-trf-pseudocoherent-tensor-closure`, have no
recorded Lean declarations in the inspected DAG; there is no module to import for them.
They are proof prerequisites only and are not required to type this statement.

Source check: read `literature/stacks-project/more-algebra.tex`,
`lemma-tensor-pseudo-coherent` (Tag 0DJE, lines 16487–16514) and
`lemma-Noetherian-pseudo-coherent` (Tag 066E, lines 16517–16548).
The first supplies pseudo-coherent tensor closure; the second identifies this with
bounded-above finite cohomology over a Noetherian ring. The local nonvanishing claim is
explicitly an agent corollary in the node, rather than attributed to Tag 0DJE itself.

A complete natural-language proof, also carried step by step in the Lean docstring:
The zero-factor implication follows from additivity of derived tensor. For closure,
apply the Noetherian cohomology criterion to U and V, apply pseudo-coherent tensor
closure, then apply the criterion to the tensor. If U and V are nonzero, their nonzero
cohomology degrees form nonempty subsets of the integers bounded above, so have
maxima a and b. Take bounded-above finite-free representatives. Cancel their terms
above a and b: if the top cohomology is zero, the incoming differential surjects onto
the top finite-free term and splits. Its kernel is a finite projective module and
therefore finite free over the local ring. Removing the split contractible two-term
summand lowers the top degree; only finitely many cancellations are needed before a
or b. The resulting complexes P,Q remain bounded above and finite free. They are
K-flat, so their signed direct-sum total tensor computes the derived tensor. In total
degree a+b the sole surviving term is P^a tensor Q^b; boundaries are the sum of the
images of dP tensor 1 and 1 tensor dQ, with the sign having no effect on that image.
Right exactness of tensor gives H^(a+b) = H^a(U) tensor H^b(V). These modules are
nonzero finite modules. Their reductions modulo the maximal ideal are nonzero by
Nakayama, and their tensor over the residue field is nonzero. Reduction of their
R-tensor is this nonzero residue-field tensor; therefore the R-tensor is nonzero.
Consequently the derived tensor is nonzero. This proves the reverse zero implication.

Edge cases checked: either or both objects zero; arbitrary integer shifts; complexes
unbounded below; no perfectness or finite projective dimension (for example the
residue field over a singular Noetherian local ring is allowed); independent upper
bounds a,b; fields as local rings. The zero ring is excluded exactly because the node
requires a unique maximal ideal, as does `IsLocalRing`, not by an added hypothesis.
The locality hypothesis matters: over Z the distinct torsion modules Z/2 and Z/3 give
zero derived tensor. Finite generation matters: over Z_(p), Q and its residue field
are nonzero with zero derived tensor, but Q is not finite. No statement dispute found.

Searches for an existing declaration (prescribed `msearch.py`, group NF, this item):

- LeanFinder: `Nonvanishing of derived tensor products of bounded above finite cohomology complexes over a noetherian local ring`.
  Eight hits, including ordinary-module support and Tor/projective vanishing; none is
  this derived nonvanishing plus closure theorem.
- Loogle: `DerivedCategory, ModuleCat, TensorProduct`. Zero hits.
- Mathlib grep: `derivedTensor|DerivedTensor` in `Algebra/Homology`. Zero hits.
- LeanSearch: `The derived tensor of nonzero bounded above complexes with finitely generated cohomology over a noetherian local ring is nonzero`.
  Eight hits, including `IsLocalRing.subsingleton_tensorProduct` (only one finite
  module against the residue field) and generic derived-category lemmas; no match.
- `rg` in the source `WeilConjectures` and side `lean/Sheaf` for derived tensor,
  finite cohomology, pseudo-coherence, and local tensor nonvanishing found the existing
  constructions and cohomology criterion described above, but no theorem matching
  the item. `grep -rn` for the item id in upstream `WeilConjectures` returned no hits.
- `rg` of `dag/lean_names_upstream.json`, the side library, and upstream for
  `local_derivedTensor_boundedAbove_finite_nonvanishing`, `tensor.*[Nn]onvanish`,
  `[Nn]onvanish.*tensor`, `tensor_isZero_iff`, and `isZero_tensor_iff` found no matching
  theorem/name collision; other nonvanishing hits concern geometric section pullback.

Compilation: the prescribed `scompile.py NF lem-trf-local-derived-tensor-nonvanishing`
compiled the delivered module cleanly both as the sandbox and as its library module
(2.1 s and 2.5 s respectively). No errors or non-sorry warnings were printed.

## Second reading by NF

A separate verification pass reopened the node and final module and matched each row
of the hypothesis/conclusion table above. The statement retains both parts of closure,
not just the nonvanishing equivalence; hU and hV bound cohomology rather than terms;
hUfg and hVfg apply in every integer degree. `IsZero U ∨ IsZero V` includes either zero
factor and does not assume either is nonzero. The tensor uses the upstream derived
monoidal instance with functorial flat resolutions, so it is not an arbitrary supplied
bifunctor or ordinary tensor of representatives. All variables and universes are bound.
There are no new nodes, dependency replacements, additional hypotheses, or changed
node fields other than `lean`. No mismatch was found and no correction was needed.
This is an in-session second pass; the maintainer provides the independent review
specified by the dispatch brief.
