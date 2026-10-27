## Worker report

`Sheaf.AlgebraicGeometry.SchlessingerAutomorphismKernel` states
`AlgebraicGeometry.ArtinDeformation.schlessinger_automorphism_kernel` with proof
`sorry`. Its six helper definitions have real data. The mathematical statement and
all helper bodies retain the versions the independent reader approved. This repair
reuses the original `squareZeroMap` in `ArtinRSTangentTensor` and records that helper
under a new definition node with `existing: true`. Only one Lean module is delivered.

Each hypothesis and clause of the item is rendered as follows:

* The field is `{k : Type u} [Field k]`; Art_k is `TestCategory k k`.
* `D : CofibredGroupoids.{u, v, w} k k` is the recorded groupoid-valued pseudofunctor.
  `hpre : IsPredeformation D` and `hrs : IsRimSchlessinger D` are exactly the two
  category hypotheses, with independent fibre object and morphism universes.
* `x₀ : fibre D (residueTest (R := k) (k := k))` is the chosen residue object.
  `testFieldInclusion` constructs the actual coefficient-field map using
  `Algebra.ofId`, with its augmentation equality. `testBasePoint` pushes x₀ along it.
* `infinitesimalAut D x₀` is literally `Aut (testBasePoint D x₀ (squareZeroTest k))`,
  namely V = Aut(x_ε). Terminality of D(k) makes these precisely the automorphisms
  reducing to identity; no additional kernel condition is necessary here.
* Existential `AddCommGroup` and `Module k` structures are on this exact V carrier.
  `∀ f g, f + g = f * g` identifies addition with automorphism composition.
* `∀ a f, a • f = infinitesimalAutScalar D x₀ a f` pins scalar multiplication to
  ε ↦ aε. The right side uses the existing `squareZeroMap (a • LinearMap.id)` and
  the actual `push.mapAut`. `testBasePointComparison` identifies its base point by
  the pseudofunctor's `compIso` and equality of coefficient maps, then Mathlib's
  `Aut.autMulEquivOfIso` conjugates. No arbitrary fibre isomorphism is chosen.
* `∀ (A' A : TestCategory k k) (p : A' ⟶ A)` quantifies over the original marked
  local algebras and residue-preserving local arrows. `Function.Surjective (map p)`
  gives the surjection hypothesis. The next binder
  `∀ a ∈ IsLocalRing.maximalIdeal (ring A'), ∀ i ∈ RingHom.ker ..., a * i = 0`
  gives exactly maximal-ideal annihilation, without a nonzero or dimension restriction.
* `x' : fibre D A'` is arbitrary. `(push D p).obj x'` is exactly x = p_*x'.
  `automorphismReductionKernel D p x'` is `((push D p).mapAut x').ker`, the actual
  kernel of the actual reduction homomorphism between these automorphism groups.
* `TensorProduct k (infinitesimalAut D x₀) (RingHom.ker (map p).toRingHom)` is V ⊗ₖ I.
  The ideal inherits its actual additive and restricted k-module structures from A'.
* The conclusion gives an action function `act` on this tensor and this kernel,
  with `act 0 h = h`, `act (t+s) h = act t (act s h)`, and
  `∀ h h', ∃! t, act t h = h'`. These are the additive action laws, freeness and
  transitivity. The kernel already contains identity, so the conclusion is nonvacuous.

Recorded dependencies used: `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`
provides `TestCategory`, `ring`, `map`, `residueTest`, `CofibredGroupoids`, `fibre`,
`push`, `compIso`, `IsPredeformation`, `IsRimSchlessinger`, and `squareZeroTest`.
They are publicly reexported by `Sheaf.AlgebraicGeometry.ArtinRSTangentTensor`, which
also supplies the existing `AlgebraicGeometry.ArtinDeformation.squareZeroMap`.
The latter is now recorded as the definition node `def-sfb-artin-square-zero-map`.
The item adds only this definition node to its original statement dependencies;
it does not add `lem-sfb-artin-rs-tangent-tensor` to them. The existing module is
publicly imported because its helper is used in a public definition, while its
theorem `artinRS_tangent_tensor` also serves the already-recorded proof dependency.
Mathlib's `Field`, `TensorProduct`, `Aut`, `Functor.mapAut`, `Aut.autMulEquivOfIso`,
and `MonoidHom.ker` give the field, tensor, automorphism, transport and kernel notions.

The other recorded proof dependencies are imported as before:
`Sheaf.CategoryTheory.ProductPreservingVectorFunctorLinearization`
(`CategoryTheory.productPreservingVectorFunctor_linearization`),
`Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra` (`artin_local_test_algebra`),
`Mathlib.RingTheory.HopkinsLevitzki` (Artinian implies Noetherian and nilpotence),
and `Mathlib.RingTheory.Noetherian.Defs` (`IsNoetherianRing`). The theorem docstring
retains the six-step natural-language proof from the node.

Source checked: Stacks formal-defos.tex, Tags 06JU, 06JV, 06JX and 06JY, especially
lines 5806--5872. Edge cases retained: I=0, V=0, infinite-dimensional V, kernels of
dimension greater than one, non-split extensions, characteristic two, and arbitrary
independent fibre universes. No statement dispute or mathematical correction.

Searches: LeanFinder for infinitesimal automorphisms/deformation groupoids returned
cotangent and smooth-algebra results, no abstract theorem. Loogle for Aut, mapAut,
AddTorsor reported no hits/unknown unqualified mapAut; direct Mathlib source gave
the exact mapAut declaration. Mathlib grep for infinitesimal/Schlessinger/mapAut
found mapAut and Galois uses. Project grep in both Lean roots and the upstream name
index found no theorem or helper-name collision among the six item-owned helpers.
The new node retains the full original LeanSearch, LeanFinder and grep outputs for
square-zero maps. LeanSearch and Mathlib grep found `TrivSqZeroExt.map`; project and
DAG grep located the exact bundled `squareZeroMap` in ArtinRSTangentTensor and that
theorem node's record. These searches establish an existing declaration to reuse,
rather than a reason to write another copy. The latest server source was read using
`scompile.py --source Sheaf.AlgebraicGeometry.ArtinRSTangentTensor` on this repair.

## Repair of returned delivery

The latest immutable returned head is `7d08a97fe948`. Its extracted module
ArtinSquareZeroMap was reported to collide with the declaration still owned by
ArtinRSTangentTensor. The requested repair is import and reuse, not rename.
I removed the extracted module, the modified copy of ArtinRSTangentTensor, and the
associated dependency-node edit from the sandbox delivery. The main module now
publicly imports the unchanged existing ArtinRSTangentTensor module directly.
The definition node `def-sfb-artin-square-zero-map` records
`AlgebraicGeometry.ArtinDeformation.squareZeroMap` in that existing module with
`existing: true`, `branch: sheaf-dag`, and no `file` field. Thus the delivered code
contains no definition, relocation or rename of squareZeroMap. This also retains
the earlier A2 repair: statement dependency ownership goes through the definition
node, without adding the tangent--tensor theorem node to stmt_deps.
The item metadata was rebased onto the current shared node, preserving its statement
and all fields except the permitted `lean` record and addition to `stmt_deps`.

## New nodes

`def-sfb-artin-square-zero-map` records the already-existing canonical marked arrow
k[f] : k[V] → k[W], (a,v) ↦ (a,f(v)), for finite-dimensional vector spaces and a
linear map f over the inherited Noetherian base R. Its existing declaration is
`AlgebraicGeometry.ArtinDeformation.squareZeroMap` in
`Sheaf.AlgebraicGeometry.ArtinRSTangentTensor`, line 35. The full signature and
source docstring were read both locally and from the live server. The definition
uses Mathlib's TrivSqZeroExt.map, restricts scalars along R → k, and bundles the map
with its residue compatibility into the actual TestCategory arrow. The new node's
statement matches each inherited binder and the formula of that exact definition.
It cites the existing test-category node and `def-sc-trivial-square-zero-extension`;
no existing definition node separately records the marked arrow. Stacks Tag 06IG,
the square-zero algebras preceding (S1)/(S2), and the functor preceding Tag 06IA are
the source. All search outputs remain in `mathlib_searches`, with verdicts updated
to record reuse. Edge cases f=0, V=0, W=0 and arbitrary characteristic are included.
No Lean module is delivered for this existing declaration.

## Second reading by Q32

Self-audit only, as the dispatcher forbids starting another agent; the maintainer
provides the independent reading. I reread the final item, definition-node record,
and live squareZeroMap source. The existing declaration has exactly the finite
parameter spaces, linear map and canonical residue-marked arrow of the new node.
The main theorem's signature and all six helper bodies are unchanged. Its actual
Aut carrier, composition/addition equality, rescaling formula, surjective arrow,
maximal-ideal annihilation, tensor ideal and precise reduction kernel still match
every item clause. Zero/add action laws and the unique transporter still express
exactly the stated torsor. There is no ArtinSquareZeroMap module in this delivery,
no local squareZeroMap declaration, and no dependency-module edit. The new node has
existing:true and no lean.file, pointing directly at the original module. Per-file
scompile and delivery preflight are run on this final version before pushing.
