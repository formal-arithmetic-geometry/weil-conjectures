## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveCoordinateKoszulSequence` states
`AlgebraicGeometry.ProjectiveSpace.exists_exact_coordinateKoszulSequence` with
one `sorry` proof. There are no definitions, auxiliary theorems, new nodes,
dependency repairs, or statement corrections. The accepted stage-1 statement and
proof plan are preserved. In particular, the inherited stage-1 rejection about
being already split under N5 does not apply: the current queue lists this item
at stage 2, and brief-stage2 section 0 explicitly authorizes this handoff.

Source read: `literature/stacks-project/perfect.tex`, Tag 0BQS,
`lemma-construct-the-next-one`, including its statement and proof. The node adds
the explicit exterior-multiplication convention for its coordinate maps; the
Lean formula preserves that convention. The latest blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read. This is a prerequisite under its direct-image proof, not the
unit's own statement.

Clause-by-clause correspondence:

- A commutative ring is `(A : Type u) [CommRing A]`. There is no nontriviality,
  domain, field, regularity, flatness, or Noetherian assumption.
- The dimension `n >= 0` is `(n : ℕ)`, and every integer twist is `(a : ℤ)`.
- The scheme is `ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))`, the shared projective
  space model over A. The coordinate type has precisely n+1 elements. The lift
  makes it live in the base ring's universe and does not change its cardinality.
  This follows the project convention in STATE, PROJECTIVE SPACE AND PROJ TWISTS,
  and the immediate consumer `ProjectiveNegativeTwistsGenerator.lean`. No new
  version of Proj or of the twisting sheaves is introduced.
- The ambient category is this scheme's `.Modules`. Its definition is
  `SheafOfModules.{u} X.ringCatSheaf`, exactly the scheme specialization of the
  recorded `CategoryTheory.ringedSiteModules`, with the inherited abelian
  structure. The dependency module is publicly imported.
- Existence of the exact complex is `∃ E : CochainComplex ... ℤ, ... E.Acyclic`.
  Mathlib defines `Acyclic` as `∀ i, E.ExactAt i`, so exactness includes all
  integer degrees, including the first and last nonzero terms.
- The terms and their summands are fixed by `e : ∀ i : ℤ, E.X i ≅ ∐ ...`.
  The coproduct index is `{I : Finset (ULift (Fin (n+1))) // (I.card : ℤ) = i}`;
  every summand is the recorded `twist ... (a+i)`. The number of i-element
  subsets is binomial(n+1,i), including one copy at i=0 and i=n+1. Thus this
  gives precisely the displayed ranks and twists. The coproduct index is empty
  for i<0 or i>n+1, so the exterior terms are zero objects. This also fixes zero
  incoming and outgoing differentials, not just exactness of an unaugmented
  sequence.
- Vector bundles are `(∀ i : ℤ, (E.X i).IsFiniteLocallyFree)`, using the
  existing module-sheaf local freeness predicate. The coproduct identifications
  additionally fix the stated constant ranks, including rank zero outside the
  range.
- Coordinate multiplication is the existing `ProjectiveSpace.twistMulX` at
  integer degree `a+i`. Its definition pulls back `Proj.twistMul` by the
  homogeneous polynomial X_j from the integral model. On the generator
  `twistGenerator ... d k`, it is exactly multiplication by x_j/x_k into the
  generator in degree d+1: multiplication sends x_k^d to
  x_j x_k^d = (x_j/x_k) x_k^(d+1). The recorded transition rule for the generators
  is `map_twistGenerator_eq_transitionUnit_smul`. This uses the actual existing
  coordinate maps, not an arbitrary family subject to an existence assumption.
- The last universally quantified equation prescribes the whole image of each
  summand I. Its left side includes I via `Sigma.ι`, transports into E via
  `(e i).inv`, applies `E.d i (i+1)`, and transports to the target direct sum via
  `(e (i+1)).hom`. Its right side sums over target subsets J and coordinates j.
  The condition `j ∉ I.val ∧ insert j I.val = J.val` selects exactly the target
  summand I union {j}; all other terms are zero. The sign is
  `(-1 : ℤ) ^ (I.val.filter (fun k ↦ k.down < j.down)).card`.
  Integer scalar multiplication of morphisms gives exactly the signed map.
  `eqToHom (congrArg (twist ...) (add_assoc a i 1))` only identifies
  (a+i)+1 with a+(i+1); it does not choose an isomorphism of twists. Coproduct
  inclusions determine a map from each summand, so this equality fixes every
  matrix entry of every differential. The complex structure includes square zero.

Dependency declarations and interfaces read and used:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
  `AlgebraicGeometry.ProjectiveSpace.twist` and its full docstring; this is the
  recorded primary declaration of def-pc-projective-space-twist.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor`,
  `ProjectiveSpace.twistGenerator`, and
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistGenerator`,
  `ProjectiveSpace.map_twistGenerator_eq_transitionUnit_smul`; these were read
  to verify that the existing coordinate multiplication implements the node's
  chart convention.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, a transparent abbreviation for Mathlib's
  `SheafOfModules`. The scheme category uses exactly the same sheaf category.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Koszul`,
  `ProjectiveSpace.twistMulX` (general coordinate map). The same file's
  `ProjectiveLine.koszul_shortExact` only treats two coordinates and therefore
  cannot serve as an existing attachment for this item.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits` supplies the actual
  coproducts, with Mathlib's `Sigma.ι` as their inclusions. The finite index
  subtype uses Mathlib's Finset and Fintype constructions.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
  `HomologicalComplex.Acyclic` and `ExactAt`; their definitions were read.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFree`, available through the twist imports;
  its class explicitly supplies finite locally free local-generator data.
- The recorded proof-dependency module
  `WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting` is
  imported without public visibility. Its
  `AlgebraicGeometry.RingedSpace.module_exactness_local_lifting` signature and
  docstring were read, including its third conjunct for exactness.
- def-pc-proj is a Mathlib leaf, recorded through `AlgebraicGeometry.Proj`,
  `AlgebraicGeometry.projIsoSpec`, and `ProjectiveSpectrum.basicOpen`; their
  source definitions were consulted. No duplicate Proj construction is needed.

Edge cases checked mathematically before writing:

- n=0 gives 0 -> O(a) --x_0--> O(a+1) -> 0; D_+(x_0) is the whole space and
  multiplication is invertible. Both singleton-subset signs are positive.
- n=1 gives the exterior-convention maps (x_0,x_1) and (-x_1,x_0), so their
  composite is zero. This is the same exact sequence as the existing projective
  line sequence after the appropriate signed permutation of its middle basis.
- For I={0,2}, adjoining j=1 has sign -1, as required by the ordered-subset rule.
- The empty subset and full subset give the two rank-one endpoints; degrees
  below zero and above n+1 have no subsets and thus zero terms.
- The zero ring gives the empty scheme and zero module sheaves; no excluded case.
- Characteristic two is allowed: signed pairs still cancel additively. All
  negative, zero and positive integer twists use the same existing twistMulX.
- The universe u is explicit and the coordinate lift works for every u.

Searches for an existing exact general sequence:

- msearch LeanFinder, query "Exact signed coordinate Koszul sequence of twists
  O(a+i) on projective n-space over any commutative ring": eight cotangent and
  projective-resolution exactness results, including
  Algebra.Generators.H1Cotangent.exact_δ_map,
  Algebra.H1Cotangent.exact_map_δ,
  Algebra.Generators.H1Cotangent.exact_map_δ',
  Algebra.Generators.H1Cotangent.exact_map_δ,
  CategoryTheory.ProjectiveResolution.exact_succ,
  Algebra.Extension.exact_cotangentComplex_toKaehler,
  Algebra.H1Cotangent.exact_δ_mapBaseChange, and
  Algebra.Generators.CotangentSpace.exact. None is this statement.
- msearch Loogle, query `"KoszulComplex", "exact"`: zero hits.
- msearch Mathlib grep, query `Koszul.*exact|exact.*Koszul|koszul.*twist`:
  zero hits.
- msearch LeanSearch, query "Exact signed Koszul complex of homogeneous
  coordinate line bundle maps on projective space": eight general exactness,
  projective-resolution and cotangent results. The useful general predicates
  `HomologicalComplex.ExactAt` and `Acyclic` were reused; none states this sequence.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `coordinateKoszul`, `coordinate_koszul`, and `koszul_shortExact`: the immediate
  consumer's docstring cites this item; the upstream projective-line sequence
  is the only existing coordinate exactness statement. Its scope is n=1.
  The general coordinate multiplication map exists and was reused.
- rg of Mathlib and `dag/lean_names_upstream.json` for the new declaration name:
  no collision.

No statement dispute or node fault was found. The old approved split is unchanged.
The docstring contains its complete four-step chart contraction proof, with its
named non-elementary dependency. The only postponed theorem matches this node.

Validation: scompile.py compiled the statement both at its sandbox name and at
its library module name, cleanly, within the default 60-second limit per file.
The delivery dry run and final push are performed through deliver2.py.

## Second reading by Q145

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
