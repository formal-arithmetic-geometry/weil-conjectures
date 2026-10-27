## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceTensorInverseLine` states
`AlgebraicGeometry.AlgebraicSpace.isLineModule_of_tensor_inverse`, with its proof
left as `sorry`. It creates no definitions, proves no theorem, and leaves the
natural-language statement unchanged.

Clause-by-clause correspondence:

- The base scheme is the explicit implicit binder `{S : Scheme.{u}}`.
- The algebraic space over that base is `(X : AlgebraicSpace S)`. This is the
  recorded fppf-sheaf algebraic-space definition, with its representable diagonal
  and representable surjective etale atlas; these are inherent in the type.
- The small etale site is `X.EtaleSite` with `X.etaleTopology`. Its structure
  sheaf is the existing `X.structureSheaf`, whose sections are the regular
  functions on its scheme objects. `X.commStructureSheaf` retains exactly those
  same sections and restrictions as commutative rings; forgetting commutativity
  gives the ring sheaf used by `X.Modules` definitionally.
- The size convention is implemented by the explicit universe `u`, the existing
  site (objects and morphisms in `u+1`), and its module sections in `u`. The landed
  additive sheafification instances on this full site use its small affine basis,
  in the original section universe. No equality of the site and coefficient
  universes, no new size assumption, and no coefficient lift is imposed.
- Arbitrary structure-module sheaves are `(M N : X.Modules)`; this is the
  dependency's `ringedSiteModules` abbreviation of Mathlib's `SheafOfModules`.
- The hypothesis that an O_X-linear isomorphism exists is `h : Nonempty (...)`.
  The source of its isomorphism is
  `(SheafOfModules.siteSheafTensorRight (A := X.commStructureSheaf) N).obj M`.
  The already existing functor forgets to module presheaves, tensors their
  sections over the section rings, and applies module sheafification. Thus it
  is exactly the sheaf tensor of the node, with factors M then N. The target is
  `SheafOfModules.unit X.structureSheaf`, the structure sheaf as its regular
  module. Morphisms and isomorphisms here are module-sheaf morphisms, hence
  sectionwise O_X-linear.
- The two conclusions are precisely `X.IsLineModule M ∧ X.IsLineModule N`.
  Opening the recorded predicate gives: for each object T, a covering sieve R,
  and for every arrow U -> T in R an isomorphism of the restriction to U with
  `SheafOfModules.unit (X.structureSheaf.over U)`. This is local isomorphism to
  O_X on the small etale site, and is the node's definition of a line module.
- There are no finite-generation, finite-presentation, quasi-coherence,
  nonemptiness, field, characteristic, or noetherian binders.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (available
  transitively through the algebraic-space imports).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleTopology`, `structurePresheaf`, `structureSheaf`, `Modules`,
  `etalePullback`, and `IsLineModule` in its `AlgebraicSpace` namespace.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  its body is exactly `SheafOfModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  tensor dependency and its public imports, especially
  `SheafOfModules.siteSheafTensorRight` and `siteTensorPresheaf` from
  `TensorProductOfUniverses`. The direct functor is used because it supports
  independent site object, morphism, ring, and module universes without asking
  for a monoidal structure as additional input.
- `def-weil-size-convention` is metatheoretic; its record has no Lean object.
  Universe parameters and the existing small-basis sheafification implement it.
- Added the already landed node `def-sfb-space-quasi-coherent-algebra` to
  `stmt_deps` for `AlgebraicSpace.commStructureSheaf` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`. Its source is the
  existing regular-functions presheaf, with a sheaf-condition proof.
- Added the already landed node `def-sfb-space-comm-algebra-sheaf` to
  `stmt_deps` for `AlgebraicSpace.etaleAlgebraModulesHasSheafify` and
  `etaleAlgebraModulesWEqualsLocallyBijective` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf`. Their signatures
  supply sheafification on the full small etale site at section universe `u`.
  The two additions reuse existing interfaces; no dependency is replaced or
  repaired, no extra nodes are created, and no mathematical clause changes.

The stated proof-dependency modules are imported for stage 3: localized tensor
restriction; preservation of sheafification under forgetting to sets; local
representatives of sheafification sections; locally ringed spaces and etaleness
of open immersions; and tensor symmetry, associativity, and unitors. Modules
already publicly imported through the statement dependencies (module
sheafification, slice restriction, schemes, and ringed-site modules) are not
repeated. The theorem docstring gives all five proof steps of the DAG, including
the empty-chart case and the normalized-pair idempotent automorphism argument.

Edge cases checked before writing:

- The empty algebraic space and empty chart are permitted. The line predicate
  can use an empty covering on an empty chart; no `Nonempty` chart hypothesis
  occurs. `Nonempty` only expresses existence of the assumed isomorphism.
- Zero modules have not been excluded. On a nonempty ordinary scheme chart with
  nonzero structure stalk their tensor cannot be the structure module, so the
  hypothesis fails; on the empty chart it is consistent with local triviality.
- The zero coefficient ring and an empty tensor-sum expression are allowed;
  padding the latter with `0 tensor 0` supports the proof's finite-sum step.
- The factors need not be quasi-coherent or finitely presented. No such
  predicate occurs in their type or in any binder.
- The source is locally ringed because its objects are schemes, not because
  an arbitrary ringed-site tensor inverse always implies local rank one.
- Both factors are concluded to be lines. Symmetry gives the second assertion
  without an extra inverse hypothesis.

Searches for existing statements (all performed in this task):

- `msearch.py`, LeanFinder, `tensor inverse sheaf algebraic space line module`:
  8 hits, mostly scheme pullback tensor comparisons and
  `PresheafOfModules.Monoidal.tensorObj`; none states the criterion.
- `msearch.py`, Loogle, `IsLineModule tensor`: no hits; Mathlib does not know
  the project's algebraic-space `IsLineModule` identifier.
- `msearch.py`, LeanSearch,
  `tensor inverse sheaf of modules implies locally free rank one`: 8 hits,
  ordinary-ring-module Picard results and free module-sheaf constructions.
  The Picard results assume or discuss invertible ring modules and do not state
  local triviality for arbitrary O_X-module sheaves on an algebraic space.
- `msearch.py`, grep, `Invertible|tensor.*inverse` in
  `Algebra/Category/ModuleCat/Sheaf`: no hits.
- `msearch.py`, grep, `tensor.*IsLineModule`: no hits.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for
  `spaceTensor`, `tensorInverse`, `IsLineModule`, `line module`,
  `isLineModule_of_tensor_inverse`, and the exact node id: existing line-module
  definitions and consumers, categorical tensor inverses, constant-coefficient
  results, and the opposite direction (line evaluation) only; no matching
  algebraic-space criterion. The upstream name index has no matching name.

Sources opened: `literature/stacks-project/sites-modules.tex`, the complete
statements and proofs of `lemma-invertible` (0B8N) and
`lemma-invertible-is-locally-free-rank-1` (0B8Q). They impose no finite-presentation
hypothesis for this inference. No statement dispute or correction is needed.

Validation: the statement with the existing full-site sheafification and tensor
interfaces compiled on the server both as an isolated sandbox module and under
its actual library module name, without errors or warnings. Final module and
preflight validation are recorded by the delivery wrapper.

## Second reading by Q155

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
