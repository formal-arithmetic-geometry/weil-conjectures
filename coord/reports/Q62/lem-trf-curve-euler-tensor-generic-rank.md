## Worker report

The module Sheaf.AlgebraicGeometry.CurveEulerTensorGenericRank states
AlgebraicGeometry.Scheme.Modules.eulerChar_tensor_invertible_generic_rank with sorry.
It is the invertible-first-factor (n = 1) specialization of Stacks 0AYV,
varieties.tex, lemma-degree-on-proper-curve, lines 9668–9702. No theorem is proved,
no new notion is defined, and the item's natural statement is unchanged.

The hypotheses and conclusion match as follows:

- A field k is `(k : Type u) [Field k]`.
- The scheme and its k-structure are `(C : Scheme.{u}) [C.Over (Spec (.of k))]`.
  Properness is `[IsProper (C ↘ Spec (.of k))]`; integrality is `[IsIntegral C]`.
- Dimension one is `(hdim : topologicalKrullDim C = 1)`. It is topological
  dimension, not a smooth-relative-dimension assumption.
- The invertible module is `(L : C.Modules) [L.IsInvertible]`.
- The coherent module is `(F : C.Modules)` with
  `(hF : RingedSpace.IsCoherent C.toRingedSpace F)`.
- The generic point and its characterization are `(ξ : C)` and
  `(hξ : closure ({ξ} : Set C) = Set.univ)`.
- The finite generic rank is
  `Module.finrank (C.presheaf.stalk ξ) (F.presheaf.stalk ξ)`.
  The node explicitly identifies the generic local ring with κ(ξ). On an
  integral scheme the generic local ring is a field, and its residue quotient
  is canonically isomorphic to it (its maximal ideal is zero). Computing rank
  over this local ring with the existing stalk action therefore computes
  exactly dim_{κ(ξ)} F_ξ, without introducing an arbitrary residue-field action
  or an extra choice of module structure. Coherence implies finite generation
  of this stalk and hence finite dimension; neither is assumed additionally.
  The bundled `PresheafOfModules.moduleStalkFunctor` uses this same Mathlib
  stalk and scalar action, as its current source shows.
- The sheaf tensor is `L ⊗ F`, the existing localization/sheafification tensor.
  The conclusion is exactly
  `(L ⊗ F).eulerChar k = (Module.finrank ... : ℤ) * L.degree k + F.eulerChar k`.
  The integer cast reflects r as a nonnegative integer in the integer formula.
- There is no positive-rank, local-freeness-of-F, smoothness, algebraic-closure,
  geometric-integrality, or characteristic restriction.

Dependency declarations used (source signatures and docstrings were read):

- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper.
- Mathlib.Topology.KrullDimension: topologicalKrullDim.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  AlgebraicGeometry.Scheme.Modules.IsInvertible.
- WeilConjectures.AlgebraicGeometry.Coherent:
  AlgebraicGeometry.RingedSpace.IsCoherent (Stacks 01BV; imported directly).
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField and Scheme.residue;
  the formula uses the canonically equivalent generic local-ring dimension.
- WeilConjectures.Topology.PresheafModuleStalkFunctor:
  PresheafOfModules.moduleStalkFunctor and stalkObj, the latter definitionally
  the usual Mathlib stalk with its existing local-ring module structure.
- Mathlib.LinearAlgebra.Dimension.Finrank: Module.finrank.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses is imported
  for the recorded tensor dependency. The tensor instance actually used on
  C.Modules is SheafOfModules.monoidalCategory C.sheaf, the existing
  localization/sheafification tensor of Stacks 03EK. No second tensor is defined.
- WeilConjectures.AlgebraicGeometry.Cohomology.Defs:
  AlgebraicGeometry.Scheme.Modules.eulerChar.
- WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar:
  AlgebraicGeometry.Scheme.Modules.degree.

Every stated proof dependency is imported without public unless also needed
for the statement. The docstring carries all eight proof steps: Noetherian
and coherent preliminaries and D(0), tensor and Euler additivity, stalk rank
additivity, classification of integral closed subschemes, O_C witness,
closed-point witness, zero-dimensional-support calculation, and coherent
property devissage. The generic-rank-zero case is kept throughout.

Edge cases checked mathematically: F = 0 gives 0 = 0; L = O_C gives degree
zero and the tensor unit identity; F = O_C gives the definition of degree;
a sheaf supported at a closed point has rank zero and unchanged Euler
characteristic under twisting, including nontrivial residue extensions.
Torsion plus positive-rank coherent sheaves are allowed; singular integral
curves are allowed. The empty scheme is excluded by integrality, and
zero-dimensional proper schemes by dimension one, just as in the node.
Positive characteristic is unrestricted. There are no independent test-object
universes or site universe equalities.

Searches for an existing statement, run using msearch.py Q62 with this item:

- leanfinder: "Euler characteristic of invertible twist of a coherent sheaf on
  an integral proper curve equals generic rank times degree plus original
  Euler characteristic". Eight unrelated hits: incidence-algebra Euler
  characteristics, scheme-module Abelian instance, rankAtStalk, and
  representation characters; no matching statement.
- leansearch: "Euler characteristic tensor coherent sheaf line bundle proper
  integral curve generic rank degree". Eight unrelated hits about integral
  curves in differential geometry, incidence algebras, characteristic
  polynomials, representation characters and Lie rank; no match.
- loogle: "AlgebraicGeometry.Scheme.Modules.eulerChar, Module.finrank".
  No hits; unknown identifier AlgebraicGeometry.Scheme.Modules.eulerChar
  in the service's Mathlib index.
- msearch grep: "eulerChar.*tensor|tensor.*eulerChar" in AlgebraicGeometry:
  zero Mathlib hits.
- rg in WeilConjectures and lean/Sheaf for Euler/tensor/rank, generic stalks,
  and the proposed name: no exact theorem. Existing RiemannRoch tensor
  formulas require a smooth proper curve or a Cartier divisor. The Ample
  forward-difference theorem requires an ample module and is not this
  arbitrary invertible-twist formula. The supplied node id has no upstream
  occurrence. The proposed declaration name also has no occurrence in
  dag/lean_names_upstream.json, Mathlib, WeilConjectures or lean/Sheaf.
- Read Stacks varieties.tex locally at both 0AYV and 0AYR; the node is exactly
  the n = 1 specialization and the existing degree is chi(L) - chi(O_C).
- Read current upstream sources missing in the older local checkout with
  scompile.py --source: WeilConjectures.AlgebraicGeometry.Coherent,
  WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre, and
  WeilConjectures.Topology.PresheafModuleStalkFunctor.

Validation: scompile.py Q62 lem-trf-curve-euler-tensor-generic-rank compiled
both the sandbox and final module contexts cleanly, 2.3 seconds each, with
no errors or warnings. The sole theorem has sorry as its complete proof.
There is no STATEMENT-DISPUTED and no fault in the item's statement.

## Repair of returned delivery ed903570217a

H13: removed dag/nodes/sec-abelian-varieties/pqf-def-coherent.json from the
packet. The landed Q25 CoherentFiniteType/IsQuasiCoherentFiniteType record and
its module are preserved. The item imports
WeilConjectures.AlgebraicGeometry.Coherent directly and its lean.note now
identifies the coherent clause as RingedSpace.IsCoherent, Stacks 01BV.
No dependency record is rebound and this delivery has no dependency modules.
The item module, theorem signature, natural statement, stmt_deps, proof and
proof_deps remain unchanged. Compared the retained node with the current
shared base: the only changed field is lean.

Advisories: corrected the tensor-instance description above to
SheafOfModules.monoidalCategory C.sheaf (the same Stacks 03EK tensor).
The second reading below is explicitly the author's self-check; the
maintainer provides the independent review.

## Second reading by Q62

Author's final self-check, not an independent review: reopened the saved module,
item node, current base node and upstream Coherent source. Field, integral proper
scheme over k, topological dimension one, invertible L, coherent F, generic point,
and the integer Euler identity match the binders and conclusion listed above.
The generic rank is over the canonical local-ring stalk action, canonically the
residue-field dimension at the generic point; zero generic rank is allowed.
Re-read Stacks varieties.tex, lemma-degree-on-proper-curve, and checked its n = 1
specialization. RingedSpace.IsCoherent is finite type plus finite-type kernels on
every open (01BV), exactly the coherent clause. The item imports it directly.
The repair removes the dependency-node overwrite, adds only the item's lean.note,
and corrects the report's tensor-instance name. No change to the Lean module is
needed. Independent review is the maintainer's delivery review; no other agent
was started.
