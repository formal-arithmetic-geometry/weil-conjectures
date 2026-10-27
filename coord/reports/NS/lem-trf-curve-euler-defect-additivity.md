## Worker report

The module `Sheaf.AlgebraicGeometry.CurveEulerDefectAdditivity` states exactly the
additivity/well-definedness node and introduces its three pieces of notation:
`curveResidueStalk`, `curveGenericRank`, and `curveEulerDefect`. All definition data
are explicit. The only theorem is `curve_euler_defect_additivity`, with proof `sorry`.
The complete six-step natural-language proof from the node is in its docstring.
There are no new independent notions, dependency replacements, statement corrections,
or disputed statements.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- The integral proper k-scheme C: `(C : Scheme.{u}) [IsIntegral C]`,
  `[C.Over (Spec (.of k))]`, and `[IsProper (C ↘ Spec (.of k))]`.
  No smoothness, geometric integrality, or algebraic closedness is imposed.
- Topological dimension one: `(hdim : topologicalKrullDim C = 1)`.
- Its specified generic point: `(ξ : C) (hξ : IsGenericPoint ξ Set.univ)`.
  Mathlib defines this as `closure ({ξ} : Set C) = Set.univ`.
- Invertible L: `(L : C.Modules) [L.IsInvertible]`, the recorded scheme predicate.
- C is locally Noetherian and quasi-compact: conclusions
  `IsLocallyNoetherian C ∧ CompactSpace C`. Quasi-compactness of a scheme means
  compactness of its underlying space; neither is assumed.
- The generic local ring is a field: `IsField (C.presheaf.stalk ξ)`.
- The canonical residue-field identification: `∃ e : C.presheaf.stalk ξ ≃+*
  C.residueField ξ, e.toRingHom = (C.residue ξ).hom ∧ ...`.
  The equation fixes the actual quotient map, so an arbitrary isomorphism cannot
  satisfy this clause. It is asserted to exist, not supplied as a hypothesis.
- Every coherent H: `∀ H : C.Modules, RingedSpace.IsCoherent C.toRingedSpace H → ...`.
  This is the full finite-type and finite-type-kernel predicate (01BV), not merely
  quasi-coherence plus finite type.
- Tensor coherence: `RingedSpace.IsCoherent C.toRingedSpace (L ⊗ H)`.
- Finite-dimensional generic stalk over κ(ξ):
  `FiniteDimensional (C.residueField ξ) (curveResidueStalk ξ e H)`.
  `curveResidueStalk` restricts the existing ringed-space stalk module's scalars
  along `e.symm.toRingHom`. Mathlib's `ModuleCat.RestrictScalars.obj'` retains the
  underlying additive group and defines scalar multiplication by composition.
  Thus this is H_ξ itself with its canonical κ(ξ)-action, not its tensor fibre,
  a chosen replacement vector space, or an additional assumed action.
- Rank: `curveGenericRank ξ e H` is exactly
  `Module.finrank (C.residueField ξ) (curveResidueStalk ξ e H) : ℕ`.
- Integer defect: `curveEulerDefect k L ξ e H : ℤ` is
  `(L ⊗ H).eulerChar k - H.eulerChar k - (curveGenericRank ξ e H : ℤ) * L.degree k`.
  These are the recorded Euler characteristic and line-bundle degree definitions.
  Properness and coherence give the finiteness that makes their definitions meaningful,
  as explained in the proof docstring; no substitute Euler function is introduced.
- D_L(0) = 0: `curveEulerDefect k L ξ e (0 : C.Modules) = 0`, using Mathlib's
  standard `ZeroObject` scope for the categorical zero object.
- Every coherent short exact sequence: `∀ S : ShortComplex C.Modules,
  S.ShortExact → ...`, followed by coherence hypotheses for S.X₁, S.X₂, S.X₃.
  This is the sheaf-module abelian category, so categorical short exactness is the
  node's exact sequence of sheaves, not sectionwise exactness on all opens.
- Rank additivity: `curveGenericRank ξ e S.X₂ = curveGenericRank ξ e S.X₁ +
  curveGenericRank ξ e S.X₃`.
- Defect additivity: `curveEulerDefect k L ξ e S.X₂ = curveEulerDefect k L ξ e S.X₁ +
  curveEulerDefect k L ξ e S.X₃`.
- Vanishing for any two terms implies vanishing for the third: the final three
  conjuncts give the implications for pairs (1,2), (1,3), and (2,3), respectively.
  In particular the middle-term and first-term cases are not omitted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, its monoidal instance and tensor.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
  The scheme-conventions node is a convention-only record, with no module or declaration.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`
  and `AlgebraicGeometry.Scheme.residue`, the canonical local-ring quotient.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; this exact predicate is used.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` is the recorded
  general tensor interface. On scheme modules the tensor is the existing scheme
  monoidal tensor from `Modules.Invertible`, with sheafification semantics.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor` gives the recorded
  `PresheafOfModules.moduleStalkFunctor`. Its record explicitly directs scheme and
  ringed-space sheaves to `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` in
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`. The latter is the functor
  used. Added the already recorded `def-pc-module-stalk-functor` to stmt_deps to
  cite that exact interface. This also avoids confusing the RingCat stalk of the
  forgotten structure sheaf with the CommRingCat structure-sheaf stalk.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `ModuleCat.restrictScalars`.
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar` (integer alternating finsum).
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree` (Euler difference).
- `Mathlib.Algebra.Homology.ExactSequence` exposes the recorded categorical exactness;
  `CategoryTheory.ShortComplex.ShortExact` is used for sheaves.

The stated proof dependencies are imported without `public`:
`WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks`
(`Scheme.exists_ringEquiv_rationalFunctionRing_pi_stalk`),
`WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor`
(`openModuleStalkFunctor` and its exactness instances),
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper`
(`Scheme.Modules.finite_setOf_nontrivial_H_of_isProper`,
`finite_support_finrankH_of_isProper`),
`Mathlib.Algebra.Category.ModuleCat.Free` (`ModuleCat.free_shortExact_finrank_add`),
`WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact`
(`Scheme.Modules.finiteLocallyFree_tensorLeft_exact`), and
`WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`
(`Scheme.Modules.eulerChar_eq_add_of_shortExact`). The proof dependency
`lem-trf-proper-field-invertible-coherent` has neither a Lean record nor a Mathlib
match, so there is no module to import for it. It is not needed to type this
statement and is not restated here.

Source and edge checks: read `literature/stacks-project/varieties.tex`,
`lemma-degree-on-proper-curve`, lines 9669 onward (0AYV), including its proof of
condition (1). Rank-one specialization is precisely the node's Euler defect.
The empty scheme is excluded by the stated integrality and dimension-one assumptions,
not by a new assumption. Zero coherent modules and zero generic rank are allowed;
the zero-object case is explicitly asserted. Short exact sequences with any zero term,
including all three zero, are included. L can have zero or negative degree. All
characteristics and non-geometrically-integral curves are retained. The specified
point is arbitrary subject to genericity. The universe is explicit and shared with
the existing project's scheme/module/Euler interfaces; no new universe equation is
imposed on those interfaces. There are no auto-bound variables.

Searches for an existing complete statement and notation (2026-10-24):

- `msearch.py ... leanfinder "Euler characteristic defect generic rank additive coherent
  short exact sequence proper integral curve"`: eight hits, including
  `ModuleCat.free_shortExact_rank_add`, `ModuleCat.free_shortExact_finrank_add`,
  `Module.length_eq_add_of_exact` and unrelated cotangent/Profinite results.
  None supplies this scheme/sheaf assertion or the residue, coherence and zero clauses.
- `msearch.py ... leansearch "Euler characteristic defect of coherent sheaves on a proper
  integral curve is additive in short exact sequences"`: eight hits, including the
  dimension-additivity lemmas and short-complex functor additivity. No complete match.
- `msearch.py ... loogle "Module.finrank, Scheme.Modules.eulerChar, Scheme.Modules.degree"`:
  zero hits; the service reports unknown identifier `Scheme.Modules.eulerChar`.
  The project-specific definitions were instead read in their recorded source files.
- `msearch.py ... grep "eulerDefect|euler_defect|eulerChar.*rank|rank.*eulerChar"`:
  five hits in Mathlib's graded-object Euler characteristic module, no scheme defect.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `lem-trf-curve-euler-defect-additivity|eulerDefect|euler_defect`: only the unrelated
  `nodal_contraction_euler_defect` in `NodalContractionEulerDefect.lean`.
  Searches for `curveResidueStalk`, `curveGenericRank`, `curveEulerDefect`, and
  `curve_euler_defect_additivity` in Mathlib and both source trees found no declarations.
  The existing downstream `eulerChar_tensor_invertible_generic_rank` states the final
  Euler formula, not this node's prerequisites and additivity, and is not used circularly.

Validation: every compiler invocation used the prescribed `scompile.py`. The initial
probes found and repaired the RingCat/CommRingCat stalk mismatch and the missing
standard `ZeroObject` scope. The corrected file compiled on the server in 9.5 seconds,
with no errors or non-sorry warnings. The wrapper's local attempt ran out of temporary
space and automatically confirmed against current server sources successfully.

## Second reading by NS

This is an explicit same-worker second pass, not an independent agent review; the
assignment prohibits starting agents. The maintainer supplies the independent reading.
I reread the node and the completed file together. The specified generic point is
retained; its local ring is asserted to be a field, not assumed. The existential
isomorphism is fixed to the residue quotient, with that same e used in the finite-rank,
zero and exact-sequence clauses. `restrictScalars e.symm` changes only scalar action;
its carrier is the original stalk. All three coherence hypotheses are present in the
short-exact-sequence clause; tensor coherence and finite generic dimension hold for
every coherent H. The defect has the correct subtraction order and casts rank to ℤ
before multiplication by degree. All three two-out-of-three implications are present.
The compile-driven correction used the owning ringed-space stalk interface instead
of trying to identify independently constructed ring-category colimits. No node
statement or dependency definition was changed. No remaining mismatch was found.
