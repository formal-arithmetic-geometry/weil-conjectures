## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentReflexiveHull` states
`AlgebraicGeometry.Scheme.Modules.coherent_reflexive_hull`, with one postponed
proof and no new definitions. Only the item's `lean` record changes.

Clause-by-clause correspondence:

- A scheme X is `(X : Scheme.{u})`, for an explicitly bound arbitrary universe u.
- Integral is `[IsIntegral X]` (def-pc-integral-scheme), including nonemptiness.
- Locally Noetherian is `[IsLocallyNoetherian X]` (pqf-def-locnoeth).
- An O_X-module H is `(H : X.Modules)`.
- Coherence is `(hH : RingedSpace.IsCoherent X.toRingedSpace H)` (pqf-def-coherent).
  This is the finite-type and finite-type-kernel predicate, not merely the
  quasi-coherent/finite-type conjunction also exposed by the dependency module.
- O_X as its own module is `SheafOfModules.unit X.ringCatSheaf`.
- H dual is `SheafOfModules.homObj (R := X.sheaf) H
  (SheafOfModules.unit X.ringCatSheaf)` (def-pur-sheaf-hom).
- H double dual is the repeated `SheafOfModules.homObj`, with target O_X each time.
  The two occurrences in the conclusion are the identical expression.
- The first conjunct is `RingedSpace.IsCoherent X.toRingedSpace` of that double dual.
- The second conjunct is `IsIso (SheafOfModules.bidual (R := X.sheaf) ...)`, applied
  to H's double dual. The existing `bidual` has type M -> Hom(Hom(M,O_X),O_X), and
  evaluates a local functional at the restricted section. Thus this is exactly
  the evaluation H double dual -> H quadruple dual, not an unspecified isomorphism.
- There is no normality hypothesis, and no separatedness, global Noetherianity,
  finite local freeness, torsion-freeness, or reflexivity assumption on H.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded public interface for
  pqf-def-coherent, exposing `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`. The node's existing repair already
  exposes precisely the needed predicate; no dependency repair is needed here.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, the exact recorded sheaf Hom.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual`:
  `SheafOfModules.bidual`, the existing canonical evaluation morphism for the same Hom.
  Its source and the presheaf definition and sectionwise evaluation formula were read.
- Mathlib's `SheafOfModules.unit` and `AlgebraicGeometry.Scheme.Modules` are the
  existing structure-sheaf module and module category.

The module also imports the already recorded proof interfaces, privately:
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
(`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`),
`WeilConjectures.AlgebraicGeometry.CoherentHomLocalKernel`
(`Scheme.Modules.homObj_locally_kernel_of_coherent`),
`WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover`
(`coherent_module_local_on_open_cover`),
`WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum`
(`RingedSpace.coherent_kernel_cokernel_sum`),
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
(`Scheme.Modules.quasicoherent_finite_type_affine`), and
`Mathlib.AlgebraicGeometry.Modules.Tilde` (`tilde.adjunction`,
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`).
The two reflexivity lemmas in the proof plan currently have no Lean record, so
there is no module for them to import. They are proof prerequisites, not missing
objects needed for this statement.

Sources read: `literature/stacks-project/divisors.tex`, section Reflexive modules,
its definition, observation following the definition, lemma-dual-reflexive (0AY4),
and remark-tensor. These say the reflexive hull is coherent reflexive under exactly
the stated integral locally Noetherian hypotheses. The theorem docstring preserves
all five steps of the node's natural-language proof, including the canonical
comparison of evaluation maps and the empty-affine case.

Edge cases checked before drafting: the zero coherent module has zero double dual
and invertible zero evaluation; a torsion module may have zero dual, so no
injectivity or invertibility of H's own evaluation is claimed; the empty scheme
is excluded by integral, while empty affine opens are allowed and have zero section
modules; the structure sheaf case reduces to rank-one evaluation; nonnormal
integral locally Noetherian schemes are included. The single universe is the
existing category X.Modules universe, with no new universe equality assumption.
All variables and universes are explicitly bound, with autoImplicit disabled.

Searches (2026-10-24):

- msearch.py LeanFinder: "The double dual of a coherent module on an integral
  locally Noetherian scheme is coherent and reflexive". Eight hits for the module
  category, its Abelian structure, finite presentation and condensed sheaves;
  no coherent reflexive-hull theorem.
- msearch.py LeanSearch: "The reflexive hull of a coherent sheaf on an integral
  locally Noetherian scheme is coherent and reflexive". Eight algebraic reflexivity
  results, including finite free/projective reflexivity and reflexivity of a dual
  when the input is reflexive; no theorem about arbitrary coherent sheaves.
  The local Mathlib Dual/Defs.lean was read to check the actual assumptions, since
  the search summaries omit the input reflexivity assumption.
- msearch.py Loogle: `"IsReflexive", "Dual"`. Three hits:
  `Module.instIsReflexiveDual`, `Module.IsReflexive.bijective_dual_eval'`, and
  `LinearEquiv.isReflexive_of_equiv_dual_of_isReflexive`. None gives this statement.
- msearch.py grep: `reflexive|doubleDual|bidual` in Mathlib/AlgebraicGeometry:
  zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: searches for reflexivity, doubleDual,
  bidual and evaluation found the existing InternalHom and Bidual constructions,
  and finite-locally-free/invertible biduality theorems. Those assume more about
  the module and do not state coherent-reflexive-hull closure.
- rg for `lem-sfb-coherent-reflexive-hull` in `lean/WeilConjectures`, and for
  `coherent_reflexive_hull`, `isCoherent.*dual.*dual`, `IsCoherent.*ᵛᵛ`,
  `reflexive hull|reflexiveHull|reflexive_hull` in both library roots: no existing
  declaration of this statement. No duplicate notion is introduced.

Validation: the prescribed scompile.py checked both its sandbox and library
module modes successfully (1.5 and 1.6 seconds), with no errors or unexpected
warnings. The only postponed proof is `coherent_reflexive_hull`.
No statement dispute or correction, new node, or dependency repair was necessary.

## Second reading by Q72

I reread the node and the completed Lean file directly; this is a self-check,
not a claim of an independent worker review (the dispatcher forbids subagents,
and the maintainer supplies the independent review).

The two scheme assumptions match integral and locally Noetherian exactly. The H
binder is in X.Modules and hH uses the recorded full coherence predicate. Expanding
the repeated homObj expression gives precisely H double dual in both conjuncts;
expanding the existing bidual definition makes the second conjunct invertibility
of evaluation of that double dual, with the required quadruple-dual codomain.
No IsIso assumption is placed on H's evaluation and no extra property of X or H
is used. The full local-kernel/affine-Hom/naturality proof is in the docstring.
I found and removed a confusing description of the definition's placement in the
module source citation; the mathematical signature needed no change. No mismatch
between the node's hypotheses or its two clauses and the signature was found.
