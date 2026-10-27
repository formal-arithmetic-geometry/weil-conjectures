## Worker report

Group Q74 states `AlgebraicGeometry.Scheme.CommAlgebraSheaf.finite_quotient_eventually_finite`
in `Sheaf.AlgebraicGeometry.FiniteQuotientEventualFiniteness`. Its sole proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The original node is preserved outside `lean`.

Read the node, all six statement dependencies and all six proof dependencies, their
records, and their available source declarations. Read Stacks `properties.tex`,
`lemma-finite-algebra-directed-colimit-finite-finitely-presented` (086N), especially
its final proof paragraph (lines 3405–3420), and
`lemma-integral-algebra-directed-colimit-finite` (0817), proof (2), lines 3452–3494.
The finite-cover monic-relation argument applies to the node's arbitrary compatible
module approximation: the lifted relations persist by cocone compatibility and
need neither injectivity nor finite generation of the approximating modules.

Hypothesis and clause correspondence:

- The qcqs scheme is `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]`.
  These are exactly the scheme conventions, without a separation or Noetherian hypothesis.
- The commutative structure algebra is `(S : X.CommAlgebraSheaf)`, the existing category
  `Under X.sheaf`; `hS : S.toModule.IsQuasicoherent` gives its quasi-coherence.
- Finite type on every affine open is `hSft`, with the structure ring homomorphism
  `(S.hom.hom.app (op U)).hom.FiniteType`. This is algebra finite type, not module finite.
- The quasi-coherent ideal module is `c.pt` with `hJ`; its inclusion is
  `i : c.pt ⟶ S.toModule`. The family `J U` consists of actual ideals, and `hi`
  makes `i.app U` injective and identifies its range with `J U` on every open.
  Naturality of `i` makes these ideal ranges compatible under restriction, while the
  sheaf property of `c.pt` gives the subsheaf property. Thus the data represent an
  ideal subsheaf, not an arbitrary family of section ideals.
- Finiteness of B = S/J on every affine open is `hfinite`: the quotient map
  `Ideal.Quotient.mk (J U)` is composed with the original structure map and is
  `RingHom.Finite`, meaning the target is finitely generated as a base module.
- The nonempty directed preorder is `(K : Type u) [Preorder K] [Nonempty K]
  [IsDirected K (· ≤ ·)]`. The index universe is the scheme universe, as required
  by the project's index-universe convention; no antisymmetry is imposed.
- The diagram and its transition maps are `(E : K ⥤ X.Modules)`; `hE` says every
  object is quasi-coherent. The compatible maps epsilon are `c.ι.app k`, where
  `c : Cocone E`; `hc : IsColimit c` states their module colimit universal property
  with the same ideal module as vertex.
- The generated ideal on an affine open at stage k is exactly
  `Ideal.span (Set.range ((c.ι.app k ≫ i).app U))`.
- The conclusion is `∃ k₀ : K, ∀ k : K, k₀ ≤ k → ∀ U : X.Opens,
  IsAffineOpen U → ... .Finite`, with the canonical quotient by that generated ideal
  and the original structure morphism. Thus one common stage works at every later
  index and on every affine open.
- No map from an E_k is assumed injective; none of the E_k are assumed finite type
  or finitely generated. `hi` is injectivity only of the ideal inclusion J → S.

The statement uses canonical affine ring quotients instead of naming an additional
sheaf quotient B or Q_k. This is an exact rendering of their specified finiteness,
not a change of objects or a weaker conclusion: the existing
`generated_ideal_quotient_quasiCoherent` gives quasi-coherence and surjectivity with
precisely that kernel on every affine open. Apply it to `c.pt` and `i` to identify
B(U) with S(U)/J(U), since J is already an ideal; apply it to `E.obj k` and
`c.ι.app k ≫ i` to identify Q_k(U) with the displayed span quotient. In each case
the first isomorphism theorem gives the isomorphism over the original base ring.
No arbitrary algebra, map, quotient identification, or unproved construction is chosen.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.IsQuasiCoherentAlgebra`, `QuasiCoherentAlgebra`,
  `Scheme.CommAlgebraSheaf.IsFinite`. The underlying category and module are
  `Scheme.CommAlgebraSheaf` and `.toModule` from `CommAlgebraSheaf`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit` are the
  dependency's recorded universal-property interface; no chosen colimit needed.
- `def-weil-pbc-scheme-conventions` is a convention-only record; its qcqs predicates
  are the standard `CompactSpace` and `QuasiSeparatedSpace` imported through
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the dependency's finite-type
  conjunction `Scheme.Modules.IsQuasiCoherentFiniteType` uses Mathlib's
  `SheafOfModules.IsQuasicoherent`; this theorem only needs the quasi-coherent
  factor and uses it directly, without imposing the finite-type factor on E_k.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is
  transparently Mathlib's `SheafOfModules`; `X.Modules` is its existing scheme
  specialization. No replacement category is defined.

All six proof-dependency modules are imported, including the Mathlib leaves:
`Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal`
(`kernel_image_quasiCoherent`, `generated_ideal_quotient_quasiCoherent`),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
(`isCompact_iff_finite_and_eq_biUnion_affineOpens`),
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`Algebra.IsIntegral.of_finite`),
`WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`
(`quasiCoherentModuleColimitAffineSections`),
`Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`
(`Algebra.finite_adjoin_of_finite_of_isIntegral`), and
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
(`quasicoherent_finite_type_affine`). The declaration docstring reproduces the
node's six proof steps with their dependency ids and explains the quotient encoding.

Edge cases checked before writing:

- Empty scheme and empty affine cover: no relation sections need lifting;
  nonemptiness of K still supplies k₀. The section rings of the empty open are
  zero rings, permitted by the statement and its finiteness predicates.
- A chart with no algebra generators: the empty list of monic relations imposes
  no extra requirement. No positive rank, nontrivial ring, or nonempty X is assumed.
- J = 0: the finite quotient is S itself, and every generated stage ideal is zero;
  the conclusion is consistent with finiteness of S. If J = S the final quotient
  is zero; colimit lifting of the finitely many relations still applies.
- Constant or one-object directed systems and preorders with equivalent distinct
  indices are allowed. No strict inequality or antisymmetry appears.
- Noninjective transition maps and noninjective epsilon maps are allowed: the
  persistence of relation sections uses the cocone equation, not injectivity.

Searches actually run using `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- LeanFinder: `A finite type quasi coherent algebra with finite quotient by an ideal
  has module finite quotients at every sufficiently late stage of a directed module
  approximation of that ideal`. Eight hits, including
  `Algebra.QuasiFinite.instQuotientIdeal`, `Ideal.finite_quotient_pow`,
  `Module.Finite.of_quasiFinite`, and `reesAlgebra.fg`. No exact sheaf-level match.
- Loogle: `Algebra.FiniteType, Module.Finite`. Eleven hits, including
  `Module.Finite.finiteType`, `Algebra.IsIntegral.finite`, and
  `Algebra.finite_iff_isIntegral_and_finiteType`. These are ring criteria, not
  eventual finiteness along arbitrary module approximations of an ideal.
- Mathlib grep: `eventual.*[Ff]inite|[Ff]inite.*quotient|[Ff]inite.*[Cc]olimit`,
  under AlgebraicGeometry. Four hits in Limits and AffineTransitionLimit, no match.
- LeanSearch: `A finite type algebra quotient by the ideal generated by a stage of
  a directed colimit of modules is eventually a finite module if the final quotient
  is finite`. Eight hits including `Algebra.FiniteType.quotient`,
  `Module.Finite.quotient`, and `FGModuleCat.instFiniteCarrierColimitModuleCatCompForget₂`;
  none states this sheaf quotient approximation lemma.
- `rg` in both `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for eventual finiteness and finite quotient phrases
  found adjacent material, including `IntegralAlgebraDirectedColimitFinite`, whose
  step 8 motivates this separate lemma but whose theorem states the full integral
  algebra approximation, not this statement. Its source was read.
- `grep -rn` of the exact node id in `lean/WeilConjectures` returned no match.
  `rg` for `finite_quotient_eventually_finite|finiteQuotientEventualFiniteness` in
  `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json` returned
  no existing declaration.

Validation: scompile.py Q74 lem-weil-pbc-finite-quotient-eventual-finiteness compiled
both its sandbox and library module names, cleanly, in 11.5 s and 12.6 s respectively.
Every variable and universe is explicitly bound; `autoImplicit false` is set.
No statement dispute or source fault was found.

## Second reading by Q74

Re-read the original node and delivered signature after the first clean compile.
This is the worker's second pass; the dispatcher prohibits starting another agent,
and the independent maintainer review remains separate.

The qcqs hypotheses match the original node. `hS` and `hSft` distinguish algebra
quasi-coherence from finite algebra generation. `c.pt`, `hJ`, `i`, `J`, and `hi`
represent exactly the original quasi-coherent ideal subsheaf; injectivity occurs
only in its inclusion, not in any approximation map. `hfinite` is finiteness for
the canonical quotient by that same ideal. `E`, `hE`, `c`, and `hc` retain the
arbitrary compatible directed module colimit from the statement. Checked that the
range used in the conclusion is the composite into S, not just the map into J,
and that the span is an ideal in S(U), not an O_X(U)-submodule span. The base map
in both finiteness predicates is the original structure map followed by the
quotient map. The quantifier order gives one k₀ before all k and all affine U.
The affine quotient identification is supplied by the recorded proof dependency
and remains valid without finite generation of E_k. No hypothesis or clause was
found missing, and no signature change was needed during this pass.
