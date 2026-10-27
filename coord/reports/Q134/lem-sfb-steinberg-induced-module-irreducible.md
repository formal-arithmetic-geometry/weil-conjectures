## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SteinbergInducedModuleIrreducible`
states `AlgebraicGeometry.steinberg_induced_module_irreducible`, with its sole theorem
proof `sorry`. It uses the actual `RhoSection.sectionModule`, not an abstract induced
representation. There are no new definitions, helper axioms, or statement corrections.

Hypothesis and clause correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Positive characteristic p: `(p : ℕ) [CharP F p] (hp : 0 < p)`. A field of positive
  characteristic automatically has prime characteristic, so no extra primality
  hypothesis is necessary. In particular p = 1 is impossible.
- Semisimple group scheme S: bundled `S : Grp (Over (Spec (.of F)))` and
  `hS : IsSemisimpleGroupScheme S.X`. That existing predicate includes smoothness,
  connectedness, affineness, finite type, and the condition on solvable normal
  subgroups. The affine instance binder exposes a structure already implied by hS;
  it is needed by the existing coordinate Hopf API and imposes no additional condition.
- Simply connected: `hsc` is the exact existing rho-section theorem's quantified
  condition on homomorphisms from semisimple groups. It requires surjectivity,
  finite kernel, and centrality after every algebra extension, and concludes `IsIso f`.
- Arbitrary split maximal torus T and Borel B containing it: `i`, `j`, `k`, and
  `hpair : IsRhoBorelPair i j k`. The predicate includes the split-torus isomorphism,
  maximal-torus and Borel conditions, and `k ≫ j = i`; no pair is singled out.
- Positive roots in Lie(B): `a` and `hconj` identify the torus action with actual
  conjugation on every test scheme; `hroots` identifies the list Φ with all nontrivial
  character tangent weight spaces, and `hΦ : Φ.Nodup` prevents multiplicities.
  These are exactly the data supplied by `exists_rho_section_modules`.
- Integral half-sum rho: `ρ` is an actual group-scheme character and `hρ` says its
  square is the product of the positive roots, i.e. twice rho is their sum in X*(T).
  This is an equality of characters, not an equality in the coefficient field.
- Extension rhoB: `ρB` is a character of B and `hρB : k ≫ ρB = ρ` gives its
  restriction. `htrivial` says it vanishes on every smooth connected normal
  unipotent subgroup, equivalently on the unipotent radical. The smoothness
  hypothesis in that quantified clause matches the node's specified smooth radical.
- Every integer r at least one: `(r : ℕ) (hr : 0 < r)` covers exactly those integers.
- The displayed module E_B(-(p^r-1)rhoB): every occurrence is
  `RhoSection.sectionModule S B j ρB (p ^ r - 1)`. Unfolding the existing definition
  gives the intersection of the kernels of
  `evaluate (g * (b ≫ j)) - characterValue (b ≫ ρB) ^ (p ^ r - 1) • evaluate g`,
  for every commutative F-algebra A, g and b. This is precisely the positive
  right-semi-invariance equation of the node, with no Borel sign reversal.
- Rationality: the conclusion supplies `c` on this actual subspace, with the existing
  `HopfAction.Coassociative` and `HopfAction.Counital` laws.
- Specified action `(s f)(g) = f(s⁻¹g)`: the third conjunct says that for every finite
  presentation `c f = ∑ q, v q ⊗ z q` and every algebra-valued s and g,
  `∑ q, evaluate g (v q).val * evaluate s (z q) = evaluate (s⁻¹ * g) f.val`.
  All tensor elements have such a finite presentation. Evaluation on all algebra
  points of the affine product detects equality; the section-subspace tensor
  inclusion is injective over a field. Hence this pins down the canonical left
  coaction uniquely and does not choose an arbitrary representation. The predicate
  is written inline to avoid introducing a duplicate representation notion.
- Nonzero and only zero/whole rationally stable subspaces: the final conjunct is
  `RationalHighestWeight.IsSimple c`. Its existing definition is `Nontrivial V ∧
  ∀ N : Submodule F V, IsStable c N → N = ⊥ ∨ N = ⊤`, where stability means the
  coaction lies in the range of the actual tensor inclusion `N ⊗ F[S] → V ⊗ F[S]`.
  Thus invariance is for the rational coaction, including nonreduced scalar extensions.

Dependencies used, with source declarations read in full:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed
  part of def-weil-algebraic-closure's recorded match.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj` and `Grp`; the group-scheme
  specialization and kernel/finite terminology in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` were also read.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`: `IsRhoBorelPair` and
  `exists_rho_section_modules`; its public dependency
  `Sheaf.AlgebraicGeometry.RhoSectionModuleData` supplies `sectionModule`,
  `Coordinate`, `evaluate`, `characterValue`, `HasRationalLeftTranslation`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `coordinateAlgebra`, `coordinateHopf`, `IsStable`, `IsSimple`. Its already landed
  owning node `def-sfb-rational-highest-weight-data` is added to stmt_deps; no copy
  or repair of that node is delivered. The public import provides the coaction API.
- Available proof dependencies are plain imports:
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit`, and
  `Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight`.
  The primitive-line, Weyl-dimension, restricted-rho-dimension, and restricted-weight
  dimension-product nodes currently have no Lean records; no missing proof-only
  declaration is required to state this item. The theorem docstring records all
  six proof steps and names those future proof inputs.

Source checked: the current blueprint's direct-image proof does not state this
supporting representation-theoretic lemma (as its split_report explains). Jantzen
is listed as wanted. I downloaded and read the published primary corroboration,
[Alexandre, pp.263--264, Definitions 2.4 and 2.8, Proposition 2.9](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/040B68C3EED952CD49A7F605ED4994B4/S0010437X24007607a.pdf/positivity-plethysm-and-hyperbolicity-of-siegel-varieties-in-positive-characteristic.pdf).
Its convention declares roots positive when their negative root group lies in B;
the node instead uses roots in Lie(B), so its rho is the negative of that source's.
The associated line-bundle right-semi-invariance equation and left action then
identify the node's space with the source's Steinberg induced module. Proposition
2.9 states simplicity. The characteristic-two exception requires integral rho,
which is explicitly part of our data.

Edge cases: characteristic two is retained (rho is integral before multiplying),
empty root list/trivial group is retained (the half-sum equation forces the trivial
character because a split-torus character lattice is torsion free, giving the
one-dimensional constant module), reducible root systems are retained, and r = 1
is retained. r = 0 is excluded exactly as in the node. The zero subspace cannot
satisfy the conclusion's Nontrivial conjunct. Tensor presentations include the empty
sum and zero tensors. F, the schemes, and the test F-algebras share universe u as
in the dependency API; arbitrary u is allowed, and same-universe affine product
points already detect the coordinate identities. `autoImplicit false` binds every
variable and universe explicitly. No local notation, private definition, or local
instance is introduced.

Searches for an existing theorem:

- `msearch.py leanfinder`: “The induced rational representation of a simply
  connected semisimple algebraic group of highest weight (p^r-1)rho is simple”.
  Eight hits: Weyl-group root representations, Lie modules, and finite-group FDRep
  results. Read representative `RootPairing.isSimpleModule_weylGroupRootRep`;
  it is about the Weyl group representation, not this rational algebraic-group module.
- `msearch.py loogle`: `"Steinberg"`: zero hits.
- `msearch.py grep`: `Steinberg|steinberg|HasRationalLeftTranslation|RhoSection`:
  zero Mathlib hits.
- `msearch.py leansearch`: “The Steinberg induced rational module is simple in
  positive characteristic”: eight hits, including abstract `IsSimpleModule` and
  finite-group/characteristic-zero results; none is the required statement.
- `rg` in `lean/WeilConjectures` for Steinberg/rho-section names returned
  semilinear Lang--Steinberg declarations only; the exact node-id search had no hits.
  `rg` in `lean/Sheaf` found the rho-section and rational highest-weight interfaces
  reused here, with no Steinberg simplicity theorem. Searched full proposed
  declaration/module names in `dag/lean_names_upstream.json`, Sheaf and
  WeilConjectures: no collisions.

Validation: scompile.py accepted the delivered module against the current server
sources (8.2 seconds), with no Lean warnings or errors. The faster cached compiler
initially reported no space on its temporary device, and the wrapper's automatic
current-source confirmation compiled cleanly. An earlier elaboration exposed that
the two existing coordinate-algebra presentations have distinct scalar-instance
paths; the delivered evaluation identity avoids any extra comparison object and
states the action directly using the already recorded evaluation map.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
