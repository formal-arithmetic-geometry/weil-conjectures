## Worker report

States the uniform heart-only proper cohomology bound, with its proof postponed as `sorry`.
The node statement, proof, and dependency lists are unchanged.

Hypotheses and clauses:
- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- `Λ` is a commutative condensed ring, with `MonObj Λ` and `IsCommMonObj Λ`.
- `hΛ` lists precisely A, Z_l, O_E, Q_l, E, and the norm-topological algebraic closure,
  in that order. Its first alternative requires a finite discrete commutative ring killed
  by a power of ℓ; the remaining alternatives use the published continuous-map ring objects.
  E is a finite intermediate field of the fixed `PadicAlgCl ℓ`; `padicIntegersRingObj`
  is its valuation ring. Ring-object isomorphisms express the allowed representations of
  Λ without altering coefficients. No finite-subextension-valued algebraic-closure case
  is added. The current `IsLocalizingAdmissibleCoefficient` includes that extra case, so
  using it alone would strengthen this node; the exact six alternatives are spelled out
  in the theorem binder, without introducing any new or private definition.
- S is `Scheme.{u}` with `[CompactSpace S] [QuasiSeparatedSpace S]`.
- `q : Y ⟶ S` and `f : X ⟶ Y` each carry `[IsProper ...]`.
- A_X and A_Y are internal `Mod` categories over the published `condensedRingObj Λ`.
- `weakSerreCoproductClosure.{u + 1} (IsConstantModelConstructible Λ X)` is the
  intersection of isomorphism-, kernel-, cokernel-, extension- and coproduct-closed
  properties containing the specified constructibles. Its coproduct closure includes
  the empty family, hence zero. Its extension condition is middle-object closure for
  short exact sequences. The index universe u+1 is the project's small-site convention.
- `∃ d : ℕ` is an integer d >= 0 via the displayed cast; it precedes M, so is uniform.
- M is a heart module, with membership in that closure as the only module hypothesis.
- `DerivedCategory.singleFunctor _ 0` is M[0]; `moduleObjectDerivedPushforward Λ f`
  is the total right derived full module pushforward. `homologyFunctor _ r` and
  `IsZero` express precisely H^r = 0 for every integer r > d.
- No completeness, invertibility, field, Noetherian or dimension hypothesis is present.

Statement dependency declarations read and used:
- Sheaf.Paper.LocalizingAdmissibleCoefficients: coefficient ring representations and the
  coefficient convention; its broader coefficient predicate is deliberately not assumed.
- Sheaf.Paper.CondensedModuleDerivedPushpull:
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward.
- Sheaf.Paper.CondensedConstantConstructibility:
  AlgebraicGeometry.ProEtale.IsConstantModelConstructible, whose finite scalar-model
  and affine-local clauses were read in full.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper, together
  with the finite-type and quasi-compact notions it imports.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: QuasiSeparatedSpace and
  AlgebraicGeometry.QuasiSeparated (the latter explains the geometric convention).
- Mathlib.Topology.Defs.Filter: CompactSpace, exposed by the geometric imports.
- def-weil-size-convention has no declaration: explicit u, sites with objects u+1,
  abelian coefficients u+1 and coproduct index u+1 implement its convention.
- WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure:
  CategoryTheory.ObjectProperty.weakSerreCoproductClosure. The upstream specialized
  constructibleCoproductClosure uses arbitrary local finite presentations, so cannot
  replace the generic closure applied here to finite constant-model constructibles.

All recorded proof-dependency modules are imported when available. The two newly split
geometric inputs lem-sfb-proper-wcontractible-closed-fibre-rigidity and
lem-sfb-profinite-geometric-family-heart-cd have no Lean records and are not imported.
Mathlib proof leaves require no new module. No import cycle is introduced.

Edge cases read before writing: zero M and empty coproducts lie in the closure; empty
schemes and fibres are allowed; d=0 permits all r>0; r<=d is unrestricted; A can be the
zero ring; ℓ may equal a residue characteristic. There is no excluded negative degree
or imposed cohomological completeness. No statement correction or disputed flag.

Searches:
- msearch leanfinder, query: A proper morphism of qcqs schemes has uniformly bounded
  higher direct images on the weak Serre coproduct closure of finite constant scalar-model
  constructible pro-etale modules. Eight hits (properness instances, condensed
  Grothendieck instances, affine limit lemmas), none states this estimate.
- msearch leansearch, query: Uniform upper bound for higher proper direct images on the
  weak Serre coproduct closure of constructible pro-etale module objects over a qcqs base.
  Eight hits (sheaf/module limits, condensed AB4Star and order/closure lemmas), no bound.
- msearch loogle, query: AlgebraicGeometry.IsProper, DerivedCategory.singleFunctor.
  Zero hits.
- msearch grep, query: proper.*(heart|Serre|cohomologicalDimension)|weakSerreCoproductClosure.
  Ten Mathlib hits, Serre derivative, abstract t-structure hearts and Serre localization;
  none matches.
- rg over WeilConjectures and Sheaf for weakSerreCoproductClosure,
  constructibleCoproductClosure, heart bounds, and this node id: found the generic
  intersection closure, the upstream broader-constructibility specialization, and
  narrower proper heart bounds requiring fields or special coefficients. No exact match.
- Read the source refinement proof (2), first paragraph, and the node's complete
  five-step local-to-global proof, retained verbatim in the theorem docstring.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
