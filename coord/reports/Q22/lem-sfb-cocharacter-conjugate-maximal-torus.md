## Worker report

The module `Sheaf.AlgebraicGeometry.CocharacterConjugateMaximalTorus` states
`AlgebraicGeometry.cocharacter_conjugate_maximal_torus`, with `sorry` as its only proof.
There are no helper definitions, new nodes, or dependency repairs. The natural-language
statement, accepted stage-1 proof, and proof dependencies are unchanged. The statement
dependencies gain the two already-landed definition nodes for tori and maximal tori:
`def-sfb-tori-multiplicative-type` and
`def-sfb-reductive-torus-centralizer-terminology`.

The inherited BLOCKED ending concerned stage-1 re-splitting, not this statement task.
The current queue lists this item at stage 2 without a Lean binding. The stage-handoff
paragraph in brief-stage2 section 0 expressly authorizes proceeding with deliver2 in
this situation. No stage-1 split is reopened.

Hypothesis and clause correspondence:

- An algebraically closed field k is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The k-group schemes G and T are `Grp (Over (Spec (.of k)))`. Their morphisms
  are scheme morphisms over k respecting the actual group laws, not arbitrary maps
  on rational points.
- G is affine and finite type through `[IsAffine G.X.left]`,
  `[LocallyOfFiniteType G.X.hom]`, and `[QuasiCompact G.X.hom]`.
- Smoothness and connectedness of G are `[Smooth G.X.hom]` and
  `[ConnectedSpace G.X.left]`. No reductivity or characteristic hypothesis is added.
- The prescribed inclusion is `i : T ⟶ G`. The hypothesis
  `hT : ReductiveTorusCentralizer.IsMaximalTorus i` unfolds to closed subgroup,
  torus, and absence of a strictly larger torus subgroup: every factorization of i
  through a closed torus inclusion has an isomorphism as its first map.
  In particular T is a closed subscheme of the affine finite-type G, so no further
  affine or finite-type assumptions on T are needed. The recorded `IsTorus` becomes
  a finite product of G_m after algebraic closure; over the algebraically closed k
  in this statement this is exactly a split torus over k, as in the node.
- The cocharacter is `mu : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G`.
  The domain uses the recorded actual Laurent-polynomial multiplicative group,
  not a replacement abstract group or only its k-points.
- The witnesses are `g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X`, a k-rational point,
  and `nu : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ T`, a cocharacter.
- The first equality says `(toUnit G_m ≫ g) * mu.hom.hom * (toUnit G_m ≫ g)⁻¹`
  equals `nu.hom.hom ≫ i.hom.hom` as actual morphisms G_m → G. Products and
  inverse here are the representable Hom-group operations from the recorded group law.
- The second equality quantifies over every `A : Type u`, `[CommRing A]`,
  `[Algebra k A]`, and point `t : StandardGroupSchemes.affine k A ⟶ G_m`.
  Since G_m is Spec k[z,z⁻¹], these points are precisely units t ∈ Aˣ, through
  the image of z (and its inverse). The displayed expression uses
  `toUnit (StandardGroupSchemes.affine k A) ≫ g` for g_A, `t ≫ mu.hom.hom`
  for mu_A(t), and `t ≫ nu.hom.hom ≫ i.hom.hom` for i_A(nu_A(t)). Thus it
  states g_A mu_A(t) g_A⁻¹ = nu_A(t) in G(A), with the inclusion explicitly shown.
  This is all-algebra equality, including nonreduced algebras, not just k-point equality.
- There is no nontriviality condition on mu and no positive-rank condition on T.

Dependency declarations read and reused:

- `Field`, Mathlib.Algebra.Field.Defs (def-weil-field).
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp` and group morphisms,
  Mathlib.CategoryTheory.Monoidal.Grp (def-sc-group-scheme).
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  and `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
  (def-weil-finite-type-morphism).
- `AlgebraicGeometry.IsSubgroupScheme` and `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs (def-sc-group-scheme-subgroup).
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth
  (def-sbc-smooth-morphisms).
- `ConnectedSpace`, Mathlib.Topology.Connected.Basic (def-weil-connected-scheme).
- `AlgebraicGeometry.StandardGroupSchemes.multiplicative`, `multiplicativeGroup`,
  `affine`, Sheaf.AlgebraicGeometry.StandardGroupSchemes (def-sc-gm-ga).
- `AlgebraicGeometry.MultiplicativeType.IsTorus`, `splitTorus`, `baseChange`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType (added landed statement dependency).
- `AlgebraicGeometry.ReductiveTorusCentralizer.IsMaximalTorus`,
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology (added landed dependency).
- Mathlib.CategoryTheory.Monoidal.Cartesian.Grp supplies `GrpObj.Hom.group`,
  inherited through the recorded subgroup module; the MonObj scope enables precisely
  those Hom-group operations. `CartesianMonoidalCategory.toUnit` is the canonical
  map to the terminal object, so no choice of scalar-extension map is assumed.

The module also imports the already-stated proof interfaces
`AlgebraicGeometry.exists_topologicalKrullDim_le` from
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType and
`topologicalKrullDimAt`/the Krull-dimension machinery from
WeilConjectures.Mathlib.Topology.KrullDimension. Closed immersions are available from
the public subgroup import. The proof nodes affine-homomorphism-flat-image,
torus-homomorphism-image, lattice-torus-coordinates-action, split-lattice-torus-projection,
and borel-maximal-torus-conjugacy have no recorded Lean declaration at this base; no
invented import for them is used. Their five-step proof route is retained in the theorem
docstring, including the greatest-dimension argument and the correct S-to-T orientation.

Source checked: local Milne Algebraic Groups (2017) PDF, Definition 12.14 and the
following paragraph (printed p.236: quotients of tori are tori), and Theorem 17.10 and
its proof (printed pp.354–355: conjugacy by G(k)). The statement agrees with these
sources and the accepted node; there is no statement correction or dispute.

Edge cases checked before writing:

- Trivial mu: g = 1 and trivial nu satisfy both equalities.
- Rank-zero torus, including trivial G: permitted by the existing splitTorus zero
  construction and by the maximal-torus predicate; no positive-rank restriction occurs.
- Smooth connected groups without reductivity, e.g. the additive group: no reductivity
  assumption enters, and the only cocharacter into a purely unipotent group is trivial.
- Positive-characteristic power/Frobenius cocharacters t ↦ t^p: no separability or
  kernel-smoothness assumption, so they remain in scope.
- Nonreduced and zero test algebras: allowed; the point type in the second conjunct
  and its Hom-group operations remain meaningful. No reduction to ordinary geometric points.
- The empty G is excluded exactly by connectedness (and already by the group unit).
- All variables and the single universe u are explicit, with autoImplicit false.
  Test algebras use the same universe as k and its schemes, never an independent
  smaller universe; morphism equality itself is scheme-theoretic.

Searches for an existing statement:

- msearch leanfinder: “Every cocharacter of a smooth connected affine algebraic group
  over an algebraically closed field can be conjugated into any chosen maximal torus”:
  8 hits, all Lie/root-system facts, no algebraic-group theorem.
- msearch loogle: `"torus", "conjugate"`: 0 hits.
- msearch grep: `cocharacter|[Mm]aximal[Tt]orus|[Ss]plit[Tt]orus`: 0 Mathlib hits.
- msearch leansearch: “A cocharacter of a smooth connected affine group scheme can
  be conjugated into any maximal torus”: 8 abstract-group/character hits, none matching.
- rg of cocharacter, IsMaximalTorus, IsTorus and splitTorus in Sheaf and
  WeilConjectures found the existing torus/maximal-torus definitions above and their
  self-centralizer/solvable-group uses, but no cocharacter conjugation theorem.
- rg for this exact blueprint id in WeilConjectures and cocharacter in
  dag/lean_names_upstream.json found no declaration.

Validation uses only scompile.py for individual compilation and deliver2.py for
server preflight/delivery. The first compile exposed μ as reserved MonObj notation;
the binder was renamed mu without changing the mathematical statement.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
