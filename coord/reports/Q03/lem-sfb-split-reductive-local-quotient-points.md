## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveLocalQuotientPoints`
states `AlgebraicGeometry.splitReductive_local_quotient_points`, with a single
`sorry` proof. It introduces no definitions. The node's mathematical statement,
proof and proof dependencies are unchanged. Its statement dependencies gain the
two already landed definition nodes `def-sfb-split-torus-over-ring` and
`def-sfb-reductive-torus-centralizer-terminology`, whose notions the statement uses.

Clause-by-clause correspondence:

* A commutative Noetherian local ring: `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`. The last class extends `Nontrivial A`, so
  the required nonzero condition is included. Its unique maximal ideal is
  `IsLocalRing.maximalIdeal A`.
* The ideal and containment are `(J : Ideal A)
  (hJ : J ≤ IsLocalRing.maximalIdeal A)`. No nilpotence is imposed.
* The two A-group schemes are `(H S : Grp (Over (Spec (.of A))))`. `Grp` bundles
  the group-object diagrams of the recorded `CategoryTheory.GrpObj` interface
  over Spec A. These are groups, not necessarily commutative groups.
* Smooth affine finite type is `[Smooth H.X.hom] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`; finite type is the last
  two properties together, as specified by the dependency record.
* The closed subgroup is `(i : S ⟶ H)
  [IsClosedImmersion i.hom.hom.left]`. The bundled group morphism respects the
  group law, and its underlying scheme map is a closed immersion.
* The specified split-torus isomorphism is `(r : ℕ)
  (e : S ≅ RingGroupSchemes.splitTorus A r)`. Natural number rank includes zero.
  The existing definition uses LaurentPolynomial A with its actual Hopf law and
  an iterated product, whose rank-zero case is the trivial group.
* Reductive geometric fibres are `hred`, universally quantified over algebraically
  closed fields F and ring maps A →+* F. Pullback and `mapGrp.obj H` give the actual
  geometric fibre with its group structure. The recorded `IsReductive` means
  affine finite type, smooth, geometrically connected, and every smooth connected
  normal closed unipotent subgroup geometrically trivial. Its `IsUnipotent` is
  smooth faithful-matrix unipotence, not a placeholder. Over algebraically closed
  F the additional algebraic-closure test is equivalent to this same fibre test.
* The geometric maximal-torus hypothesis is `hmax` with the same fields and maps,
  applied to the actual pulled-back inclusion using `mapGrp.map i`.
  `IsMaximalTorus` requires a closed torus inclusion and that every containing
  torus inclusion has an isomorphic factorization. Over an algebraically closed
  field its torus predicate means a finite product of multiplicative groups.
* H(A) is the Hom type `𝟙_ (Over (Spec (.of A))) ⟶ H.X`: the terminal object of
  this over-category is Spec A with the identity structure morphism. H(A/J) is
  the Hom type from `Over.mk (Spec.map (CommRingCat.ofHom
  (Ideal.Quotient.mk J))))` to H.X. The displayed lambda precomposes with
  `toUnit` of this object. Its underlying scheme map is precisely the spectrum
  of the quotient ring homomorphism (by `CategoryTheory.Over.toUnit_left`), so
  this is the canonical reduction map, without a freely chosen map.
* Surjectivity is exactly `Function.Surjective` of that lambda. Precomposition
  preserves the group law on points. The node mentions cocharacters only as
  terminology; none occurs in its hypotheses or conclusion, so no irrelevant
  cocharacter variable is added.
* Neither henselianity nor completeness is a hypothesis. There is no restriction
  on characteristic or on nilpotents in A or J.

Dependency declarations read and used:

* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
* `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and the bundled
  `CategoryTheory.Grp`, over Spec A, as allowed by def-sc-group-scheme. Read also
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, whose module documentation
  explicitly identifies the group-object and point conventions.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
* `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, used inside the recorded
  reductivity predicate; it includes nonemptiness.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
* `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `AlgebraicGeometry.RingGroupSchemes.splitTorus` and its `multiplicative` input.
* `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` and `.IsMaximalTorus`.
  Read their underlying algebraicity/unipotence predicates in
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure` too.
* The proof-only import
  `Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveLocalGaussAtlas` supplies
  `AlgebraicGeometry.splitReductive_local_gauss_atlas`, with exactly these H,S,i,e,
  hred,hmax hypotheses. Read its full signature and proof docstring.
* The other recorded proof dependencies are imported without `public`:
  `Mathlib.AlgebraicGeometry.OpenImmersion` (`AlgebraicGeometry.IsOpenImmersion`)
  and `Mathlib.AlgebraicGeometry.Scheme` (`AlgebraicGeometry.Spec`, `.Spec.map`).

The node's source was opened at
https://sites.math.washington.edu/~jarod/papers/iwahori.pdf (Theorem 4.1 proof,
p.7) and https://stacks.math.columbia.edu/tag/01J6 (last proof paragraph).
The full local-quotient theorem is the DAG's explicitly labelled strengthening
of the approximation input, not a verbatim assertion of AHLH. Its four-step
proof is preserved in the declaration docstring: use the relative atlas, factor
the local-spectrum point through one chart, lift polynomial and unit
coordinates, and compose. The current blueprint unit and direct-image proof
were read under `literature/blueprint/latest/`; this is a descendant tool, not
the unit's own statement.

Edge cases checked before writing:

* J=0 gives reduction through Spec(A/0), canonically the identity-base case; no
  literal equality A/0=A is required. J=m gives residue-field point lifting.
* Non-nilpotent J is allowed: for A=k[t]_(t) and J=(t), the coordinate argument
  still lifts units, since uv=1+j is a unit. No formal-smoothness lifting shortcut
  is being assumed.
* r=0 and the trivial group are included; the actual split-torus construction has
  trivial rank-zero product. In the atlas proof d=0 and empty Laurent lists need
  no coordinate choices. A torus H=S and GL_n give the expected unit and matrix
  lifting special cases.
* A zero ring is excluded by `IsLocalRing`; J=top is excluded by hJ. The empty
  scheme is not incorrectly admitted as a connected geometric group fibre.
* All geometric test fields live in the ring's universe u, matching the existing
  atlas interface, rather than an independent smaller universe. Residue fields
  and their algebraic closures admit representatives in this universe. The
  universes and every binder are explicit, with both auto-implicit options false.

Searches for an existing theorem, all on 2026-10-24 with
`/home/ubuntu/weil-launcher-all/batch2/msearch.py Q03
lem-sfb-split-reductive-local-quotient-points`:

* `leanfinder`: "For a split reductive group scheme over a local ring the map on
  points to points over a quotient by an ideal contained in the maximal ideal is
  surjective". Eight hits: Scheme.residue_surjective, pointsPi_surjective,
  IsLocalRing.residue_surjective, Ideal.algebraMap_residueField_surjective,
  Ideal.Quotient.stabilizerHom_surjective_of_profinite,
  IsLocalization.surjective_quotientMap_of_maximal_of_localization,
  Ideal.surjectiveOnStalks_residueField,
  PrimeSpectrum.piLocalizationToMaximal_surjective. None is this theorem.
* `loogle`: `"IsLocalRing", "Surjective"`. Eight hits, including
  IsLocalRing.of_surjective, .of_surjective', .map_maximalIdeal_of_surjective,
  .surjective_units_map_of_local_ringHom, residue-surjectivity declarations,
  .spanFinrank_maximalIdeal_add_finrank_eq_of_surjective, and
  .exists_surjective_of_not_isLocalRing. Unit lifting is relevant to the proof
  but does not supply the general reductive-group statement.
* `leansearch`: "For a split reductive group scheme over a local ring reduction
  modulo a proper ideal is surjective on points". Eight hits: residue-field
  surjectivity, scheme stalk surjectivity, pointsPi surjectivity, and the local
  ring tensor-injectivity criterion. No match.
* Mathlib `grep` search:
  `splitReductive.*quotient|reductive.*surject|local.*quotient.*points`: zero hits.
* `rg -n` over `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for
  `splitReductive_local_quotient_points|lem-sfb-split-reductive-local-quotient-points`
  found only the existing Cartan theorem's proof-plan reference; no declaration.
* Searches for `splitTorus`, `IsReductive`, and `IsMaximalTorus` found the two
  landed definition nodes above, reused without duplication. The atlas theorem
  is structurally stronger input, not the same declaration.

The initial sandbox and library-form server compiles via `scompile.py` both
passed without errors or warnings. All Lean lines are at most 100 characters.
There is no disputed statement, dependency repair, new definition node, or
statement correction.

## Second reading by Q03

The dispatcher explicitly prohibits starting another agent; the maintainer's
independent review follows delivery. This section records this worker's separate
manual rereading of the node against the completed Lean file, not an independent
worker review. I checked the ring hypotheses and nontriviality, hJ, all four
structure-map properties, the bundled closed subgroup, specified rank and
isomorphism, both geometric-fibre quantifiers, and the source/codomain and
direction of precomposition in the final `Function.Surjective`. In particular,
`toUnit_left` identifies reduction with Spec of `Ideal.Quotient.mk J`, and the
terminal source is H(A), not a group-scheme-homomorphism type. No mismatch was
found and no statement correction was needed. The two added definition-node
dependencies are already landed and exactly the notions used by hred,hmax,e.
