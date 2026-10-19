## Worker report

The module `Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction` states
`DerivedCategory.isPseudoCoherent_inverse_ring_reconstruction`, with proof `sorry`.
It introduces no new definition, node, dependency module, or statement correction.
Source checked: Stacks Project, More on Algebra, Tag 0CQF,
`lemma-Rlim-pseudo-coherent-gives-pseudo-coherent`, statement and full proof in
`literature/stacks-project/more-algebra.tex`, lines 28335–28375. The node uses its
nilpotent-kernel, first-level-pseudo-coherent case. The complete six-step proof from
the node is included in the theorem docstring.

The statement's inputs and conclusions match as follows. All indices in Lean are
shifted by one: `0` is the source's `1`; `n + 1` is the next level.

1. Commutative inverse-system rings are `R : ℕ → Type u`, with
   `[∀ n, CommRing (R n)]` and `φ : ∀ n, R (n + 1) →+* R n`.
   A sequential inverse system is determined by these successive maps.
2. Surjective transitions are exactly `hsurj : ∀ n, Function.Surjective (φ n)`.
3. Nilpotent kernels are `hnil : ∀ n, IsNilpotent (RingHom.ker (φ n))`.
   Ideal multiplication is the relevant multiplication; exponent zero causes
   no extra case, since an ideal with zeroth power zero is in the zero ring,
   where its first power is also zero.
4. The inverse-limit ring is `A`, its projections are `q`, and `hq` makes the
   projections compatible. `hlim` says every compatible scalar tuple has a
   unique preimage. Since all `q n` are ring homomorphisms, this is exactly
   the compatible-tuple ring with componentwise operations, presented by its
   canonical ring isomorphism. No completion or adic-ideal hypothesis is added.
5. `HasDerivedCategory.{w}` binds the chosen localization universes, and all
   module categories use `ModuleCat.{max u v}` so the rings and their finite
   free modules fit. `Eₙ n` is an object of the recorded `DerivedCategory`.
6. `L n` and `adjφ n` present derived scalar extension as the left adjoint of
   `(ModuleCat.restrictScalars (φ n)).mapDerivedCategory`. This is a universal
   characterization of derived tensor, not an arbitrary functor with a name.
   Ordinary restriction is exact. Its derived functor is the actual Mathlib
   construction, including `mapDerivedCategoryFactors`. The one-object-site
   specialization of `SheafOfModules.derivedChangeOfRings` supplies the usual
   K-flat construction; its derived tensor is this left adjoint, uniquely up
   to the adjunction-preserving isomorphism. There is no flatness assumption
   on `φ`, `q`, or the quotient rings.
7. `t n : Eₙ (n + 1) ⟶ Rφ(Eₙ n)` is the given map in `D(R (n + 1))`.
   `hred` says its adjoint under `adjφ n` is an isomorphism. Thus it is exactly
   the transition-induced derived reduction, rather than a bare unrelated iso.
8. `hpc : IsPseudoCoherent (Eₙ 0)` uses the dependency's actual predicate.
9. The analogous `M n`, `adjq n` present derived tensor along each limit
   projection `q n`. These are choices of the operation already in the
   statement, not extra algebraic hypotheses.
10. `χ n` is the derived identification of restriction along `q n` with the
    composite along `φ n` and `q (n + 1)`. `hχ` fixes this identification:
    on every complex it is precisely `ModuleCat.restrictScalarsComp'`, through
    the recorded `mapDerivedCategoryFactors` isomorphisms. It therefore
    introduces no independently chosen action or twist.
11. The restricted derived tower has objects `Rq(Eₙ n)` and transitions
    `Rq_next.map (t n) ≫ (χ n).inv.app (Eₙ n)`. The `HasProduct` instance names
    its countable product. `E`, `pE`, `δ`, and `hE : IsDerivedLimitTriangle ...`
    give the node's chosen derived limit with its actual Roos projections.
12. The first conclusion is exactly `IsPseudoCoherent E`. The next conclusion
    says for every `n` that the adjoint of `pE ≫ Pi.π _ n` under `adjq n` is
    an isomorphism: these are the projection-induced derived comparisons.
13. The existential `Pₙ`, common integer `b`, and `βₙ` supply bounded-above
    representatives of every `Eₙ`. Their terms satisfy both `Module.Free`
    and `Module.Finite`, with no fixed finite rank imposed across degrees.
14. `uₙ` is a chain map into the restricted preceding complex; every component
    is surjective. `θₙ` is an actual chain isomorphism from ordinary termwise
    extension to `Pₙ n`. The degreewise `extendRestrictScalarsAdj.homEquiv`
    equation identifies its transpose with `uₙ`, so the reduction map is
    the one induced by the transition. The `Q.map (uₙ n)` equation, using
    `βₙ` and `mapDerivedCategoryFactors`, says it represents the given `t n`.
15. `P`, `p`, and their two compatible-tuple clauses say `P` is the termwise
    inverse limit: its projections commute with transitions and every
    compatible vector tuple in every degree has a unique inverse image.
    Since `p` consists of module-linear chain maps, both linear operations
    and the differential on this limit are the componentwise ones.
16. `P.IsStrictlyLE b` is the same upper cutoff. `Module.Free A (P.X i)` and
    `Module.Finite A (P.X i)` give bounded-above finite free over the actual
    inverse-limit ring. `β : Q.obj P ≅ E` represents the specified `E`.
17. The equation involving `Q.map (p n)`, the restriction factorization,
    `βₙ n`, and `β.hom ≫ pE ≫ Pi.π _ n` makes this representation respect
    every specified derived-limit projection.
18. `θ n` is a chain isomorphism `P ⊗_A R n ≅ Pₙ n`; its degreewise adjunction
    equation identifies it with the transpose of the actual chain projection
    `p n`. No unrelated isomorphism of these complexes suffices.
19. The auxiliary chain maps `η n` have, degree by degree, the ordinary
    scalar-extension unit. `γ n` identifies `(M n).obj (Q.obj P)` with
    `Q.obj (P ⊗_A R n)`. The unit equation normalizes this isomorphism against
    `adjq n` and the actual `mapDerivedCategoryFactors`; hence it is the
    ordinary-to-derived tensor comparison on this bounded-above free model.
20. The last equation says `γ.hom ≫ Q.map θ.hom ≫ βₙ.hom` equals transport by
    `M.map β.hom` of the adjoint of the specified `pE` projection. This is
    exactly the clause that the chain reductions represent the
    projection-induced derived comparison maps. It is stronger than merely
    recording the existence of isomorphic source and target objects, as the
    node explicitly requires.

Dependency declarations inspected and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; full signatures and docstrings read.
- `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`;
  its full definition is the existence of a bounded-above finite-free model.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle` (the specified Roos triangle) and
  `CategoryTheory.IsDerivedLimit` (the existential property).
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`:
  `SheafOfModules.derivedChangeOfRings`; the full theorem was read. It gives
  K-flat-derived tensor for general ringed sites; used for the ordinary-ring
  specialization in the node's proof, with the ordinary operation expressed
  by Mathlib's restriction/extension adjunction rather than copied.
- Mathlib `ModuleCat.ChangeOfRings`: `ModuleCat.extendScalars`,
  `ModuleCat.restrictScalars`, `ModuleCat.extendRestrictScalarsAdj`,
  `ModuleCat.restrictScalarsComp'`; the adjunction, units, and canonical
  composition isomorphism were inspected. `DerivedCategory.ExactFunctor`
  supplies `Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`.
- Proof-only imports cover the recorded
  `DerivedCategory.isPseudoCoherent_iff_of_surjective_nilpotent_kernel`,
  `CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`, and Mathlib's
  triangulated-category and triangle-isomorphism lemmas. Unstated proof
  dependencies have no module to import and are not replaced by new results:
  `lem-weil-pbc-nilpotent-marked-free-complex-lift`,
  `lem-weil-pbc-surjective-module-complex-tower-limit`,
  `lem-weil-pbc-scalar-extension-hom`,
  `lem-pc-ring-derived-map-representative`.

Edge cases checked: zero rings are allowed (`Nontrivial` is not assumed);
rank-zero modules and the zero complex are allowed; a complex can have
infinitely many nonzero negative degrees; the tower need not be eventually
constant and nilpotence exponents need not be uniform; no Noetherian,
finite-dimensional, adic, or characteristic condition was added. The tower
has its genuine first index, so no empty-index convention enters. The common
module universe is at least the ring universe and is freely enlargable.
There is no assertion that derived-limit isomorphisms are canonical.

Searches (2026-10-15):

- `msearch.py leanfinder`, query "Inverse limit of pseudo coherent complexes
  over surjective nilpotent ring quotients": 8 hits, local cohomology,
  ordinary adic completion, and the condensed projection lemma; none states
  reconstruction of the derived tower or its projection-induced maps.
- `msearch.py loogle`, query "ModuleCat.restrictScalars, DerivedCategory":
  0 hits.
- `msearch.py grep`, query `pseudo.?coherent|nilpotent.*complex`: 0 Mathlib hits.
- `msearch.py leansearch`, query "Derived inverse limit of pseudo coherent
  complexes over nilpotent quotient rings": unavailable, Internal Server
  Error. No verdict inferred from unavailability.
- `rg` in upstream `WeilConjectures` for pseudo-coherence and nilpotent
  complexes: only the finite-free proper direct-image discussion; no match.
  Exact item-id search in upstream source: no hits.
- `rg` in `lean/Sheaf` finds the existing pseudo-coherence definition and
  nilpotent-invariance theorem used here, together with other unrelated
  pseudo-coherence results. No inverse-ring reconstruction declaration.
- Exact proposed declaration/module search in `dag/lean_names_upstream.json`,
  Mathlib, upstream, and `lean/Sheaf`: no name collision.

No statement dispute or node fault found. The normalized adjunction data,
canonical restriction composition, and compatible-tuple universal properties
make explicit the operations in the natural statement; they do not introduce
private substitute objects.

Validation: server-only `scompile.py`, nice 19, two threads, default 60 seconds
per file. The complete statement compiled in 2.6 seconds, without errors or
warnings; the temporary `#check` and `example` probes were removed.

## Second reading by NV

I read the sandbox node and theorem independently against Stacks More on Algebra,
Tag 0CQF, including the introduction to the section on limits and the complete
proof. The node is explicitly the nilpotent-kernel, first-level-pseudo-coherent
case of that lemma. Its restriction from locally nilpotent kernels and the
source's eventual-pseudo-coherence alternative is already in the node, not a
restriction introduced by this Lean statement. No additional standing hypothesis
is needed. There is no statement correction, new node, or dependency module.

Object/hypothesis/conclusion inventory and matching verdicts:

1. A sequential system of commutative rings indexed from 1: `R`, its pointwise
   `CommRing` instances, and `φ` encode exactly this, with Lean 0 denoting 1.
   Successor maps determine all longer transitions. Pass.
2. Surjective transitions and nilpotent ideal kernels: `hsurj` and `hnil`.
   `IsNilpotent` here uses ideal multiplication, not elementwise nilpotence.
   Its possible exponent zero only occurs in the zero ring, where exponent
   one also works. Thus it is equivalent to the node's positive exponent. Pass.
3. The compatible-tuple limit ring: `A`, the ring maps `q`, `hq`, and `hlim`.
   The latter gives a unique scalar for every compatible tuple. These ring
   projections therefore identify A with the tuple subring, with componentwise
   operations; they do not impose completeness for an additional ideal. Pass.
4. Derived categories of modules: the imported `DerivedCategory`, `Q`, and
   explicit `HasDerivedCategory` instances implement the localization in
   def-weil-abstract-derived-category. `ModuleCat.{max u v}` admits the rings,
   their finite free modules, and arbitrarily larger module universes. Pass.
5. Derived tensor for transitions and projections: `L, adjφ` and `M, adjq`
   name left adjoints to the exact derived restriction functors. This universal
   characterization specifies derived scalar extension uniquely with its unit;
   such adjoints exist for ring maps, so this is presentation data, not a
   flatness or finiteness hypothesis. I read derivedChangeOfRings and its
   one-object-site interpretation; no competing tensor notion is defined. Pass.
6. Given objects and transition maps: `Eₙ` and `t` have precisely the prescribed
   types in D(R n) and D(R (n+1)), respectively. `hred` asserts invertibility
   of the transpose of this very `t`, not an unrelated identification. Pass.
7. Initial pseudo-coherence: `hpc : IsPseudoCoherent (Eₙ 0)` uses the exact
   predicate from RingPseudoCoherent: a bounded-above finite-free model. Pass.
8. Restriction of the tower to A: `χ` with `hχ` fixes the composition of
   restrictions to the identity-on-elements `restrictScalarsComp'`, via the
   genuine `mapDerivedCategoryFactors`. Thus the transitions in `hE` are
   exactly the restricted `t` maps; χ cannot introduce a twist. Pass.
9. The chosen derived limit and its projections: `HasProduct`, `E`, `pE`,
   `δ`, and `hE : IsDerivedLimitTriangle ...` specify precisely the recorded
   Roos triangle. The product is of the actual restricted Eₙ. Pass.
10. Main conclusions: `IsPseudoCoherent E` and the following `∀ n, IsIso ...`
    give pseudo-coherence and invertibility of the adjoint of
    `pE ≫ Pi.π _ n`. These are the specified projection-induced maps. Pass.
11. Finite-level models and common cutoff: existential `Pₙ`, `b`, and `βₙ`,
    with `(Pₙ n).IsStrictlyLE b`, `Module.Free`, and `Module.Finite`, give
    exactly bounded-above finite-free representatives, with one upper bound
    chosen for the entire tower. No uniform rank across degrees is imposed. Pass.
12. Strict transitions: `uₙ`, componentwise surjectivity, and `θₙ` give chain
    maps and ordinary reduction chain isomorphisms. The degreewise
    `extendRestrictScalarsAdj.homEquiv` equation fixes θₙ as the reduction of
    uₙ. The `Q.map (uₙ n)` equation identifies uₙ with t under βₙ and exact
    restriction. Thus the marking clause is retained. Pass.
13. Termwise limit: `P`, `p`, compatibility under uₙ, and degreewise unique
    realization of compatible vector tuples express precisely the inverse
    limit. Linearity and the differential are componentwise because p consists
    of linear chain maps and jointly determines every element. Pass.
14. Limit model: `P.IsStrictlyLE b`, finite freeness of every `P.X i`, and
    `β : Q.obj P ≅ E` give the claimed model. The equality with
    `β.hom ≫ pE ≫ Pi.π _ n` explicitly respects the specified projections. Pass.
15. Ordinary reductions of the limit: `θ` consists of chain isomorphisms;
    its degreewise adjunction equation makes each the transpose of p n,
    hence the actual projection-induced tensor map. Pass.
16. Identification with derived comparisons: `η` has exactly the ordinary
    extension unit in each degree; the equation involving the unit of adjq
    normalizes `γ` to the ordinary/derived tensor identification on P.
    The final equation transports θ and βₙ along γ and M.map β to precisely
    the transpose of the original derived-limit projection. No clause merely
    asserts existence of isomorphic objects. Pass.

Dependency reading: opened all four statement-dependency nodes and their recorded
modules. RingPseudoCoherent and DerivedLimit give exactly the definitions used;
DerivedChangeOfRings is the general ringed-site construction, and Mathlib Basic
is the actual localization. Also opened every proof-dependency record, the
Mathlib restriction/extension adjunction and composition isomorphism,
ExactFunctor's derived localization factorization, TensorProduct.Basic's
liftBaseChangeEquiv, and KProjective's Qh_map_bijective and bounded-above
projective criterion. No new-definition/dependency-module review under H12/H13
is needed because the delivery has neither.

Edge cases: zero rings and zero/rank-zero complexes are included, with no
Nontrivial instance; the nilpotent extension of a zero ring is again zero.
There is no lower bound on complexes and no uniform nilpotence exponent.
The natural-number tower is nonempty as required, so an empty index type is
not part of the node. There is no scheme, characteristic, or natural-number
rank parameter whose edge case could be excluded. The common integer cutoff
may be any integer. No Noetherian, adic, field, or finite-dimensional assumption
appears. Every variable and universe is bound explicitly; autoImplicit is false.
The arbitrary localization universe names the chosen derived categories.

Independent H4 searches, using different descriptions from the first worker:

- `msearch.py leanfinder`: "Compatible finite free complex models over an
  inverse system of nilpotent ring quotients recover a derived limit".
  Eight hits, all ordinary adic-completion compatibility/lifting lemmas;
  none concerns a derived tower of pseudo-coherent complexes.
- `msearch.py loogle`: `"DerivedCategory", "limit"`: zero hits.
- `msearch.py grep`: `finite.free.*limit|limit.*finite.free|reconstruct.*complex`:
  zero hits. Direct rg in all Mathlib and upstream WeilConjectures for
  pseudo-coherence, nilpotent complexes, and inverse reconstruction found
  only upstream Cohomology/DirectImage/FiniteFreeComplex. Reading it shows
  scheme direct-image models, not ring-tower reconstruction.
- Direct rg in project RingTheory pseudo-coherence modules found no competing
  reconstruction. I also opened StabilizedFiniteFreeTower: that is a direct
  system over a single ring with eventual degreewise stabilization and
  localized cohomology, not this inverse system of changing coefficient rings.

Mismatch found and repaired: the Worker report incorrectly classified
lem-weil-pbc-scalar-extension-hom and lem-pc-ring-derived-map-representative
as unstated. Both have Mathlib matches. Added proof-only imports
`Mathlib.RingTheory.TensorProduct.Basic` and
`Mathlib.Algebra.Homology.DerivedCategory.KProjective` to carry those proof
steps, as required by stage 2 §3(7). Only the marked-lifting and surjective-tower
lemmas in that worker list actually lack recorded declarations. No theorem
signature or node statement needed repair. The node's lean.statement was
checked byte-for-byte against the theorem signature and remains unchanged.
The sole local theorem has proof sorry; no data definitions, private copies,
local notation, or proofs were introduced. Source/blueprint docstrings contain
all six proof steps, and every Lean line is at most 100 characters.

Validation after repair: prescribed server-only scompile.py passed, nice 19,
two threads, 60 seconds per file. The delivered module compiled in 2.8 seconds,
with no errors or warnings (its side-only nilpotent-invariance import also
compiled in 1.3 seconds). The first compile command used a relative path from
the read-only repository and failed before invoking Lean; rerunning with the
absolute sandbox file path succeeded.
