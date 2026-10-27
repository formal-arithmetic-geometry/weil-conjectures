## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricTriplesColimitComparison` states
`AlgebraicGeometry.Scheme.geometric_triples_colimit_comparison`, with `sorry` as its
only postponed proof. Its eight supporting definitions give the prescribed residue
map and geometric point, the map on each chart, point evaluation, triple residue
maps, and the two exact compatibility predicates. They contain real terms, not
choices of unspecified maps or postponed data. They belong to the canonical
comparison of this node and are all listed in `lean.declarations`.

Sources read: Stacks `etale-cohomology.tex`, `lemma-describe-etale-local-ring`
(Tag 04HX), especially the final paragraph of its proof; `algebra.tex`,
`lemma-map-into-henselian-colimit` (08HR) and `lemma-uniqueness-henselian`
(08HT); `fields.tex`, definition and existence of algebraic closures (09GS,
09GT). The declaration docstring gives all seven proof steps from the node,
including the field argument, coprojection uniqueness, two henselian lifts,
uniqueness of their composites, representative transport, and closure existence.
The node statement, dependencies and proof have not been changed.

Hypotheses, in the order of the node:

- The commutative local ring is `(A : CommRingCat.{u}) [IsLocalRing A]`.
  Its specified residue field is exactly `IsLocalRing.ResidueField A`.
- The separable residue closure is `(K : Type u) [Field K]` with
  `[Algebra (IsLocalRing.ResidueField A) K]` and
  `[IsSepClosure (IsLocalRing.ResidueField A) K]`.
- The extension is `(Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]`.
  The further algebra structure over the residue field and its scalar tower
  specify the composite embedding, imposing no additional field condition.
  In particular there is no hypothesis that Ω/K is algebraic or that k is perfect.
- `geometricTriplesBaseResidue A K` is literally the residue quotient followed
  by the algebra map to K. `geometricTriplesPoint A K Ω` is `Spec.map` of its
  composite with `algebraMap K Ω`. Thus x is constructed, never arbitrary.
- `C : Type v` is an arbitrary commutative henselian local A-algebra,
  with `[IsLocalHom (algebraMap A C)]` and the recorded universe-independent
  ind-etale predicate `hC : RingHom.IndEtaleAcrossUniverses (algebraMap A C)`.
- `q : C →+* K`, `hq`, `hker`, and `hqa` render respectively the specified
  map, its surjectivity, its maximal-ideal kernel and its restriction to A.

Conclusions, clause by clause:

- The first conjunct says, element by element, that
  `separableClosure (IsLocalRing.ResidueField A) Ω` is exactly the range of
  `algebraMap K Ω`.
- The second conjunct quantifies over every ring-written affine pointed
  neighbourhood `n : strictHenselizationNeighbourhoods x` and every element
  of the residue field at its point. Its map to Ω is the second component
  of `SpecToEquivOfField Ω _ n.2.left`; the asserted membership in the
  range of `algebraMap K Ω` is precisely the image-in-K assertion.
  The recorded fully faithful essentially surjective affine inclusion means
  these n cover all affine pointed neighbourhoods up to pointed isomorphism.
- `J : Type u`, `[SmallCategory J]`, `r : J ⥤ strictHenselizationNeighbourhoods x`
  and `[r.IsEquivalence]` describe any small category of representatives.
  Its ring diagram is exactly `r.op ⋙ strictHenselizationCoordinateRings x`.
  With `J = SmallModel _` and `r = (equivSmallModel _).inverse`, this is
  definitionally `strictHenselizationAffineDiagram x`, and its colimit is
  the recorded `strictHenselizationRing x`. Quantifying over every r states
  representative independence without a colimit over a large category.
- `c` with `_hc : IsColimit c` is any presentation of D_A as the ring
  colimit of the recorded triple diagram. `qA` with `_hqA` specifies its
  induced residue map on every coprojection. This is not an unconstrained
  map or an additional geometric assumption: it spells out the colimit and
  its induced map already introduced in the node. Their existence is supplied
  by the recorded strict-henselization-triples theorem.
- For each `j`, the existential `t` and `hB` give t_V with ring exactly Γ(V),
  and `GeometricTriplesRepresents` fixes its chart map and its map to Ω.
  A field-valued ring map uniquely determines its kernel prime and induced
  residue embedding, so these equations identify precisely q_v and φ_v;
  the triple structure supplies etaleness, the prime-over-base condition,
  and residue compatibility. `geometricTriplesResiduePoint A K` reads the
  base prime and embedding from the prescribed A → K. This prime is the
  maximal ideal, since A → K is its residue quotient followed by an embedding.
- The existential b is characterized by the structure-map equation on every
  coprojection: `geometricTriplesChart (r.obj j) ≫ colimit.ι ... (op j) = b`.
  This specifies the canonical A-structure, rather than postulating an arbitrary one.
- `i : C ≃+* ↥(colimit ... : CommRingCat.{u})`, together with
  `i.toRingHom.comp (algebraMap A C) = b.hom`, is exactly an A-algebra
  isomorphism. The following equality of ring maps states
  K → Ω composed with q composed with i inverse composed with λ_V equals
  the map induced by the lifted point. The quantified i' clause proves
  uniqueness among exactly the A-isomorphisms satisfying this condition.
  A heterogeneous ring equivalence preserves the independent universe v of C;
  using a categorical ring isomorphism here would incorrectly identify v with u.
- `GeometricTriplesCoprojections r c g` spells out `g μ_(t_V) = λ_V`, with
  only the equality transport between the displayed coordinate rings.
  `IsIso g` and `∀ t, t.α ≫ c.ι.app t ≫ g = b` state invertibility and
  A-linearity. `q.comp (i.symm.toRingHom.comp g.hom) = qA.hom` is precisely
  `q i⁻¹ g = q_A`. The final universally quantified g' is a ring map,
  with no A-linearity or invertibility assumed: uniqueness is among ring maps,
  exactly as requested, not merely among algebra isomorphisms.
- The last conjunct is existence of a field L, K-algebra structure and
  `IsAlgClosure K L`. Every algebraic closure is included in the already
  universal assertion for algebraically closed Ω; algebraicity is not imposed
  there. Thus the final allowance for any algebraic closure is retained.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.SpecToEquivOfField`, and evaluation.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem`, with Mathlib's `IsSepClosure`
  as the actual separable-closure predicate. Its imported `separableClosure`
  is the exact relative-closure declaration from the dependency's Mathlib match.
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: the category of elements of
  `pointSmallEtale x`. The recorded `strictHenselizationNeighbourhoods` and
  `strictHenselizationAffineInclusion_isEquivalence` use this same category.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `HenselianLocalRing`
  (Mathlib), and the recorded strictly henselian terminology.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`:
  `RingHom.IndEtaleAcrossUniverses`, canonically defined using `RingHom.ulift`
  and the existing upstream ind-etale predicate.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `strictHenselizationNeighbourhoods`, `strictHenselizationCoordinateRings`,
  `strictHenselizationAffineDiagram`, `strictHenselizationRing`, and the
  representative-equivalence construction. The theorem's universal r form
  specializes definitionally to this construction, without a new henselization.
- `WeilConjectures.AlgebraicGeometry.EtaleResidueTriples`:
  `EtaleResidueTriple` and `etaleResidueTriplesRingDiagram`; both are used directly.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`:
  `AlgebraicClosure`, `IsAlgClosure`, `IsAlgClosed`, and closure existence.
- Proof imports: `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`
  (`etale_local_ring_triples`),
  `WeilConjectures.RingTheory.StrictHenselizationTriples`
  (`strictHenselization_triples`), and
  `WeilConjectures.RingTheory.MapIntoHenselianColimit`
  (`Algebra.map_into_henselian_colimit`). Mathlib's colimits, filtered finality
  and equivalence-colimit declarations are supplied by these imports.

Edge cases checked before writing and on rereading:

- Imperfect k: IsSepClosure, not IsAlgClosure, is required for K; there is
  no perfectness or purely inseparable triviality assumption.
- Ω may have positive transcendence degree over K; only IsAlgClosed is used.
- A may be a field, k separably closed, or C = A when its hypotheses hold;
  there is no dimension, nonzero maximal ideal or proper extension assumption.
- The zero ring is correctly excluded by IsLocalRing, as required for a local
  ring with a residue field; fields K and Ω are nontrivial.
- An empty representative category cannot be equivalent to the neighbourhood
  category, which contains the identity neighbourhood. No artificial nonemptiness
  hypothesis is added.
- Coprojection compatibility is not vacuous: the theorem explicitly supplies
  t_V for every representative, and tests every triple satisfying its exact equations.
- The universe of C is independent. Site rings and fields use the existing
  dependencies' common ambient universe u; all these objects can be put in a
  common ambient universe without restricting their cardinalities. The index
  category is small in that same universe.

Searches made (through the prescribed msearch wrapper unless noted):

- `leanfinder`: “A henselian local ind-etale algebra with separably closed
  residue field is uniquely the colimit of affine pointed etale neighbourhoods,
  compatibly with residue triples”. Eight hits: standard-etale presentations,
  lifts and residue maps; none is this recognition and comparison statement.
- `loogle`: `Algebra.Etale, HenselianLocalRing`. Zero hits.
- `grep`: `strictHensel|residue.*[Tt]riple|pointed.*[Cc]olimit`. Four hits,
  in `AlgebraicGeometry/PullbackCarrier` and `Galois/Prorepresentability`;
  no matching statement.
- `leansearch`: “A local henselian ind-etale algebra with residue field a
  chosen separable closure is the strict henselization colimit of geometric
  etale neighbourhoods”. Eight hits, including IsSepClosure.recOn,
  HenselianLocalRing.TFAE, HenselianRing, and etale field decompositions;
  no matching recognition or coprojection comparison.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  geometric/triple/colimit, residue triples, strictHenselizationAffine and the
  item ID. Existing nearby results are `etale_local_ring_triples`,
  `strictHenselizationPointEvaluation_comparison`, `strictHenselizationLocalStructure`,
  and the pointed-presentation comparisons. Their full signatures do not give
  recognition of arbitrary C, the specified K, both uniqueness clauses, and
  all coprojection equations together. They are not an existing match.
- `rg` for all nine proposed full declaration names in Mathlib and both project
  roots found no declaration collision. No missing independent notion or
  unusable dependency required an extra node or a dependency-record repair.

## Second reading by Q20

This is an independent clause-by-clause reading by the maintainer reviewer (2026-10-24). It
replaces the delivered section, which was the worker's own rereading (delivery-errors H11).
I read it with the node, the Stacks places and the Lean file open. The Lean and the records
are unchanged.

Sources: Stacks `etale-cohomology.tex` l. 4255-4300, Tag 04HX `lemma-describe-etale-local-ring`
(the separable algebraic closure κ^sep ⊂ κ(s̄), the neighbourhood colimit, and the triple
colimit over (B, q, φ)), and `algebra.tex` l. 42881-42919, Tags 08HR/08HT (unique R-maps from
ind-étale algebras into henselian local rings, and the recognition isomorphism compatible
with the maps to K).

Node statement as a list, with its Lean rendering:

1. (A, m, k) local, k its residue field: `(A : CommRingCat.{u}) [IsLocalRing A]` with
   `IsLocalRing.ResidueField A`. Correct.
2. K/k a separable closure [def-pd-separable-closure]:
   `[Algebra k K] [IsSepClosure k K]`, the Mathlib predicate the dependency module uses. It
   does not assume IsAlgClosure, so imperfect k is covered. Correct.
3. Ω any algebraically closed extension of K: `[Algebra K Ω] [IsAlgClosed Ω]`. The extra
   `[Algebra k Ω] [IsScalarTower k K Ω]` only names the composite embedding. Every
   (Ω, K → Ω) admits it, so this is not an extra hypothesis. Ω/K is not assumed algebraic.
   The universe Ω : Type u is forced by the recorded `strictHenselizationNeighbourhoods`
   (s : Spec Ω ⟶ S in Scheme.{u}). It is the ambient convention, not a silent restriction.
4. x induced by A → k → K → Ω: `geometricTriplesPoint = Spec.map (residue ≫ algebraMap k K ≫
   algebraMap K Ω)`. This is constructed, not arbitrary. Correct.
5. The relative separable closure equals the image of K: conjunct 1,
   `z ∈ separableClosure k Ω ↔ z ∈ range (algebraMap K Ω)`. This is the exact Mathlib match
   of def-weil-pbc-relative-separable-closure. Correct.
6. κ(v) → Ω lands in K for every affine pointed neighbourhood: conjunct 2. It ranges over
   every ring-written neighbourhood n and every z in the residue field at
   `(SpecToEquivOfField Ω V n.2.left).1`, with the embedding `.2`. Every affine pointed
   neighbourhood is pointed-isomorphic to a ring-written one
   (`strictHenselizationAffineInclusion_isEquivalence`), and the property is invariant
   under isomorphism. Correct.
7. C a henselian local A-algebra, A → C local and ind-étale: `C : Type v`,
   `[HenselianLocalRing C] [Algebra A C] [IsLocalHom (algebraMap A C)]`, and
   `hC : RingHom.IndEtaleAcrossUniverses` (the recorded def-weil-pbc-ind-etale-algebra
   declaration, a §1(B) universe repair). The universe of C is independent, which is more
   general than the node. Correct.
8. q : C → K surjective, ker q = m_C, q|_A = A → k → K: `q`, `hq`, `hker`, and `hqa` against
   `geometricTriplesBaseResidue` (literally residue ≫ algebraMap). Correct.
9. G = A^sh_{Spec A,x} with coprojections λ_V and structure map b: the statement quantifies
   over every small J with an equivalence `r : J ⥤ strictHenselizationNeighbourhoods x`, and
   G = `colimit (r.op ⋙ strictHenselizationCoordinateRings x)`. With J = SmallModel and
   r = (equivSmallModel _).inverse, this is definitionally `strictHenselizationAffineDiagram`,
   whose colimit is the recorded `strictHenselizationRing` (I checked the source of
   StrictHenselization.lean l. 109-133). This also covers "independent of the chosen small
   representative category". b is existential but characterized by
   `chart_j ≫ ι_j = b` for all j. J is nonempty, because it is equivalent to a category
   containing the identity neighbourhood, so b is unique. This is not an arbitrary map. The
   def node itself records no b declaration. (`strictHenselizationStructuralMap` is a scheme
   map on the SmallModel colimit and is not cited by the node.)
10. There is exactly one A-algebra isomorphism i : C ≅ G with q i⁻¹ λ_V followed by K ↪ Ω
    equal to the map induced by x_V: `∃ i : C ≃+* G` with `i ∘ algebraMap = b`, and for all j,
    `algebraMap K Ω ∘ q ∘ i.symm ∘ ι_j = geometricTriplesEvaluation (r.obj j)`
    (= v.appTop ≫ ΓSpecIso, the same formula as the legs of `strictHenselizationPointCocone`).
    Uniqueness is stated among all i' with the same two conditions. A ring equivalence
    rather than a categorical iso keeps v free. Correct, neither weaker nor stronger.
11. t_V = (Γ(V), q_v, φ_v) with the chart structure map is an étale residue triple: for each
    j there exist t and `hB : t.B = Γ(V)` with `GeometricTriplesRepresents`, which says
    `t.α = chart` and `ψ_t ≫ (K→Ω) = evaluation`. Since K → Ω is injective, ψ_t is
    determined. Its kernel is q_t, and φ_t is determined on Frac(B/q_t). So t is exactly
    t_V, and its existence asserts that t_V is a triple. Correct.
12. D_A is the triple colimit with μ_t and the induced residue map q_A: any `c` with
    `IsColimit c` of `etaleResidueTriplesRingDiagram A p K χ`, where (p, χ) is read from the
    closed point by `SpecToEquivOfField`, and qA is characterized by `ι_t ≫ qA = ψ_t`
    (`geometricTriplesTripleResidue` is the same ψ as `strictHenselization_triples`). Such a
    c exists by the recorded strict-henselization-triples theorem, so the clause is not
    vacuous. Correct.
13. There is exactly one ring map g : D_A → G with g μ_{t_V} = λ_V. It is an A-isomorphism
    and q i⁻¹ g = q_A: `∃ g` with `GeometricTriplesCoprojections r c g`, `IsIso g`,
    `∀ t, t.α ≫ ι_t ≫ g = b`, `q ∘ i.symm ∘ g = qA`, and uniqueness among all ring maps g'
    satisfying only the coprojection predicate. The uniqueness of g does not depend on i, so
    there is no nested-∃! weakening. Correct.
14. Existence of an algebraic closure of K: last conjunct, `∃ L, IsAlgClosure K L`. Any
    algebraic closure is algebraically closed, so it is already covered by item 3. Correct.

Edge cases: A a field (m = 0); k separably closed (K = k possible); k imperfect; Ω
transcendental over K; C = the triple colimit itself. None is excluded. The empty J is
impossible under the equivalence. The zero ring is excluded by IsLocalRing, as in the node.
Universes: A, K, Ω and J are in u (forced by the dependencies), and C is in an independent v.

Records: the statement field is verbatim the file signature (checked by script). The
stmt_deps cover every notion used: the residue field, IsSepClosure, separableClosure,
pointed neighbourhoods, HenselianLocalRing, IndEtaleAcrossUniverses,
strictHenselizationCoordinateRings/Ring, EtaleResidueTriple/ringDiagram, and
IsAlgClosed/IsAlgClosure. The helper definitions have real bodies and source and blueprint
docstrings, and the theorem docstring carries the seven proof steps. The proof is only
`sorry`. There are no new nodes, and the non-lean fields of the node are identical to live.

Searches: rg in lean/WeilConjectures and lean/Sheaf for `strictHenselization*` definitions
(StructuralMap, PointCocone/PointEvaluation, RepresentativeIso, Presentation) and for the
triples theorems. None states recognition of an arbitrary C together with the g/i
comparison, so this is not an existing statement.
