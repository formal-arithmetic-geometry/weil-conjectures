## Worker report

This repairs the substantive H3/H4/H11 return on immutable head
`bac63c039a473d7c67ded7d5a3e5874aa028c3ee`. The retained packet was first tested with
`deliver2.py --no-push`: its preflight and compilation passed, but rereading it against
`review.md` confirmed the mathematical defects. Mechanical acceptance did not resolve them.
The faulty structures have been replaced by prescribed constructions in
`lean/Sheaf/AlgebraicGeometry/LogRegularPair.lean`. The informal statement is unchanged;
only the item's `lean` record changes. No new nodes or dependency-record repairs are needed:
the helpers specialize existing Mathlib constructions to this node's own divisorial notion.

I read the source PDF, PDF pages 75–77, printed pages 69–71: ILO Exposé VI §§1.1–1.4
and the examples in §1.5. The source requires the étale log structure, strict local rings,
the actual nonunit ideal and characteristic-group rank, and exactly the specified
triviality open. The node uses the equivalent Krull-dimension formula described in its
stage-1 review. Nothing here changes that statement or the source hypotheses.

Clause-by-clause rendering:

1. The pair is given by `(V U : Scheme.{u})`, `j : U ⟶ V`, `[IsOpenImmersion j]`,
   `[IsLocallyNoetherian V]`, and `(_hU : DenseRange j)`. The closed boundary `Z` is
   the complement of the image of this open immersion. No excellence, finite type,
   separatedness, or characteristic condition is imposed. The density argument is a
   bound proof of the source hypothesis; its underscore suppresses the unused-proof
   warning without removing the hypothesis.

2. `divisorialSections j W` is the comap of the unit submonoid along the ring map
   `(pullback.fst W.hom j).appTop.hom`. Membership is therefore **equivalent** to
   becoming invertible on `W ×[V] U`. It is not a chosen submonoid with only one
   implication. `divisorialRestriction j f` is pullback along `f.left`; the proof
   that it preserves divisorial sections uses the canonical map between the two
   scheme-theoretic pullbacks. `divisorialLogPresheaf j` packages these monoid maps,
   their identity law and composition law. `divisorialStructuralMap j` has component
   exactly `Submonoid.subtype`; naturality is proved by reflexivity on the actual
   pullback functions. All sections, multiplication, restrictions and the structural
   inclusion thus have real prescribed data.

3. The pair predicate includes
   `Presheaf.IsSheaf V.smallEtaleTopology (divisorialLogPresheaf j)`.
   `divisorialLogSheaf j h` bundles precisely that presheaf with the descent proof
   `h`. This proof supplies no data and selects no sections or maps. Expressing
   descent as a property in the predicate avoids a hidden postponed theorem inside
   a definition; it is the source's requirement that `M` be the divisorial **sheaf**.
   There is no existentially chosen presheaf, arbitrary restriction family, or
   arbitrary chart proposition.

4. `strictLocalRing V t` is
   `((Scheme.pointSmallEtale t).presheafFiber (A := CommRingCat)).obj
   V.etaleStructurePresheaf`. `strictLocalGerm V t W w` is exactly
   `Point.toPresheafFiber W w V.etaleStructurePresheaf`. The recorded point has
   fibres consisting of lifts of the geometric point to étale neighbourhoods;
   `presheafFiber` is the colimit over their opposite category. Thus this is the
   strict local ring from the node, retaining the field and the geometric point,
   rather than `V.presheaf.stalk x`. The latter expression does not occur.

5. `divisorialStalk j t` is the supremum of the submonoid images of
   `divisorialSections j W` under all the prescribed pointed-neighbourhood ring
   germs. In this filtered colimit this supremum is the union of those images:
   any finitely many germs have a common refinement and can be multiplied there.
   It is consequently the divisorial stalk inside the strict local ring. The
   inclusion is legitimate: filtered ring colimits are created on underlying
   sets, and equality of germs means equality on a further neighbourhood; the
   same further neighbourhood is used for divisorial sections. This is the usual
   subobject presentation of the geometric stalk of a subsheaf. `divisorialGerm`
   is the canonical restricted germ homomorphism into this prescribed submonoid.
   No arbitrary stalk, unrelated ring, or separate colimit model is chosen.

6. The existential `h` in the pair predicate is only the proof that every strict
   local ring unit belongs to `divisorialStalk j t`. Since the structural map is
   an inclusion, its inverse image of units is the unit submonoid. Both a ring
   unit and its inverse belong to the stalk, so its intrinsic unit group maps
   bijectively to the ring unit group. This is the log-structure unit condition.
   `divisorialUnitsIn L h` is its prescribed inclusion, with value `a.1` on a ring
   unit `a`; it is not an arbitrary map.

7. `IsFineSaturatedMonoid P` uses a finite generating set, injectivity of the
   **canonical monoid homomorphism** `Algebra.GrothendieckGroup.of`, and closure of
   its image under positive roots in that same group completion. The quantified
   natural number `n` with `0 < n` is the positive integer of the saturation
   condition, written multiplicatively as `g ^ n`. This rules out the returned
   absorbing-zero counterexample; no underlying-set embedding is used.

8. `HasDivisorialFineSaturatedCharts j h` says that **each geometric point** has a
   pointed étale neighbourhood `W`, a commutative monoid `P` satisfying the actual
   fine-saturation predicate, and `β : P →* divisorialSections j W`. For **every**
   geometric point of `W` (encoded by `t'` and its lift `w'`), its stalk chart is
   `(divisorialGerm j t' W w').comp β`. Thus there is one chart on an étale
   neighbourhood, not unrelated chart choices at individual stalks. The chart map
   into the sheaf on this neighbourhood is given on further objects by the already
   prescribed restrictions of these sections. The `W`'s cover because every
   geometric point has a lift to one.

9. For a stalk chart `β : P →* L`, its structural composite `α` is
   `L.subtype.comp β`. `divisorialChartCongruence β` is `conGen` of the relations
   `(p,1) ~ (1,a)` exactly when `(β p).1 = a.1` for `a : Aˣ`. These are exactly the
   identifications along `α⁻¹(Aˣ)`. `divisorialChartPushout β` is the **actual**
   congruence quotient of `P × Aˣ` with its Mathlib commutative-monoid structure;
   the product is the coproduct of commutative monoids. `IsDivisorialStalkChart`
   requires surjectivity of the prescribed product homomorphism
   `β.coprod (divisorialUnitsIn L h)` and equality of its kernel congruence with
   `divisorialChartCongruence β`. By the quotient universal property these are
   exactly bijectivity of the induced pushout map, hence its being an isomorphism.
   A mere unrelated isomorphism or an arbitrary alleged pushout is insufficient.

10. The triviality clause is
    `divisorialStalk j t = IsUnit.submonoid (strictLocalRing V t) ↔
    (Scheme.SpecToEquivOfField Ω V t).1 ∈ Set.range j`.
    This compares the stalk with **the ring units**, not with the whole
    multiplicative monoid of the ring, and gives exactly the open complement.

11. The characteristic monoid is Mathlib's `Associates L = L / Lˣ`. By the log
    unit condition in point 6 this is exactly `M_t / Aˣ`. Its group completion is
    `Algebra.GrothendieckGroup (Associates L)`. `Additive` supplies its abelian
    group notation, and `TensorProduct ℤ ℚ (...)` forms the required rational
    tensor product. `divisorialCharacteristicRank L` is the **actual**
    `Module.rank ℚ` of this tensor product projected by `Cardinal.toENat` to `ℕ∞`.
    Fine saturated charts make the rank finite. Using `toENat` also retains the
    correct infinite-dimension value; it does not silently turn infinity into zero.
    There is no rank witness or arbitrary numeric field.

12. `divisorialNonunitIdeal L` is
    `Ideal.span {a | ∃ m : L, ¬ IsUnit (m : A) ∧ (m : A) = a}`.
    This is exactly the ideal generated by the structural images of log nonunits,
    since the unit condition identifies intrinsic log units with ring units.
    The last two clauses require `IsRegularRing (A ⧸ divisorialNonunitIdeal L)`
    and `ringKrullDim A = ringKrullDim (A ⧸ divisorialNonunitIdeal L) +
    (divisorialCharacteristicRank L : WithBot ℕ∞)` for the prescribed strict local
    ring and stalk. Neither the ideal nor the rank is existentially chosen.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; its recorded
  affine-cover equivalent gives the node's local Noetherian condition.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` and `.Sites.Etale`:
  `Scheme.Etale` and `Scheme.smallEtaleTopology` (objects, morphisms and the
  jointly-surjective topology). Étale fibre products are actual scheme pullbacks.
- `Mathlib.AlgebraicGeometry.ResidueField` and `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `Scheme.SpecToEquivOfField` and `IsAlgClosed`. Algebraically closed test fields
  and all visible variables/universes are explicitly bound.
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint` and
  `Mathlib.CategoryTheory.Sites.Point.Basic`: `Scheme.pointSmallEtale`,
  `Point.presheafFiber`, and `Point.toPresheafFiber`. The recorded
  `Point.sheafFiber` restricts this same `presheafFiber` to sheaves, so the
  recorded geometric-stalk construction is reused, not reimplemented.
- `WeilConjectures.AlgebraicGeometry.Sites.Gm`: `Scheme.etaleStructurePresheaf`,
  whose values are `Γ(W.left, ⊤)` and whose sheaf property is already proved
  upstream. I also read the live `StrictHenselization` module through
  `scompile.py --source`: `geometricStalkFunctor` is the same recorded fibre
  interface, while `strictHenselization` uses the cofinal affine index model.
  This delivery uses the point-fibre model already specified by the dependency.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularRing`;
  `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` in `WithBot ℕ∞`.
- Algebraic helpers reuse `IsUnit.submonoid`, `Associates`,
  `Algebra.GrothendieckGroup`, `conGen`/`Con.ker`/`Con.Quotient`, `TensorProduct`,
  `Module.rank` and `Cardinal.toENat`, rather than replacing these Mathlib notions.

Edge cases checked by unfolding the clauses, not by adding Lean theorems:

- Empty boundary, `j = 𝟙 V`: the canonical section monoids and geometric stalks
  are exactly units; the characteristic group is zero and the nonunit ideal is
  zero. The condition is ordinary regularity. In particular the affine cusp
  counterexample from the return is excluded: one cannot choose its maximal
  ideal or manufacture a dimension witness.
- The origin as boundary in the regular affine plane: the divisorial sheaf is
  trivial across the codimension-two boundary. The exact triviality-locus
  equivalence fails at the origin, excluding the returned counterexample.
- A normal crossing of two divisors: the characteristic monoid at the crossing
  is `ℕ²`; the actual group completion has rational rank two, and the generated
  ideal is the two boundary parameters. Choosing zero ideal and zero rank is
  impossible.
- Empty scheme: no geometric test point exists, so the chart, unit, triviality,
  and local conditions are vacuous as they should be. The canonical sheaf clause
  still has its usual meaning. Rank zero and the zero-ring Krull-dimension
  convention retain Mathlib's values; no nonzero-ring hypothesis was added.
- The two-element absorbing-zero monoid cannot inject by its canonical monoid
  homomorphism into its group completion. This directly repairs the fine
  saturation defect in the review.

Searches made for an existing complete definition:

- `msearch.py leanfinder`, query `divisorial log structure fine saturated chart log
  regular pair`: eight unrelated number-field logarithmic-embedding hits; no match.
- `msearch.py leansearch`, query `fine saturated monoid chart divisorial log structure
  logarithmic regular pair`: eight hits about division pairs, localization and
  subalgebra saturation; none defines this notion.
- `msearch.py loogle`, query `"LogRegular"`: zero hits.
- `msearch.py grep`, query `Divisorial|LogStructure|SaturatedMonoid` in
  `AlgebraicGeometry`: zero hits.
- Direct `rg` over upstream `WeilConjectures`, project `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no complete divisorial log-regular definition;
  the nodal-resolution file only mentions the intended chart lemma in a docstring.
  Searching the item id in upstream likewise found no declaration. Algebraic
  source searches found and reused the Mathlib constructions listed above.

There is no disputed source statement, no statement correction, no new axiom, no
postponed theorem, and no `sorry`. The short proofs inside the functor/map definitions
are only their construction laws. Every declaration has its source and blueprint
citation. The node's `lean.statement` is copied byte-for-byte from the final multiline
signature, and `lean.declarations` lists all the module's declarations.

## Second reading by Q116

This is a separate rereading by the same worker, as the dispatcher explicitly prohibits
starting other agents. I do not claim an independent agent's approval.

With the complete node, source and file open, I checked the eight numbered findings of
the return. The scheme/open/density/local Noetherian hypotheses remain explicit.
The section condition is an exact comap, the restrictions and structural inclusion
are constructed, and descent is a property of that fixed presheaf. The log unit map
is the subtype map, not a chosen map. Fine saturation uses the canonical group
completion. Charts are on étale neighbourhoods and hold at every geometric point of
the neighbourhood; their pushout is the actual congruence quotient and the prescribed
map must have exactly its kernel and be surjective. The triviality test compares with
`IsUnit.submonoid A`, not `⊤`. The strict ring and all germs retain `t` through
`pointSmallEtale`; no ordinary local stalk is used. The characteristic group is the
group completion of the quotient by intrinsic units, identified with ring units by
the log unit condition. Its rank is computed after tensoring with ℚ. The ideal is
literally the span of the structural images of nonunits. Finally the regularity
and dimension clauses use those exact invariants.

This rereading found and removed further errors in the intermediate repair: a map
labelled “pushout” without its actual relations, a free rank field, and a triviality
comparison with all ring elements. None remains in the final file. In contrast to
the returned H11 report, the account above distinguishes constructed data, required
properties, and mathematical edge-case checks; it does not treat clean compilation
as evidence of semantic correctness.
