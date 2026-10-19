## Worker report

The item is stated as `WeilConjectures.exists_compactSupportLerayFiltration` in
`Sheaf.Paper.CompactSupportLerayFiltration`. Its theorem proof is `sorry`.
The original statement and proof are unchanged. Two definition nodes supply the
missing canonical higher-image interface on the currently recorded common-stage
Weil heart. Their definitions contain real categorical constructions; all postponed
well-definedness/comparison results are named, documented declarations in their
owning node's `lean.declarations`.

Hypotheses and clauses, read against the original node:

- `D : FiniteFieldDatum.{u}` retains the chosen finite field, characteristic prime,
  degree, cardinality and algebraic closure. `l`, `[Fact l.Prime]` and `hl : l ≠ D.p`
  give precisely the allowed coefficient prime. `Ω : Type v` with `Field`,
  `Algebra (Padic l)` and `IsAlgClosure` gives the chosen coefficient closure.
  The scheme and coefficient universes remain independent.
- `X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))` and the Over arrows `h₀`, `g₀` retain their
  actual base structures. For each arrow, `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` on `.left` express separated finite type. The latter two instances
  on `Z₀.hom` and `Y₀.hom` express finite type over k₀. `QuasiSeparated` on these
  structure maps is equivalent to quasi-separatedness of the schemes over a field.
- No finite-type instance for X₀ is added as a theorem hypothesis.
  `zlSourceWeilHeart h₀` is literally the dependency's
  `sfCommonStageWeilSheaf`, with its finite-type and quasi-compact structure-map
  instances derived from `h₀.w` and composition. It changes neither objects nor
  arrows. The same induced instances are used in the two higher-image wrappers.
- `F : zlSourceWeilHeart ... h₀` is the specified constructible common-stage Weil
  sheaf, with no weight, mixedness, lissity, or irreducibility assumption. `n : ℕ`
  is exactly an integer n≥0.
- `ch`, `cg`, `cgh` are arbitrary compactification presentations of the three
  canonical operations. They are universally quantified, rather than a
  restrictive existence assumption: Nagata applies to the stated morphisms.
  The helper `zlWeilHigherShriek_compactification_independent` identifies any two
  choices by an isomorphism of actual Weil sheaves. In particular the statement
  neither requires a separated structure map over k₀ nor chooses a preferred
  compactification.
- `m : ℕ`, `G : Fin (m+1) → sfCommonStageWeilSheaf ... Y₀ Ω`, and
  `φ i : G i.castSucc ⟶ G i.succ` are the finite chain. `Mono (φ i)` makes it a
  chain of subsheaves, `IsZero (G 0)` gives its initial zero, and the final
  `Nonempty (G (Fin.last m) ≅ zlCompositeHigherShriek ... n F)` gives its specified
  endpoint. Endpoints are expressed by isomorphism in the heart, as usual for a
  categorical filtration.
- For each `i : Fin m`, the witnesses `a b : ℕ` with `a+b=n` give both nonnegative
  indices. `S` belongs to the same heart, `ι` targets exactly
  `R^a g! (R^b h! F)`, and `π` targets `cokernel (φ i)`, the actual adjacent
  quotient. `Mono ι ∧ Epi π` renders the two required arrows. All arrows are in
  the actual Weil category, so equivariance is part of their types.

Recorded dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `FiniteFieldDatum.geometricFiber`.
- Mathlib: `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsProper`,
  `QuasiSeparated` (the finite-type, proper and quasi-separated dependency matches).
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilFrobeniusPullback`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilForget`, `sfCommonStageWeilSheaf`,
  `sfWeilPrimeInvertible`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`,
  `sfCommonStageHeart`, `sfCommonStageStandardTStructure` and its heart properties.
- `Sheaf.Paper.IntegralRationalQbarCompactSupport`: `sfQbarCompactSupportValue`
  (including its actual integral and rational construction).
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`,
  `constructibleIntegralPullback`, `rationalDerivedPullback_existsUnique` and the
  common-stage object prescription.
- `Sheaf.Paper.IntegralPullbackComposition`: `integralPullbackComposition`, with its
  specified finite-reduction normalization; no bare natural isomorphism replaces it.
- `Sheaf.Paper.ConstructiblePullbackTExact`: the heart-preservation facts used in
  the well-definedness proof plans. Mathlib `Ind`, `AsSmall`, Yoneda, left Kan
  extension, adjoints and `Functor.rightDerived` are reused, rather than copied.
- `WeilConjectures.Compactification.Defs`: `AlgebraicGeometry.Compactification`.
  Its open part is automatically quasi-compact when the compactified morphism is,
  exactly as in this item, so the recorded compactification notion is respected.

The main module also imports the recorded t-structure/short-exact and exact-couple
proof dependencies that already have declarations. The lower-bound, operation,
shift-equivariance and qcqs composition obligations without declarations are
identified explicitly in its seven-step proof docstring; no assumed theorem was
used to construct the new definitions.

Edge cases checked: n=0 still allows the sole diagonal (0,0); a zero abutment may
have m=0; m=0 makes the adjacent-quotient clause vacuous and forces the endpoint to
be zero; an empty source gives zero higher images; the empty scheme does not need
any selected geometric point. The prime-unit helper uses `hl` explicitly, so the
forbidden case l=p is excluded. Frobenius may be semilinear over k: its naturality
is an equality of scheme maps, with no added k-linearity hypothesis. No separatedness
of X₀, Z₀ or Y₀ over k₀ is imposed. The ambient equivariant category allows arbitrary
Frobenius orbits, including the free sum of all iterates; it is not the ind-category
of finite-dimensional Weil representations.

Searches: actual wrapper searches are saved in `searches.jsonl` and copied into the
new records. Leray/filtration searches (LeanFinder, LeanSearch, Loogle
`"SpectralSequence"`, and Mathlib grep `Leray|higherLowerShriek|exists_filtration`)
found no exact common-stage statement. Source and side `rg` searches found the
upstream `AlgebraicGeometry.WeilSheaf.exists_filtration_higherLowerShriek_comp` in
`WeilConjectures.DeligneLaumon.Reduction.FormalSteps`. It is not attached as existing:
its concrete pro-etale Weil category is not the node's recorded common-stage heart.
The node itself already warns of this mismatch. Exact item-id grep in upstream
returned no hit. Further searches for equivariant ind-sheaves and canonical higher
compact-support images found only generic Ind/derived-functor infrastructure and
unrelated adic-completion lemmas. `tools/blueprint_refs.py search 'equivariant ind'`
and `search 'higher compact support'` returned zero blueprint-node matches.
Direct `rg` searches in both source trees for `zlIndWeilHeart`,
`zlWeilHigherShriek`, `def .*IndWeil`, `def .*WeilInd`, and
`def .*commonStage.*[Hh]igher` returned no hits. These search locations and results
are also explicit in the new node records. Direct DAG searches found generic
IndCons assertions, which are not this
Frobenius-equivariant specialization; their generic Ind notion is Mathlib's reused
`Ind`, not redefined here. No new definition is a copy of those assertions.

Validation: `scompile.py Q153 lem-zl-compact-support-leray-filtration` compiled
all three files separately in dependency order, including private-overlay, sandbox
and library checks: exit 0, no errors or warnings. Library passes took 27.2 s,
9.4 s and 2.8 s, respectively, under the unchanged 60-second limit. The final
delivery dry run additionally checks the complete packet. No statement correction
and no STATEMENT-DISPUTED issue.

The first dry run identified ten Prop-instance proofs written with the `instance`
keyword and `sorry`. Each is now a named `theorem` with the `instance` attribute;
the statement, source and full proof docstring are unchanged. Data-bearing
instances retain their explicit constructions. The repaired packet is recompiled
and checked by the prescribed delivery wrapper.

## New nodes

`def-zl-weil-ind-sheaf-category` owns `Sheaf.Paper.WeilIndSheafCategory`. It defines
all Frobenius pairs in the ind-completion of the actual underlying common-stage
heart, the fully faithful embedding of the existing Weil heart, and canonical
inverse image. Pullback composition is fixed on integral representatives by the
recorded finite-reduction-normalized integral comparison. The heart and ind
squares retain these components, with the Yoneda comparison equal to the inverse
Kan unit. Thus neither a natural isomorphism nor a Weil structure is picked from
an unconstrained nonempty type. Ordinary direct image and open extension are
selected only through their adjunction universal properties. The source is the
first blueprint proof paragraph and the proper/open sheaf-resolution construction
of SGA 4 XVII. The recorded LeanSearch/Loogle/grep searches and direct DAG/source/
side searches above found no existing declaration of this specialization.

`def-zl-weil-compact-support-cohomology` owns
`Sheaf.Paper.WeilCompactSupportCohomology`. It applies exact open extension before
taking the right derived functors of the proper direct image. This distinction was
checked against `literature/stacks-project/more-etale.tex`, compact-support section:
Rf! is not generally the right derived functor of ordinary f!. Injective resolutions
are Mathlib's actual construction in the ambient Grothendieck category. The named
representability theorem selects a preimage along a fully faithful embedding, so
the result, including its Weil action, is determined up to the isomorphism used in
the filtration statement. The comparison theorem identifies its underlying carrier
with cohomology of the actual integral/rational/common-stage compact-support value,
for every finite-stage integral model and geometric compactification. Proper/open
mates fix its natural action. This node also owns the elementary geometric/source
instance presentations needed to avoid extra hypotheses. Sources: the same blueprint
paragraph, SGA 4 XVII §5–6, and Bhatt–Scholze 6.7.6–6.7.7. Three-kind searches found
generic `Functor.rightDerived` and `totalRightDerived`, which are reused; none gave
the common-stage Weil-heart higher operation.

## Second reading by Q153

The dispatcher explicitly forbids starting other agents. This is an author second
reading; the maintainer supplies the independent review after delivery.

I read the original node, its seven proof steps, the source paragraph, and all three
modules again. The explicit scheme hypotheses match the node; the source heart
uses consequences of h, not an additional source finite-type assumption. The chain
has m arrows and m+1 vertices; `castSucc`/`succ` identify the correct adjacent quotient.
The iterated higher image has h in the inner and g in the outer operation. Both
indices are natural and sum to n. The final image uses h₀≫g₀. No weights appear.

For the definitions I checked that ind-completion precedes Frobenius fixed pairs,
so the ambient resolution category has the free equivariant objects needed for
forgetting to preserve injectives. I checked the normalizing equation for the
composition comparison on every integral representative and the Yoneda equation
for ind-squares. The chosen functors are adjoints or Kan extensions with specified
units, and the final representing object is along a fully faithful embedding.
Only proper direct image is derived. The comparison uses the recorded compact-support
value and standard t-structure, rather than substituting the upstream concrete Weil
category. The coefficient-prime lemma retains its characteristic exclusion explicitly.
Universe lifts raise sizes through `AsSmall.{0}` and impose no equality of u and v.
