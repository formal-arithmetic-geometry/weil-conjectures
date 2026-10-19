## Worker report

The delivery defines `AlgebraicGeometry.Scheme.CompleteCoefficientDatum` and its
reduction construction in `Sheaf.Paper.CompleteCoefficientDatum`. The auxiliary
constructions and all the identities are listed in `lean.declarations`. There
are three dependency modules, described below. No theorem is proved: every
new theorem has proof `by sorry`, a source, the owning blueprint id, and a
natural-language proof. Definitions contain actual data.

This supersedes the old WAITING report. The genuine prerequisite
`lem-pur-kflat-change-of-rings` now has the published declaration
`SheafOfModules.changeOfRings_isKFlat_of_flat_terms`. It is used by the stated
`adicReductionModel_isKFlat`; there is no further prerequisite wait.

Clause-by-clause rendering of the item:

- Scheme and small pro-etale site: `(X : Scheme.{t})`, `X.ProEt`, and
  `ProEt.topology X`, exactly the site used by the recorded
  `Scheme.proEtaleDerivedCategory`. Objects remain in universe `t+1`, morphisms
  in `t`. There is no site replacement or equality of these universes.
- Constant coefficients: `adicConstantRing X A` is the constant sheaf of
  `CommRingCat.of (ULift A)`; `adicModuleRing` forgets commutativity using the
  recorded construction. `adicConstantMap` applies the constant-sheaf functor
  to `RingHom.ulift φ`; `adicModuleMap` forgets commutativity of that map.
  These are abbreviations/maps of the existing constant-sheaf construction,
  not another definition of the site or of its derived category.
- Commutative ring: `[CommRing Λ]`. Noetherian: the datum's `noetherian` field
  is `IsNoetherianRing Λ`. The chosen ideal is its `ideal : Ideal Λ` field.
  Finite generation, equivalently the existence of a finite list
  `(f₁,...,fᵣ)`, is `finitelyGenerated : ideal.FG`. The list itself is not used
  by any subsequent construction.
- `P_n = Λ/I^n`: all quotient types are the actual Mathlib `Λ ⧸ I ^ n`, using
  Mathlib ideal powers. Positive indices are `n : ℕ+`, so every integer
  `n ≥ 1` occurs, including `1`.
- Additive torsion is **of Λ/I**, not of Λ: `quotientTorsion` quantifies over
  `x : Λ ⧸ ideal` and asks for `m : ℕ`, `0 < m`, and `m • x = 0`.
- Every positive quotient is perfect **over Λ**, not over its own quotient
  ring: `quotientPerfect` is `adicQuotientPerfect Λ ideal n` for `1 ≤ n`.
  That definition places `ModuleCat.of Λ (Λ ⧸ I^n)` in degree zero with
  `DerivedCategory.singleFunctor`, then applies the repaired exact
  bounded-finite-projective predicate. The standard localization is used;
  no arbitrary object is substituted for the degree-zero quotient.
- Arbitrary `K : proEtaleDerivedCategory X Λ`: `AdicKFlatModel X Λ K` records
  one chosen complex, K-flatness, flat terms, and an isomorphism from its
  localization to K. This is the choice of model specified in the node's
  proof step 1, as in the recorded `derivedTensor` interface, rather than an
  extra restriction on K. `adicKFlatModel_exists` states availability for
  **every** K using Tag 06YS. No boundedness is assumed.
- `K_n` in the quotient-coefficient derived category is `adicReduction`:
  localize `adicChange X (Ideal.Quotient.mk (I^n)) M.complex`, where
  `adicChange` is the recorded `SheafOfModules.changeOfRingsComplex` along the
  constant coefficient map. This is the actual complex, not a chosen object
  from a mere existence statement. The repaired
  `derivedChangeOfRingsGeneral` gives precisely its derived-scalar-extension
  interpretation and canonical K-flat-resolution comparisons.
- Regard the reductions in D(X_proet,Λ): `adicReductionUnderlying` first
  applies `SheafOfModules.restrictScalars` termwise (`adicRestrict`) and then
  localizes in the **recorded** original coefficient category. In particular
  the underlying abelian sheaves and differentials remain unchanged.
  `adicReductionUnderlying_tensor` states its identification with the
  dependency's actual `Scheme.derivedTensorRing` using the same K-flat model
  and the degree-zero constant quotient module. This theorem asserts a
  property; no definition chooses unspecified data from its `Nonempty`.
- Quotient homomorphisms: `adicQuotientMap I b a hab` is the actual
  `Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)`. Its compatibility
  with the maps from Λ, identity, and composition are stated explicitly.
- `q_{b,a}`: `adicTransitionComplex_exists` uniquely characterizes the
  Λ-linear chain map on local sheafified tensor generators by
  `r tensor m ↦ q_{b,a}(r) tensor m`. `adicTransitionComplex` selects this
  uniquely determined map, and `adicTransition` localizes it. This is not an
  arbitrary map between two existentially chosen objects.
- Transition identity and composition: `adicTransition_id` says exactly
  `q_{a,a} = 𝟙`; `adicTransition_comp` says
  `q_{c,a} = q_{c,b} ≫ q_{b,a}` for `hab : a ≤ b`, `hbc : b ≤ c`.
- Normalization source: `adicReductionTwice` is the localization of the
  **successive** termwise changes of rings, first to P_b, then to P_a.
  `adicReductionModel_isKFlat` states K-flatness and flat terms of the first
  changed complex over P_b, using the landed Tag 0G7E declaration; therefore
  this very successive model computes the stated derived extension over
  P_b. It does not assert that P_b is flat over Λ.
- Canonical `θ_{b,a}`: `adicBalance_exists` uniquely characterizes the chain
  isomorphism by the balancing formula, in the scalar-first convention of
  the existing change-of-rings API:
  `s tensor (r tensor m) ↦ (s * q_{b,a}(r)) tensor m`.
  The inverse in the proof is `s tensor m ↦ s tensor (1 tensor m)`.
  `adicBalanceHom` chooses the uniquely determined map;
  `adicBalanceIso` uses its separately stated invertibility theorem.
  `adicNormalization` is exactly the localization of this balancing
  isomorphism. Its target is D(X_proet,P_a), as required.
- Normalization cocycle: `adicNormalization_cocycle` compares the two
  actual composites from the triple-extension model. The left side applies
  `adicChangeHom` to θ_{c,b} along P_b→P_a and follows by θ_{b,a}. The right
  side applies the same ordinary balancing comparison for P_c→P_b→P_a
  to the P_c-model and follows by θ_{c,a}. Thus the source associativity
  identification is present as a specified canonical map, not omitted or
  replaced by equality between unrelated sources.
- Normalization unit: `adicUnit_exists` uniquely specifies the ordinary
  unit map `s tensor m ↦ s • m`; `adicUnitHom` selects it.
  `adicNormalization_unit` identifies θ_{a,a} with its localization on the
  changed complex. This covers equal indices without silently assuming
  strict unitality of extension of scalars.
- Canonicity under resolution comparisons: the two additional naturality
  statements, `adicBalanceHom_naturality` and
  `adicTransitionComplex_naturality`, state the exact commutative diagrams
  on chain maps. The proof docstrings explain preservation of these
  equalities when quasi-isomorphisms between K-flat models are inverted,
  as supplied by `lem-pur-derived-change-of-rings`. Thus the model choices
  are the usual explicit choices of representatives, with their canonical
  comparisons, not extra coefficient or boundedness hypotheses.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`: exact ambient category,
  constant ULift coefficients, and standard localization.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` and
  `isNoetherianRing_iff_ideal_fg`: Noetherian condition.
- `Mathlib.RingTheory.Ideal.Quotient.Operations` and its dependencies:
  ideal multiplication and powers, `Ideal.Quotient.mk`,
  `Ideal.Quotient.factor`, `Ideal.pow_le_pow_right`, and the quotient module
  and ring structures. Read the recorded algebra/quotient match as a list
  of declarations, not as a nonexistent single identifier.
- `WeilConjectures.CategoryTheory.DerivedCategory.Perfect`,
  `DerivedCategory.IsPerfect`: exact finite projective model definition,
  with the localization-universe repair below.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`,
  `SheafOfModules.derivedChangeOfRings`: all quasi-isomorphism, pointwise
  derived-functor, triangulatedness, universal-property, and K-flat counit
  clauses are retained in the universe-general repair below.
- `Sheaf.Algebra.Homology.DerivedTensor`,
  `Scheme.derivedTensorRing` and `Scheme.derivedTensor`: underlying derived
  tensor, computed with the same chosen K-flat model.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
  `SheafOfModules.restrictScalars`: actual termwise restriction.
- `Sheaf.Algebra.Homology.ChangeOfRingsComplex`,
  `SheafOfModules.changeOfRingsComplex`: actual changed terms and
  differentials. Its now-landed node was added to `stmt_deps`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`,
  `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`: K-flatness and flat
  terms over the target coefficients. Its now-landed node was added to
  `stmt_deps`; the previous WAITING report no longer applies.
- `Sheaf.Algebra.Homology.KFlatResolution`,
  `CochainComplex.exists_isKFlatResolution`: general resolution existence,
  with the small-site universe repair below. This already recorded node
  was added to `stmt_deps` under the explicit landed-nodes rule in §5.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
  `SheafOfModules.changeOfRingsPresheaf`, `changeOfRings`,
  `changeOfRingsHom`, and `changeOfRingsComplex`: these are reused, not
  privately rebuilt. `PresheafOfModules.sheafificationAdjunction` supplies
  the actual map from tensor generators to sheafified sections.

Edge cases checked: n=1 is included; equal indices have actual unit maps;
triples may have any equalities among indices. I=0, I=top, the zero ring,
and the empty scheme are not excluded. An empty generating list is allowed
by `Ideal.FG`. Quotients need not be flat over Λ, finite as sets, or
nonzero. K need not be bounded or perfect. The torsion hypothesis applies
only to Λ/I. The coefficient ring is not assumed I-adically complete.
No statement correction or disputed statement is needed.

Searches made (the sandbox search log also retains earlier attempts):

- `msearch.py leanfinder`, "Derived scalar extension along quotient rings
  gives a reduction tower with canonical associative normalization
  isomorphisms": eight ordinary quotient/scalar-tower hits, including
  `Ideal.Quotient.isScalarTower` and cotangent-related scalar towers;
  none is the derived coefficient reduction tower.
- `msearch.py loogle`, `"restrictScalars", "DerivedCategory"`: zero hits.
- `msearch.py grep`,
  `derivedChangeOfRings|coefficientReduction|CompleteCoefficientDatum`:
  zero Mathlib hits.
- Earlier `msearch.py leansearch`, "Derived scalar extension sheaves of
  modules composition quotient rings": service unavailable (Internal
  Server Error); not treated as evidence of absence.
- `rg` over the read-only source `WeilConjectures` and this group's
  `lean/Sheaf`, with the tower names and node id: no existing datum or
  coherent canonical quotient reduction tower; the relevant general
  derived-change-of-rings and tensor declarations are those reused above.
- `rg` for the new declaration names (`derivedChangeOfRingsGeneral`,
  `IsPerfectRingComplex`, `adicBalanceHom`, `CompleteCoefficientDatum`)
  across Mathlib, the source, and the group library: no preexisting names.
  The more general PerfectScalarExtension theorem was inspected; it uses
  an inline model predicate and does not provide a usable shared
  arbitrary-universe perfect-ring-complex definition.

All writes were made in the assigned sandbox; no local Lean or lake build
ran, no direct git command ran, and no delivery was pushed. All four
modules are compiled separately on the server by `scompile.py`, nice 19,
two threads, 60 seconds per file. All four delivered modules compiled cleanly (main module approximately seven
seconds, each dependency module under two seconds). The required
`deliver2.py NF def-weil-pbc-complete-coefficient-datum --no-push` printed
`OK (dry run)`: compilation and preflight passed except for the expected
independent second-reading section, which the next worker writes. Nothing
was pushed. No second-reading section has been written by this worker.

## Dependency modules

`def-pc-perfect-ring-complex`:
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral` defines
`DerivedCategory.IsPerfectRingComplex`, with **exactly** the source's bounded
finite projective model predicate. The recorded upstream `IsPerfect` requires
`HasDerivedCategory.{u} (ModuleCat.{u} R)`. The actual standard localization
of `ModuleCat.{u} R` is in universe u+1, so the old interface could not state
the degree-zero quotient condition here. The repair separates the
localization universe w from u. Only this dependency's `lean` field changes.
Its proof is empty because this is an actual definition, with no `sorry` data.

`lem-pur-derived-change-of-rings`:
`Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral` states
`SheafOfModules.derivedChangeOfRingsGeneral`. The old theorem identifies
site object and morphism universes. The repair uses `C : Type u`,
`Category.{v} C`, coefficients/modules in max u v, and independent
localization universe w. For the actual site these are u=t+1, v=t,
coefficients t+1; no equality is imposed. Every original clause remains:
the additive termwise functor is specified on objects and morphisms by the
recorded change of rings; it preserves quasi-isomorphisms between K-flat
complexes; the pointwise left derived functor exists everywhere; it has
the defining counit/universal property, is triangulated, and computes on
K-flat complexes. The original proof is retained as a full docstring,
and the proof is `sorry`. Only the node's `lean` field changes.

`lem-pc-kflat-resolution`:
`Sheaf.Algebra.Homology.KFlatResolutionGeneral` states
`CochainComplex.exists_isKFlatResolutionGeneral`. The old resolution
interface also identified site object and morphism universes. The repair
retains every clause on the same arbitrary site: resolution of every
complex, K-flatness, flat terms, quasi-isomorphism, and a degreewise
epimorphic augmentation. Flatness is written as exactness of the existing
tensorRight functor, the defining condition of the recorded flat-sheaf
predicate, without its incidental universe equality. The proof docstring
carries all four original construction steps. Only the node's `lean`
field changes; adding this already recorded node to the item's `stmt_deps`
is permitted by brief-stage2 §5.

## Second reading by NF

I independently read the base node, its sandbox copy, every declaration in
CompleteCoefficientDatum.lean, and all three dependency modules. I compared the
item with its blueprint source, order 1255, and read the Stacks hypotheses and
constructions in sites-cohomology.tex at lemma-K-flat-resolution (06YS),
lemma-derived-base-change (06YY), lemma-pullback-K-flat (0G7E), and
lemma-derived-pullback-composition (0D6D). These apply to arbitrary ringed sites
and unbounded complexes; they impose no Noetherian scheme, flat quotient, or
boundedness assumption. I also read the recorded pro-etale category, tensor,
restriction, termwise change-of-rings, K-flatness and flatness declarations,
the original three dependency interfaces, and the repaired interfaces.

The node's objects, hypotheses and clauses, with their Lean renderings:

1. An arbitrary scheme X and its small pro-etale site: `X : Scheme.{t}`,
   `X.ProEt`, `ProEt.topology X`, and `proEtaleDerivedCategory X A`.
   `adicConstantRing` is the very constant CommRingCat sheaf of ULift A
   used by that recorded category; `adicModuleRing` forgets commutativity.
   `adicLocalization` uses the same `HasDerivedCategory.standard`.
   Verdict: exact, including site objects in t+1 and morphisms in t.
2. A commutative Noetherian coefficient ring: `[CommRing Λ]` and the
   `CompleteCoefficientDatum.noetherian : IsNoetherianRing Λ` field.
   An ideal with a finite generating list: `ideal : Ideal Λ` and
   `finitelyGenerated : ideal.FG`. No chosen list enters any formula, so
   existence of a finite list is exactly the required datum. Verdict: exact.
3. Positive quotient coefficients P_n: the actual Mathlib quotient
   `Λ ⧸ d.ideal ^ (n : ℕ)`, with `n : ℕ+` in the tower and `1 ≤ n` in
   the hypothesis. The power and quotient use the recorded Mathlib
   operations, not formal symbols or arbitrary replacement rings.
   Verdict: exact; the bound includes n=1.
4. Additive torsion of Λ/I: `quotientTorsion` quantifies over elements of
   `Λ ⧸ ideal`, with a positive natural annihilator for each element.
   Perfectness of every P_n over Λ: `quotientPerfect` and
   `adicQuotientPerfect` put `ModuleCat.of Λ (Λ ⧸ ideal ^ n)` in degree
   zero and apply `DerivedCategory.IsPerfectRingComplex` over Λ.
   Verdict: exact; neither torsion of Λ nor perfectness over P_n is
   substituted. No completeness assumption is added by the structure name.
5. Every K in D(X_proet,Λ): `K : proEtaleDerivedCategory X Λ` and a
   chosen `M : AdicKFlatModel X Λ K`. Its fields are a K-flat complex,
   flat terms, and an isomorphism from its localization to K.
   `adicKFlatModel_exists` supplies such a model for every K, as required
   by proof step 1. Verdict: an explicit representative choice, not a
   restriction on K.
6. Reduction by derived change of rings to D(X_proet,P_n):
   `adicReduction` localizes `adicChange` along `Ideal.Quotient.mk`.
   `adicChange` is the landed `changeOfRingsComplex`, whose terms and
   differentials I checked. The generalized derived-change-of-rings
   dependency supplies its K-flat computation and canonical comparisons.
   Verdict: exact real construction, with no existentially chosen object.
7. The same reduction in D(X_proet,Λ), with its derived tensor meaning:
   `adicReductionUnderlying` applies the recorded `restrictScalars`
   termwise before localization. Its underlying sheaves and differentials
   are retained. `adicReductionUnderlying_tensor` compares this object
   with the recorded `derivedTensorRing`, using the identical K-flat
   model and the actual constant quotient in degree zero. Verdict: exact.
8. Quotient-induced q_{b,a} for every b≥a≥1: `adicQuotientMap` is
   `Ideal.Quotient.factor` for `Ideal.pow_le_pow_right`. The uniquely
   specified `adicTransitionComplex` sends r tensor m to q(r) tensor m;
   `adicTransition` localizes it in the original coefficient category.
   `adicTransition_id` and `adicTransition_comp` have exactly the node's
   identities, with Lean composition in the order c→b→a. Verdict: exact.
9. Canonical normalization θ_{b,a}: `adicReductionTwice` is successive
   extension first to P_b and then to P_a. `adicReductionModel_isKFlat`
   supplies K-flatness and flat terms over P_b, so this computes the
   successive derived extension. `adicBalance_exists` uniquely specifies
   the isomorphism by s tensor (r tensor m) ↦ (s*q(r)) tensor m, in the
   existing API's scalar-first convention. `adicNormalization` localizes
   precisely this map. Verdict: the scalar-extension associativity map,
   with target D(X_proet,P_a), not an arbitrary isomorphism.
10. Cocycle and unit: `adicNormalization_cocycle` compares the two maps
    from the same triple-extension complex; its right path includes the
    ordinary balancing comparison for P_c→P_b→P_a. The left path is
    extension of θ_{c,b}, followed by θ_{b,a}. `adicNormalization_unit`
    identifies θ_{a,a} with the localized unique map s tensor m ↦ s•m.
    Verdict: exact, including the canonical source identification and
    equal indices. `adicBalanceHom_naturality` and
    `adicTransitionComplex_naturality` give the comparison diagrams from
    proof steps 2 and 3; localization and inversion preserve them.

Dependency-module reading (H13): the original `IsPerfect` explicitly fixes
`HasDerivedCategory.{u} (ModuleCat.{u} R)`. The repaired predicate has the
identical bounded finite projective complex formula with localization universe
w independent of u. I checked the source definition in upstream Perfect.lean
and Stacks more-algebra.tex, definition-perfect; the node's cited cutting
lemma is a use of that notion, not a different definition. The original
change-of-rings and resolution interfaces both impose `Category.{u}` on
`Type u`, which cannot serve the stipulated small site. Their repairs
separate site universes and retain all clauses. In particular the resolution
still has a degreewise epi quasi-isomorphism and exact tensorRight terms;
the latter is precisely the defining formula of the recorded flat predicate.
The change-of-rings repair fixes both the objects and maps of E, preserves
quasi-isomorphisms between K-flat complexes, and states pointwise existence,
the universal derived pair, triangulatedness and its K-flat counit condition.
These are authorized interface repairs, not additional mathematical notions.
There are no new definition nodes to audit under H12.

Edge cases: `Ideal.FG` permits the empty generating list. I=0, I=top, the zero
ring, the zero derived object and the empty scheme are not excluded beyond
the stated coefficient conditions. The tower deliberately excludes n=0,
as does the node; the auxiliary ideal map remains meaningful there.
Equal pairs and triples of indices are included with `≤`, and the actual
unit comparison is stated. There is no characteristic restriction, finiteness
of quotient sets, nontriviality, completeness, boundedness of K, or flatness
of P_n over Λ. Coefficients and schemes use the recorded common size
convention, with ULift only on constant coefficients; none of the repairs
identifies the two site universes. All variables and universes are bound.

Independent H4 searches used different concept queries from the worker:

- `msearch.py leanfinder`: "Adic ideal quotient coefficient tower derived
  categories sheaves scalar extension associativity" returned eight hits,
  including `localCohomology.diagram`, ordinary AdicCompletion scalar towers
  and `AdicCompletion.transitionMap_comp_reduceModIdeal`. Their signatures
  concern ordinary modules/completion or local cohomology, not this derived
  sheaf coefficient tower.
- `msearch.py loogle`: `"quotient", "Perfect"` returned seven unrelated
  perfect-field, perfect-group and perfection/Teichmuller declarations.
- `msearch.py grep`: `adicReduction|CompleteCoefficientDatum|derivedChangeOfRings|IsPerfectRingComplex`
  returned no Mathlib hits. Independent `rg` over Mathlib, slopmaster2
  WeilConjectures, the group's exact pro-etale framework and lean/Sheaf
  found no existing tower or generalized declarations under the searched
  names. Broader searches for coefficient data, reduction towers and
  balancing isomorphisms found ordinary coefficient extensions, not this
  notion. The usable existing component definitions are reused above.
- `msearch.py leansearch`: "Derived reductions modulo powers of an ideal
  with canonical transitive change of rings isomorphisms on sheaves"
  was unavailable (Internal Server Error); no absence verdict is inferred.

Mismatches found and repaired: no mathematical statement mismatch. The
KFlatResolutionGeneral proof docstring cited older intermediate node names;
I replaced it with the current dependency node's three telescope steps,
including the cone desc restrictions and epi factorization. The
DerivedChangeOfRingsGeneral proof docstring likewise now follows its current
DAG steps: build E, invoke the K-flat quasi-isomorphism lemma, then apply
the resolving-class theorem. I added direct public imports of
ChangeOfRingsComplex and TensorProduct to the item, which uses both and
which previously obtained them only transitively. No definition, hypothesis,
theorem signature, or node statement was changed; no statement correction
or citer audit is required. The node `lean.statement` fields remain verbatim
substrings of their respective signatures. Chosen maps come only from
uniquely specifying theorems; all other definitions have real data, all
postponed theorems have source/proof docstrings, and no proof was supplied.

Validation: all four delivered files compiled cleanly in the independent
server compilation via scompile.py (nice 19, two threads, 60 seconds per
file). Line-width and verbatim-signature checks passed. The final delivery
commands repeat server compilation after the documentation/import repairs.
