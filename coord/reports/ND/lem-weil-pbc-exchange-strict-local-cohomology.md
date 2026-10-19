## Worker report

The module `Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology` states
`AlgebraicGeometry.Etale.isIso_exchange_iff_strictLocalCohomology`, with its whole proof
`sorry`. Source checked directly: literature/stacks-project/etale-cohomology.tex,
Tag 0EZU, lemma-base-change-f-star-general-stalks (lines 16497 onward).
No statement correction or new definition is needed.

Hypothesis and clause correspondence:

- Schemes and morphisms: `{X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)`.
- The two hypotheses on g are exactly `[QuasiCompact g] [QuasiSeparated g]`.
  No finite-type, properness, smoothness, or torsion hypothesis is imposed.
- The Cartesian square is the chosen `pullback f g`, with its first and second
  projections h and e, represented by `(IsPullback.of_hasPullback f g).toCommSq.flip`.
  The flip makes g the pushforward edge and f the inverse-image edge.
- Abelian etale coefficients: `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Nonnegative degree: `q : ℕ`; `q : ℤ` is used only by the derived homology API.
- The canonical degree-q exchange: apply `DerivedCategory.Plus.homologyFunctor` to the
  component of the recorded `derivedBaseChangeMapPlus` at `singleFunctor _ 0 F`.
  Its source and target identify canonically with f-inverse-image R^q g_* F and
  R^q h_* e-inverse-image F by exactness. Invertibility is invariant under these
  comparison isomorphisms, so there is no choice of a replacement exchange map.
- The two directions are the displayed `↔` with `IsIso` on the left and every
  geometric point on the right: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X)`. Its image is exactly `x ≫ f`.
- Strict local rings/schemes are the dependency's `Scheme.strictHenselizationRing`
  and `Scheme.strictHenselizationScheme`, with `strictHenselizationStructuralMap`.
- The canonical functorial map is represented by `a`, a homomorphism from the strict
  local ring at `x ≫ f` to the strict local ring at `x`. Its two defining equations
  are compatibility with the canonical evaluations into Ω and the equation `ha`
  over S. These are specifications of the map, inside the universal quantifier,
  not extra hypotheses on f, g, F, or geometric points. Such a map exists uniquely
  by `strictHenselizationFunctoriality` and its residue identification. Evaluation
  has maximal-ideal kernel (the pointed-map/residue theorem); evaluation compatibility
  therefore forces the inverse image of the target maximal ideal to equal the source
  maximal ideal. Thus a is local. The same compatibility forces exactly the inclusion
  between the residue fields embedded in Ω. Conversely the unique local functorial map
  satisfies these equations. No arbitrary map over S is substituted for the canonical map.
- The local products are `pullback (strictHenselizationStructuralMap (x ≫ f)) g`
  and `pullback (strictHenselizationStructuralMap x ≫ f) g`. Their arrow is the
  dependency's `pullback.map` induced by `Spec.map a`, the identity of T, and the
  identity of S, with `ha` supplying commutativity.
- Coefficients on the source are the inverse image of F along `pullback.snd`.
  `cohomologyMap` pulls these back along the displayed arrow; its target uses the
  iterated inverse image, canonically identified with pullback of F from T since
  the arrow preserves the T-projection. Bijectivity is unchanged by that canonical
  coefficient isomorphism. `Function.Bijective` states isomorphism of these abelian
  cohomology groups, using the node's recorded Sheaf.H / cohomologyMap presentation.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.snd`,
  `pullback.map`; Mathlib's `IsPullback.of_hasPullback` specifies the Cartesian square.
- Mathlib.FieldTheory.IsAlgClosed.Basic and AlgebraicGeometry.ResidueField:
  `IsAlgClosed`, `Scheme.SpecToEquivOfField` (the geometric point is written inline).
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact / QuasiSeparated: `QuasiCompact`,
  `QuasiSeparated`, using only the quasi-compact clause of def-weil-finite-type-morphism.
- Mathlib.CategoryTheory.Sites.Sheaf: `Sheaf`; the small etale topology is Mathlib's.
- Sheaf.AlgebraicGeometry.StrictHenselization: `Scheme.strictHenselizationRing`,
  `Scheme.strictHenselizationScheme`, `strictHenselization_properties`.
- Sheaf.Paper.StrictHenselizationFunctoriality: `strictHenselizationFunctoriality`
  and `strictHenselizationResidue`, including their residue normalization; the structural
  map is exposed by its imported Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap.
- Sheaf.Paper.StrictHenselizationPointEvaluation: `Scheme.strictHenselizationPointEvaluation`.
  The already-landed node def-weil-pbc-strict-henselization-point-evaluation was added to
  stmt_deps so this normalization uses an existing definition, not a new spelling.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.rightDerivedLowerStarPlus`.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek: `Etale.cohomology`,
  `Etale.rightDerivedGlobalSections`; the recorded cohomology node allows the existing
  Sheaf.H presentation for abelian coefficients (comparison is a stage-3 bridge).
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance:
  `Etale.cohomologyMap`, using the recorded canonical cohomology pullback.
- WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded: recorded
  `Etale.derivedBaseChangeMap`; for its recorded bounded-below abelian clause use
  WeilConjectures.SixFunctors.BaseChange.Derived: `Etale.derivedBaseChangeMapPlus`.
  The actual map used is H^q of that component, as specified by the dependency record.
- All stated proof dependency modules are imported, including the strict-local stalk
  formula, canonical restrictions, representative formula for higher exchange,
  cohomology pullback functoriality, geometric stalk comparisons and conservativity.
  The upstream affine-neighbourhood import is unavailable in the local pinned source
  but is available on the server: the server import probe checked it successfully.

Edge cases checked: q=0 uses the usual underived exchange via the recorded comparison;
there is no q>0 restriction. The zero sheaf is allowed. For X empty the geometric-point
condition is vacuous and every sheaf map on its etale topos is invertible. Empty T,
empty S when morphisms exist, arbitrary characteristic and arbitrary abelian coefficients
are admitted. Ω uses the same universe as Scheme, matching the existing geometric point
and strict-henselization APIs, with coefficient groups in u+1. Every universe and variable
is explicitly bound. Canonical-map compatibility does not exclude any geometric point.

Searches for existing statements:

- msearch.py leanfinder, query "Etale higher direct image base change is an isomorphism
  if and only if cohomology pullback on strict henselizations is bijective": eight
  unrelated ring-map etale/Kaehler results; no match.
- msearch.py loogle, query `"stalk", "cohomology"`: zero hits.
- msearch.py grep, query `strict.*hensel.*cohom|cohom.*strict.*hensel`: zero Mathlib hits.
- msearch.py leansearch, query "Etale base change is an isomorphism if and only if
  pullbacks on strict local cohomology are bijective": service unavailable (Internal
  Server Error), no conclusion drawn from this unavailable search.
- rg over WeilConjectures and lean/Sheaf for `exchange.*strict|strict.*cohomology|
  base.change.f.star.general`: existing special strict-local comparisons and the
  projective-line reduction, no general iff statement. The new name was searched in
  Mathlib, WeilConjectures and lean/Sheaf: no collision.
- rg for this item's id in WeilConjectures: no existing attachment. The upstream
  name index was checked for strict-henselization functoriality/evaluation; no match.
- Searches for `strictHenselizationPointEvaluation` found its already-landed DAG node
  and full construction via `colimit.desc`, so it is reused directly.

Validation: server-only scompile.py, nice 19, two threads, 60 seconds per file.
The first complete draft exposed a private-import visibility issue and an incorrect
Cartesian-square API call, both corrected. Final compile and delivery dry run are
recorded by the tool output for the second reader. No local compiler or build was run.


## Second reading by ND

Independent second reader: opened the node, its five proof steps, the complete Lean
module, and the recorded dependency signatures. Read Stacks etale-cohomology.tex,
lemma-base-change-f-star-general-stalks (Tag 0EZU), including its surrounding text.
The lemma imposes precisely qcqs on g; no ambient Noetherian, properness, torsion,
finite-type, or characteristic assumption is inherited. Also read Tags 04HX and
03PS and algebra.tex Tags 04GU and 08HV to check the strict-local interpretation.

Object/hypothesis/conclusion inventory and correspondence:

1. Schemes X, S, T and maps f:X→S, g:T→S: `{X S T : Scheme.{u}}`,
   `(f : X ⟶ S) (g : T ⟶ S)`. These are Mathlib schemes and scheme morphisms,
   not affine schemes or schemes over an extra base. Verdict: exact.
2. Quasi-compact and quasi-separated g: `[QuasiCompact g] [QuasiSeparated g]`.
   Read the Mathlib classes: compact preimages of compact opens, and quasi-compact
   diagonal respectively. No such hypothesis is imposed on f or the schemes.
   Verdict: exact, with neither finiteness nor separation strengthened.
3. Y=X×_S T and projections h:Y→X, e:Y→T: the chosen `pullback f g` inside
   `(IsPullback.of_hasPullback f g).toCommSq.flip`. Read `pullback.map` and
   the exchange signature: flipping puts the original g on its pushforward edge
   and f on its inverse-image edge. No extra square is assumed. Verdict: exact.
4. Abelian etale sheaf F on T: `F : Sheaf T.smallEtaleTopology
   AddCommGrpCat.{u + 1}`. This is the dependency's coefficient category, with
   the existing exact `upperStar` and left exact `lowerStar` constructions.
   It imposes no torsion or coefficient-ring restriction. Verdict: exact.
5. Degree q≥0: `(q : ℕ)`, mapped to ℤ only for the homology functor.
   This includes zero without an additional positivity hypothesis. Verdict: exact.
6. Canonical higher exchange is an isomorphism: the left side is `IsIso` of
   `Plus.homologyFunctor.map` of `derivedBaseChangeMapPlus.app` at
   `Plus.singleFunctor _ 0 F`. Read Derived.lean's definition and its resolution
   formula: this is the right-derived underived mate, rather than an arbitrary
   morphism or the underived exchange alone. Exact inverse image identifies its
   degree-q source and target with those of the node. This bounded-below abelian
   presentation is expressly allowed by sbc-def-base-change-map's lean record;
   it avoids the monoidal-instance requirements of the unbounded presentation.
   Verdict: the same canonical exchange, through canonical comparison isomorphisms.
7. Equivalence, for every geometric point with image under f: `↔ ∀ (Ω : Type u)
   [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)` and `x ≫ f`.
   Read the recorded inline geometric-point encoding and residue-field API.
   Verdict: correct quantifier order and correct image point.
8. Strict-local schemes and their canonical map: both use the recorded
   `strictHenselizationRing` (the affine pointed-neighbourhood coordinate-ring
   colimit), with `strictHenselizationStructuralMap`. The additional quantified
   ring map a is constrained by equality of the canonical evaluations into Ω
   and by ha, the structural compatibility over S. Opened the full signatures of
   `strictHenselizationResidue` and `strictHenselizationFunctoriality` and the
   construction of `strictHenselizationPointEvaluation` by `colimit.desc`.
   The evaluation equals the residue quotient followed by the specified embedding
   into Ω: both agree on every coordinate-ring coprojection. Its kernel is the
   maximal ideal. Hence evaluation compatibility gives
   a⁻¹(m_x)=m_s, forcing locality, and forces the specified residue inclusion.
   Functoriality therefore gives existence and uniqueness of precisely the maps
   quantified here. This is not a possibly empty family or an extra assumption
   on f. Verdict: exactly the canonical map, without duplicate definitions.
9. Local products and cohomology pullback: `pullback.map` goes from
   `pullback (strictHenselizationStructuralMap x ≫ f) g` to
   `pullback (strictHenselizationStructuralMap (x ≫ f)) g`, with component
   `Spec.map a` and identity on T and S. Read its actual argument order and
   equations. Cohomology is contravariant, so `cohomologyMap` has the node's
   direction from the S-local product to the X-local product. Verdict: exact.
10. Coefficients and invertibility: `upperStar` along the S-local product's
    `pullback.snd` pulls F from T. The target of `cohomologyMap` pulls it again
    along the product map; its composite to T is the other projection, so the
    standard inverse-image composition isomorphism gives the specified target
    coefficients. `Function.Bijective` of this additive homomorphism is exactly
    an isomorphism of abelian groups. Read the existing cohomologyMap definition
    and the cohomology/pullback node records permitting the Sheaf.H presentation;
    its comparison with derived Γ is an existing stage-3 bridge obligation,
    not a newly substituted notion. Verdict: exact.

Edge cases: q=0 is included; F=0 is allowed; no index family is introduced, so no
nonempty-index condition is hidden. Empty X makes the point condition vacuous,
and the exchange is a map in its trivial abelian sheaf category. Empty T and
empty S (when the displayed maps exist) are admitted. All characteristics and
arbitrary abelian coefficients are covered. Scheme, geometric-point and strict
henselization universes agree with their recorded APIs; groups are in u+1.
Every scheme point admits a geometric point in universe u by algebraic closure
of its residue field, so the selected universe still detects isomorphisms.
No variable or universe is left unbound.

Independent searches, with different wording from the worker:

- LeanFinder via msearch: “A base change morphism for higher direct images of
  etale abelian sheaves is invertible precisely when restriction on strict local
  fiber cohomology is bijective”. Eight hits, including general local bijectivity
  for sheaves and module-section comparisons; none states this criterion.
- Loogle via msearch: `"cohomologyMap"`, zero hits.
- Mathlib grep via msearch: `strictHenselization.*[Ii]so|[Ii]so.*strictHenselization`,
  zero hits. Direct rg of Mathlib, upstream WeilConjectures and project Sheaf for
  `strictLocalCohomology`, exchange/strict in both orders, the Stacks label, and
  0EZU found only related constructions and special cases, not this general iff.
- Opened upstream ProjectiveLine/StrictHenselian.lean and the project's
  StrictLocalExchangeCompatibility.lean at their statements: the former is a
  projective-line special case, the latter a compatibility equality with extra
  comparison data, not this general criterion. Neither replaces this module.

No new definition nodes or dependency modules occur in this delivery. The added
stmt_dep is the already-landed point-evaluation definition, whose construction
was read directly; it is reused rather than copied. There is no statement
correction, so the correction/citer audit does not apply. No mathematical or
encoding mismatch was found and no Lean or node change was needed. The module
contains one theorem with only `sorry`, no definitions or local notation, and
its source/blueprint docstring follows all five node proof steps in order.
The node's lean.statement was checked programmatically to equal the theorem
signature verbatim. Second reading changed only this report.

Validation: the server-only scompile.py run passed, reporting nice 19, two threads,
60 seconds per file; the delivered module took 2.9 seconds, with no errors or
warnings. Its proof-import overlay also compiled successfully. No local compiler
or global build was used. Delivery preflight/dry-run results follow in the tool log.
