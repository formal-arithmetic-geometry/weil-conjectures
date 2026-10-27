## Worker report

Recorded `existing: true` for
`AlgebraicGeometry.integralChartLogificationThickening` in
`Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening`, already attached to
`lem-per-integral-chart-logification-thickening` (Q73, reviewed 2026-10-24).
The two DAG `statement` strings compare exactly equal, including all paragraphs,
references and quantifiers. I read the complete existing module, including its
six helper definitions and thirteen-step proof docstring, and the underlying
presentation, log, chart, morphism, stalk and thickening definitions. This delivery
changes this item's `lean` record and adds the five landed definition owners to
`stmt_deps`, with the signature copied verbatim from the source, excluding `:= by`. There is no new module and no duplicate theorem.
The existing theorem remains a stage-2 statement with `sorry`; no proof is claimed.

The source ILO VI 1.1, printed p.69, was read directly from the local PDF (PDF p.75).
It specifies étale log structures and local fine charts, and generally assumes
locally Noetherian log schemes. This node explicitly supplies a more general,
agent-formulated construction on arbitrary schemes; its source record says this
is not itself an ILO theorem. The existing declaration likewise uses the unbundled
`EtaleLogStructure`, never the Noetherian `FineLogScheme` or `FineSaturatedLogScheme`.
No source correction or statement dispute is needed.

Hypotheses and clauses, in order:

- Any scheme T: `T : Scheme.{max u v}`. There is no Noetherian, affine, separation,
  reducedness, or characteristic hypothesis. The common enlarged universe supports
  a monoid `P : Type v` without restricting its size relative to T's functions.
- Finitely generated integral commutative monoid: `[CommMonoid P]`,
  `hfg : Monoid.FG P`, and
  `hint : Function.Injective (Algebra.GrothendieckGroup.of (M := P))`.
  These express exactly finite generation and the canonical group-completion embedding.
- Multiplicative chart: `β : P →* Γ(T, ⊤)`. Its restriction is `associatedLogBeta β W`.
- A log structure is `L : EtaleLogStructure T`: a `CommMonCat` sheaf on
  `T.smallEtaleTopology` and its structural natural transformation to the
  multiplicative structure presheaf. `reflectsUnits` and `unitsBijective` express
  the inverse image of ring units being isomorphic to those units, tested at
  geometric stalks. These are equivalent to the sheaf unit axiom because the
  small étale site has enough geometric points. Neither field assumes integrality.
- The explicit presheaf is `associatedLogPresheaf β`. Its values are the actual
  `divisorialChartPushout` quotients of `ULift P × Γ(W.left, ⊤)ˣ` by
  `divisorialChartCongruence`, and restriction fixes p and pulls back the unit.
  The congruence identifies `(e,1)` with `(1,β(e))` for precisely the elements
  mapping to ring units; multiplication gives the node's `(pe,v) ~ (p,β(e)v)`.
  The lift is canonically isomorphic to P and introduces no new mathematical data.
- Sheafification and structural formula: the existential unit
  `η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj` and
  `IsAssociatedLogPresentation β L η` give the monoid sheafification universal
  property (composition with η bijective for every monoid sheaf) and explicitly
  `α(η([p,b])) = β_U(p) * b.val`. This determines the sheaf and its structural map
  up to the unique presentation-preserving isomorphism; no arbitrary object is
  chosen from a bare existence theorem.
- Integral fine log structure: the first conjunct after the presentation is
  injectivity of `GrothendieckGroup.of` for every geometric stalk; `L.IsFine`
  is étale-local charting by finitely generated integral monoids.
  `L.IsChart (Scheme.Etale.mk (𝟙 T)) (associatedLogIota β L η)` specifies the
  global chart that produces L.
- Canonical stalk formula: `IntegralChartStalkPresentation β L η` gives an
  isomorphism from the displayed pushout over `strictLocalRing T t` to the actual
  log stalk, normalized on every pair `(p,b)` represented in every pointed étale
  neighbourhood. Its map on units is the actual ring germ `strictLocalGerm`.
- All scheme maps and all target log structures: the universal quantifiers
  `(S : Scheme.{max u v}) (a : S ⟶ T) (K : EtaleLogStructure S)` impose no
  extra geometric or logarithmic assumptions. `K.HomAlong L a` presents maps
  `a⁻¹L → K` by natural section maps on all relative test diagrams, with the
  structural compatibility equation built in.
- The asserted bijection is `Function.Injective (integralChartCompose β L η K a)`
  together with its range being exactly the charts c satisfying
  `(K.alpha.app ...).hom.comp c = associatedLogDownChart (a.appTop.hom.toMonoidHom.comp β)`.
  Evaluation on the chart is the forward map, injectivity gives uniqueness, and
  the exact range gives existence for every and only compatible chart. This is
  bijectivity onto the node's specified subtype, expressed without arbitrary choices.
- Étale restriction: `IntegralChartEtaleRestriction β L η` quantifies over every
  `U : T.Etale`, produces an associated presentation for `β_U`, and identifies
  its sheaf with the restricted original sheaf. The comparison is normalized on
  all pair representatives and preserves the structural maps.
- Every first-order thickening: `(T₀ : Scheme.{max u v}) (j : T₀ ⟶ T)` followed
  by `IsFirstOrderThickening j →`. That recorded predicate means closed immersion
  and square-zero defining ideal. It already implies equality of underlying spaces.
- Reduced chart and canonical log map: `L₀`, `η₀`, and `H : L₀.HomAlong L j`,
  with `IsAssociatedLogPresentation (j.appTop.hom.toMonoidHom.comp β) L₀ η₀`
  and the equality of `integralChartCompose ... H` with `associatedLogIota ...`.
  Here reduced means restriction modulo the thickening ideal, not passing to the
  reduced scheme. Nilpotents in T₀ are retained.
- Strict stalk pushout: `IntegralChartThickeningStalks j L L₀ H` supplies ring
  reduction r and log reduction q normalized on every relative germ. It states
  r surjective, `RingHom.ker r = integralChartThickeningIdeal j t`, and the kernel
  square zero. The ideal is the span of germs vanishing on the base change of j.
  Compatibility with `unitsIn`, surjectivity of `q.coprod (L₀.unitsIn t)`, and its
  kernel being exactly the generated unit-identification congruence present the
  target as the pushout along `Aˣ → (A/I)ˣ`. The ring quotient is canonically
  identified by the stated surjectivity and exact kernel.
- Nonempty torsor fibres: the same predicate states `Function.Surjective q` and,
  whenever `q m = q m'`, `∃! c : RingHom.ker r` with a unit b of value `1+c`
  satisfying `m' = m * L.unitsIn ... b`. The next conjunct gives the unique such
  unit for every c. Thus both existence of lifts and free transitive difference
  by the ideal are present.
- Sheaf-local assertion: `IntegralChartThickeningLocal j L L₀ H` specifies the
  actual reduction natural transformation ρ by `H.sectionMap`, states
  `Presheaf.IsLocallySurjective T.smallEtaleTopology ρ`, and gives the unique
  ideal difference of any two sections with equal reduction on every étale W.
  It also identifies each ideal section with its unique unit log section of
  structural value `1+c`. It does not require surjectivity on global sections.
- Multiplication versus addition: both the stalk and sheaf-local predicates
  explicitly state `(1+c.val)*(1+d.val) = 1+(c.val+d.val)` for all kernel elements.

Dependencies read and reused through the existing declaration:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; full signatures and docstrings read.
- `def-weil-pbc-etale-site`: `Scheme.Etale`, `Scheme.smallEtaleTopology`,
  `Scheme.ofArrows_mem_smallEtaleTopology_iff`, from Mathlib's étale morphism/site
  files. The last criterion is exactly jointly surjective covering families.
- `lem-trf-commutative-monoid-sheafification` is a Mathlib leaf: its recorded match
  is `CategoryTheory.sheafificationAdjunction` in
  `Mathlib.CategoryTheory.Sites.Sheafification`, together with
  `sheafifyComposeIso` and `sheafComposeIso_hom_fac` in
  `Mathlib.CategoryTheory.Sites.PreservesSheafification`. I read these declarations;
  they give the monoid universal property and its underlying-set normalization.
- `def-weil-pbc-geometric-stalks`: `pointedEtaleStalkDiagram`, `pointedEtaleStalk`,
  `pointedEtaleCommMonStalkHasColimit`, `pointedEtaleGerm` in
  `Sheaf.AlgebraicGeometry.PointedEtaleStalk`. The existing log stalk uses exactly
  this diagram and colimit, not a separately invented stalk.
- `def-sbc-first-order-thickening`: `IsFirstOrderThickening`,
  `WeilConjectures.AlgebraicGeometry.Thickening`, exactly closed immersion and
  `j.ker ^ 2 = ⊥`.

The existing module also reuses `AssociatedLogUniversalStalks` for the real quotient
presheaf and `IsAssociatedLogPresentation` (owned by the landed
`def-per-associated-log-presentation`), `FineSaturatedLogBlowup` for unbundled log
structures and charts, `FineLogEtaleDescentDatum` for `IsFine`,
`FineLogSchemeMorphisms` for `HomAlong`, and `LogRegularPair` for strict-local rings,
germs and the quotient pushout. These definitions were read at their source; the
Noetherian theorem in `AssociatedLogUniversalStalks` is not assumed by the binding.
Their already landed definition nodes are now explicit statement dependencies;
no new node, duplicate definition or dependency-module repair is required.

Edge cases checked before attaching the declaration: the empty scheme (the sheaf
condition forces the terminal section monoid on the empty object); P trivial;
P a finitely generated group; a noninjective β on elements mapping to units;
non-saturated integral P; β taking nonunits to zero; characteristic two; arbitrary
non-Noetherian T; the identity thickening and zero ideal (unique difference zero);
nonreduced T₀; and failure of global-section surjectivity. None is excluded by a
binder. All universes and typeclass binders are explicit in the existing theorem.

Searches performed with `msearch.py` under Q132 and this item:

- `leanfinder`: “Integral finitely generated monoid chart logification on arbitrary
  schemes with universal property and strict square zero thickening torsor fibers”.
  Eight ordinary étale/affine-space/normalization hits; no logarithmic theorem.
- `loogle`: `"LogStructure"`. Zero hits.
- `grep`: `LogStructure|logification|integralChartLogification` in Mathlib's
  AlgebraicGeometry directory. Zero hits.
- `leansearch`: “Associated log structure of a finitely generated integral monoid
  chart and strict square zero thickening”. Eight square-zero-extension,
  divided-power, nilradical and localization hits; no logarithmic theorem.
- Local `rg` of `lean/WeilConjectures` and `dag/lean_names_upstream.json` for log
  structures, logification and the theorem name found no exact upstream theorem.
  Search for this item's blueprint id in `WeilConjectures` also found none.
- Local `rg` of `lean/Sheaf` found the exact existing theorem and its full helper
  predicates. DAG filename search found the perverse twin. Parsing both node JSON
  files confirmed exact equality of the entire natural-language statements.

Validation: the prescribed delivery wrapper checks this existing declaration by a
server-compiled import and `#check`, and runs the maintainer's server preflight.
No module is delivered or separately restated.


## Repair of returned delivery 686f6eb0dc2d

H2 repaired: the retained sandbox packet had the same five original `stmt_deps`
as current main. I added all five landed nodes required by the maintainer:

- `def-trf-fs-log-blowup`: owns `EtaleLogStructure`, `IsChart`, stalks and units.
- `def-trf-fine-log-etale-descent-datum`: owns `EtaleLogStructure.IsFine`.
- `def-trf-fine-log-scheme-morphisms`: owns `EtaleLogStructure.HomAlong`.
- `def-per-associated-log-presentation`: owns `associatedLogPresheaf`,
  `IsAssociatedLogPresentation`, `associatedLogIota` and `associatedLogDownChart`.
- `def-trf-log-regular-pair`: owns `strictLocalRing`, `strictLocalGerm`,
  `divisorialChartCongruence` and `divisorialChartPushout`.

I checked all five current node records: each has a landed Lean interface for
these declarations. The original dependencies are retained. The complete Lean
record is unchanged from the returned sandbox packet, and the natural-language
statement remains identical to both current main and the twin. Comparing the
repaired packet with current main shows changes only to `lean` and `stmt_deps`.
This is the gained-landed-dependencies repair authorized in the return, not a
statement correction. The delivery wrapper constructs the repaired commit on
current main and compiles the existing-declaration probe before preflight.

The maintainer's ownership note is conditional on pruning the twin. This packet
contains no module edits and does not prune the twin; docstring ownership remains
with the existing module until that separate pruning occurs.

## Second reading by Q132

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
