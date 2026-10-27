## Worker report

The module `Sheaf.CategoryTheory.NormalizedComparisonBinaryRestriction` states
`CategoryTheory.normalizedComparison_binary_restriction`, with its sole theorem proof
`sorry`. It constructs three helpers owned by this node: `binaryComparisonComposite`
is H, `binaryRestrictionCounit` is eta, and `binaryComparisonTransport` is the specified
tilde h. All have real data, assembled from Mathlib natural isomorphisms, whiskerings,
associators and unitors. No missing independent notion or dependency repair was needed.

Source read: main-20261015 blueprint,
`sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md`,
paragraph (2), and all seven steps of this node's extracted categorical proof.
The blueprint attributes composition compatibility to that of the projection formula;
this node isolates precisely the categorical restriction calculation.

Hypothesis and clause correspondence:

- The categories C_X^r, C_S^r, C_T^r, C_X^s, C_S^s, C_T^s are `Xr`, `Sr`, `Tr`,
  `Xs`, `Ss`, `Ts`, each with its own explicit object and morphism universes and
  `Category` instance. This uses the dependency `def-nagata-category`'s exact Mathlib
  match `CategoryTheory.Category`, in `Mathlib.CategoryTheory.Category.Basic`.
- The six L functors are `Lar`, `Lbr`, `Labr`, `Las`, `Lbs`, `Labs`; the six E functors
  are `Ear`, `Ebr`, `Eabr`, `Eas`, `Ebs`, `Eabs`. The morphism labels a, b, ab index
  these supplied data only; no base category or geometric arrow is hypothesized.
  Mathlib's `A ⋙ B` means apply A first, reversing the displayed functional products.
- The six rho isomorphisms are `rar`, `rbr`, `rabr`, `ras`, `rbs`, `rabs`, each of
  type E followed by L isomorphic to the identity on the source category.
- The supplied restriction identifications are arbitrary isomorphisms `cr` and `cs`
  from Lab to La followed by Lb; they are not equality assumptions or identities.
  There is just one binary composition, so no further triple-composition coherence
  data occurs in the statement.
- The two gamma isomorphisms are `gr : Ebr ⋙ Ear ≅ Eabr` and
  `gs : Ebs ⋙ Eas ≅ Eabs`.
- Equation (G) for r is `gr_compat`; for s it is `gs_compat`. Each maps gamma by Lab,
  then applies rho_ab. Its other route first applies the specified restriction
  identification at Ea(Eb M), then Lb(rho_a), then rho_b. Thus the implicit
  identification in (G) is present explicitly, with its correct direction.
- The coefficient functors are `FX`, `FS`, `FT`; the three q isomorphisms are `qa`,
  `qb`, `qab`. The hypothesis `q_compat` states exactly the supplied composition
  equality after the cr/cs identifications: qab then FT(cr) equals cs then Lbs(qa)
  then qb. It does not replace qab by arbitrary composite data.
- The given h isomorphisms are `ha : Ear ⋙ FX ≅ FS ⋙ Eas` and
  `hb : Ebr ⋙ FS ≅ FT ⋙ Ebs`. Equations (N) are `na` at every M in Sr and `nb` at
  every M in Tr: apply Ls(h), then rho_s; equivalently apply q at Er(M), then F(rho_r).
- `binaryComparisonComposite ha hb` constructs H as ha at Ebr(M), followed by
  Eas(hb at M). Its definition inserts all required associators.
- `binaryRestrictionCounit rar rbr` and `binaryRestrictionCounit ras rbs` construct
  eta_r and eta_s as Lb(rho_a at Eb(M)), followed by rho_b. Associators and the
  identity-functor unitor are explicit in the construction.
- The first conclusion conjunct is (B) evaluated at every M in Tr: Lbs Las(H_M)
  followed by eta_s at FT(M) equals Lbs(qa at Ear Ebr M), then qb at Lar Ear Ebr M,
  then FT(eta_r at M). The order is Mathlib's diagrammatic order.
- `binaryComparisonTransport ha hb gr gs` is an actual natural isomorphism,
  constructed as FX(gr inverse), then H, then gs at FT. Its endpoint is exactly
  `Eabr ⋙ FX ≅ FT ⋙ Eabs`, so the statement also retains the isomorphism assertion.
- The second conclusion conjunct is the normalization of that specified transported
  isomorphism, evaluated at every M in Tr: Labs(tilde h_M) followed by rho_abs at FT(M)
  equals qab at Eabr(M), followed by FT(rho_abr at M).
- All equalities of natural transformations, including hypotheses, are rendered
  as equality at every object. By `NatTrans.ext`, this is equivalent to equality
  of transformations, not a weakening. The component form also avoids conflating
  a chosen natural identification with definitional equality.
- No faithful, full, adjunction, additive, nonempty or geometric assumptions occur.

Dependency source inspection: read `CategoryTheory.Category` and `CategoryStruct`
in `Mathlib.CategoryTheory.Category.Basic`, including all laws; read
`CategoryTheory.Functor.whiskerLeft_comp_whiskerRight` in
`Mathlib.CategoryTheory.Whiskering` (the proof-dependency
`lem-amb-natural-transformation-whisker-exchange`'s exact Mathlib match).
Also read `Functor`, `NatTrans`, functor associators/unitors, `isoWhiskerLeft`, and
`isoWhiskerRight` signatures/docstrings. The single public import of Whiskering supplies
all notions in the signature and the proof-dependency exchange identity; no other
recorded dependency module exists or is needed.

Edge cases checked before writing: empty categories are allowed (no objects or
Nonempty instances are selected); singleton and identity functors give the identity
calculation. Zero categories and zero objects impose no extra assumption.
Nontrivial specified cr/cs are retained explicitly in both (G) and q compatibility,
so the result is not restricted to strict functor composition. Natural isomorphisms
retain their given inverses. Six independent object and six independent morphism
universes exclude no mixed-size category case. All binders are explicit, with
`autoImplicit false`; no file-local notation or instances occur.

Searches performed with `msearch.py` for this item:

- LeanFinder, “Normalized comparison isomorphisms for two composable restriction
  functors and compatible extension compositors”: 8 hits, mainly SmallObject
  restriction/iteration and ComposableArrows; no matching statement.
- Loogle, `CategoryTheory.NatTrans.naturality, CategoryTheory.Functor`: 9 hits,
  including naturality, pullback/pushout cone lemmas and Grothendieck.map_map;
  none is the two asserted normalization conclusions.
- Mathlib grep, `normaliz.*comp|comp.*normaliz`, `CategoryTheory`: 8 hits,
  free monoidal/bicategorical coherence constructions; none matches.
- LeanSearch, “Two normalized comparison natural isomorphisms remain normalized
  under composition and transport by compatible compositors”: 8 hits including
  free coherence, NatIso.trans_app and product comparisons; none matches.
- Project `rg` searches for normalized comparison and restriction normalization
  in `lean/WeilConjectures` and `lean/Sheaf`, plus grep of the exact blueprint id
  in `lean/WeilConjectures`: no declaration states this generic calculation.
  Nearby equivalence/adjunction comparisons require additional adjunction data,
  and scalar binary coherence specializes to tensor products. Full-name searches
  for all four declarations in Mathlib and both project roots returned no clashes.
  The upstream name index was also searched for restriction/normalization matches.

Validation: `scompile.py NU lem-sfb-normalized-comparison-binary-restriction` compiled
both the sandbox and library-name forms successfully (4.0 s and 2.6 s), with no
errors or unexpected warnings. No statement correction or disputed statement.

## Second reading by NU

No second reading by a worker: the dispatcher brief prohibits starting another
agent, and authorizes direct delivery for the maintainer's independent review.
The worker's correspondence above records every hypothesis and both conclusions;
it is not represented as an independent review.
