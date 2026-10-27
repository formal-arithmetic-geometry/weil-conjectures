## Worker report

The module `Sheaf.Paper.ExceptionalFiniteOperations` states
`WeilConjectures.exists_sfFiniteExceptionalOperations`; its only postponed proof is
that theorem. The repair pins the two restricted functors to the canonical intrinsic
compact-support and coefficient-conjugated exceptional functors. It also pins `rF`
and `rG` to the resulting canonical realization isomorphisms and requires shift
compatibility for both. The added statement dependencies record every owner of these
objects and of the normalized Hom chain.

Hypotheses and clauses, checked against the node:

- `D : FiniteFieldDatum.{u}` supplies p,a,q,k₀,k, the cardinality, algebra structure
  and algebraic closure. `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p` are exactly
  the coefficient prime assumptions.
- Both schemes have `Over (Spec (.of D.k))` instances and locally finite type and
  quasi-compact structure morphisms. These two properties mean finite type.
  `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` impose
  precisely the relative conditions. Neither structure morphism is assumed separated.
- `c : Compactification f` retains the specified middle scheme `c.Z`, open
  immersion `c.i`, proper map `c.g` and factorization. The natural-number `d`
  and `hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)` render the stated
  nonnegative dimension bound. This is for every supplied bound, including 0
  for an empty middle scheme, whose dimension is bottom.
- `E : ConstructibleExceptionalCoefficients.FieldStage l` packages an arbitrary
  finite-dimensional extension of `Padic l`; `n : ℕ+` ranges over exactly all
  positive exponents, including 1. `Padic.coefficientExtensionRing l E.carrier n`
  is the existing quotient by the chosen uniformizer power, not an l-power
  reindexing or an arbitrary finite ring. The finiteness instance is directly
  `Padic.finite_coefficientExtensionRing`.
- F and G are functors between the actual `finiteTorConstructibleCategory`
  full subcategories. The equalities `eF` and `eG` force their composites with the
  full inclusions to be the canonical `sfIntrinsicCompactSupport` and
  `sfFiniteOperationsIntrinsicRight`, respectively; they cannot be replaced by
  arbitrary functors with isomorphic outputs. Their morphisms are ambient derived morphisms; no abstract
  category, completion or class of test objects replaces these categories.
  Their inherited triangulations are the already-published finiteTriangulated
  instance, indexed by FieldStage and the positive exponent.
- The existential Additive, CommShift, IsTriangulated and Adjunction data assert
  additivity, coherent integer shifts and exactness of both functors. The unit
  and counit have `CommShift ℤ`. `sG = adj.rightAdjointCommShift ℤ` specifies
  the entire right shift structure as the adjoint one for the chosen left shift.
- `sfFiniteOperationsRealization` is exactly the full inclusion followed by the inverse
  of `sfIntrinsicDerivedEquivalence`, the published canonical equivalence with fixed-ring
  module-sheaf coefficients. Its shift structure is the composite of the full
  triangulated inclusion and the termwise exact coefficient-equivalence inverse. The
  equality `rF = sfFiniteOperationsLeftRealization ...` makes `rF` the published
  `sfIntrinsicCompactSupportComparison` transported through that equivalence. The
  equality `rG = sfFiniteOperationsRightRealization ...` makes `rG` the corresponding
  unit/counit cancellation for the specified `sfFiniteExceptionalAt` functor. The
  statement separately requires `rF.hom.CommShift ℤ` and `rG.hom.CommShift ℤ`; no
  automorphism can be absorbed into either realization.
- `hX` and `hY` assert bounded-below typing of these constructible objects.
  Existence of an explicit `FixedEtaleOriginWitness` is part of the conclusion,
  so the normalization does not quantify over a possibly empty witness type.
  The Hom equation holds for every witness W and every a. Its left side is the
  full-inclusion/coefficient realization of `adj.homEquiv`, followed by rG;
  its right side first uses the inverse of rF, then exactly the published
  `specifiedExceptionalHomEquiv` chain. This retains the ordinary etale
  adjunction, site comparison unit/full faithfulness and proper/open comparison;
  it also states witness independence by using every W. The helper only supplies
  CompactSpace Y from the given quasi-compact structure map over a field.
- The F Tor clause is `[a,b] → [a,b+2*d]`, using exactly
  `HasProEtaleTorAmplitude`, on every input of the finite-Tor category.
- `∃ cMinus cPlus : ℤ` is outside BOTH E and n. The last two clauses apply
  these same signed constants to the cohomological `constructibleInterval`
  and the Tor predicate for G. This renders coefficient-independent
  constructible/cohomological and Tor bounds. Using one pair for the two bounds
  loses no generality: take the lesser lower bound and greater upper bound if
  initially given different pairs. No coefficient or refinement equations
  between different choices have been asserted.

Dependencies used (module and declarations):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the ring and uniformizer are the
  public coefficient-extension definitions it imports.
- `def-weil-scheme-morphism-properties` is explicitly a convention node: use
  Mathlib's `Scheme.Over`, `Scheme.Hom.IsOver`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, and `IsProper` for its named notions.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`,
  `Compactification.Refinement`; only the former is needed at one fixed c.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the recorded finite
  coefficient module/derived categories and canonical coefficient realization.
  `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` supplies their
  actual intrinsic constant-ring equivalence `sfIntrinsicDerivedEquivalence`.
- `Sheaf.Paper.FiniteTorAmplitudeSites` reexports `finiteTorConstructible` and
  `finiteTorConstructibleCategory` from `Sheaf.Paper.FiniteTorAmplitude`;
  these are the recorded pro-etale definitions (not the etale alternative).
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`.
  Its fixed-module expression is the existing
  `ProEtale.rightDerivedLowerShriekOfCompactification`, used in rF and the Hom
  chain; it is exact extension followed by derived proper direct image.
- The recorded `ConstructibleExceptionalCoefficients.System` lives in
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`, publicly
  reexported by its recorded module. Importing that owning data module supplies
  FieldStage and the inherited finiteTriangulated structure. The aggregate
  System existence theorem is not an assumption of this finite construction.
  `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt` supplies the already-existing
  exact specified-c finite composite needed by the node's definition; it is
  publicly imported through `SpecifiedExceptionalClassHom`. It is not copied.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`:
  `ProEtale.specifiedExceptionalHomEquiv`; this is the retained class-adjunction
  normalization, at specified c rather than a hidden HasCompactification choice.
- All recorded proof-dependency modules that are stated are imported, including
  PurityAffineChartBounds, ProEtaleFiniteCoefficientDirectImage,
  CompactSupportDirectImageTriangulated, the upstream finite-type/dimension
  module, CanonicalCompactSupportSiteComparison, ProEtaleConstructibleOrigin,
  OpenExtensionFiniteTor, FiniteCtfTriangulated and CompactSupportComparisonUnit.
  Mathlib's `Adjunction.mkOfHomEquiv`, `Adjunction.rightAdjointCommShift`,
  `Adjunction.CommShift` and `Adjunction.isTriangulated_rightAdjoint` are already
  exposed by the data module. The ordinary adjoint is the upstream
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`, which now
  holds without requiring the node's automatically-derived Noetherian hypotheses.

Edge cases: empty middle scheme forces empty X and allows d=0; zero objects
remain objects of the full categories; n=1 is present; identity morphisms and
relative identity compactifications are present. No global separatedness of X
or Y, no flatness of coefficient quotients and no chosen origin are hypotheses.
Reversed intervals are handled by the published interval predicate (empty
cohomological support), not by adding an unrequested a≤b premise. Site object
and morphism universes remain those of the actual Scheme.ProEt site, with
ModuleCat values in u+1 and ambient derived/full categories in u+2.

Searches actually run:

1. msearch.py leanfinder: "Compact support and exceptional inverse image exact
   adjunction on bounded constructible finite Tor pro etale categories with
   uniform coefficient bounds". Eight unrelated hits, including condensed
   discrete-module adjunctions and a generic continuous sheaf adjunction;
   no exact match.
2. msearch.py loogle: "Adjunction.rightAdjointCommShift, Adjunction.CommShift,
   Functor.IsTriangulated". Zero hits; service reports unknown identifier
   Adjunction.rightAdjointCommShift. The actual names/signatures were then read
   from Mathlib/CategoryTheory/Shift/Adjunction.lean and checked by scompile.
3. msearch.py grep: "sfFiniteExceptional|finiteExceptional.*[Aa]djunction|
   compactSupport.*Tor" in CategoryTheory: zero hits.
4. rg of WeilConjectures and Sheaf for the item ID and finite-operation names
   found generic intrinsic operations and the coefficient-construction records,
   not this statement. In particular `exists_system` and
   `exists_coefficient_construction` do not state the specified-c normalized Hom
   equality and the uniform Tor/cohomological bounds required by this item.
   Upstream node-ID search and dag/lean_names_upstream.json likewise gave no
   exact declaration. The module's declaration names were checked for clashes.

Source read: Zheng's PDF was converted to text in the sandbox; Propositions
2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24 were read at their labels.
The current blueprint's `def-weil-exceptional-inverse-image.md` (under
sec-six-functors-basics/sk-prop-a1-kummer) explicitly defines the finite composite,
its relative adjunction and the coefficient-independent chartwise bounds.
The unit compatibility proof and every node proof step were read. No
STATEMENT-DISPUTED or change to the natural-language statement is required; the returned
Lean rendering is repaired to state its existing canonical normalization faithfully.

Validation: `scompile.py` compiled the final delivered module in sandbox and library
module modes, with no errors or warnings. The only postponed proof is the main theorem.
The initial saved packet passed the requested first dry run, but still had the returned
semantic defect. The repaired packet's dry run then found a record-signature mismatch:
I removed the trailing `:=` from `lean.statement` to match the parser's signature.
The next prescribed dry run passed preflight and compilation (commit 7db35f803e7).
The final packet, including the new existing-definition attachment, passed the prescribed
dry run and per-file compilation at commit 90fd3f815f5. Preflight requested the new-node
`import_flags` field; I supplied the empty list and reran successfully.

## Preserved construction steps 1–3

The following are the node's first three construction steps, verbatim, as
requested by the source obligation:

1. The proper part $p_c$ is of finite type by the definition of properness. Finite-type composition therefore makes $\overline X$ finite type over $k$. The finite-type-over-Noetherian theorem applies to $X,Y,\overline X$ over the spectrum of the field $k$, so all are Noetherian. The finite-dimension lemma supplies a nonnegative integer bound $d_c$ for a nonempty $\overline X$; in the empty case set $d_c=0$. These choices involve schemes only, hence are independent of $E,n$.

2. For $K$ of Tor interval $[a,b]$, open extension gives $j_!K\in D^b_{ctf}(\overline X,A)$ with the same interval. Apply the pro-etale direct-image theorem to the proper, hence separated finite-type, map $p_c$ and the bound $\dim\overline X\le d_c$. It gives $Rp_{c,*}j_!K\in D^b_{ctf}(Y,A)$ with Tor interval $[a,b+2d_c]$. Restrict the actual ambient functor on objects and morphisms; its inclusion realization is the identity. The compact-support triangulated-functor theorem gives its additive exact structure. Since the finite-Tor categories are full triangulated subcategories, the same shifts and distinguished triangles give the restricted structure. Use the ambient integer shifts, computed by shifts of complexes and their resolution comparisons; their unit and addition identities restrict unchanged.

3. Apply the general-admissibility corollary to the already defined $G_A=\nu_X^*f^\times_{c,A}R\nu_{Y,*}$. Its statement imposes only relative separatedness. It supplies bounded constructibility and finite Tor amplitude, so restrict this actual functor on morphisms as well. For nonempty $X$, fix its finitely many affine presentations once, put $D=\max_U d_U$ and $e=\dim Y$. The corollary gives $c_U=2(d_U+e)$ and $c=\max_U(c_U+1+2(D-d_U))=2D+2e+1$. Thus both its cohomological bound and its Tor bound are $[a-2D,b+2e+1]$. All these integers are geometric and independent of $E,n$. For empty $X$ use its stated convention $D=c=0$.

## Second reading by Q48

The dispatcher forbids delegation, so this is my second self-reading with the node
and final Lean file open; the maintainer supplies the independent review.

1. Finite-field datum: `D : FiniteFieldDatum.{u}` and `l`, `[Fact l.Prime]`,
   `_hl : l ≠ D.p` retain the characteristic and coefficient-prime assumptions.
2. Finite-type field schemes: the `Over`, `LocallyOfFiniteType` and `QuasiCompact`
   instances for X and Y impose exactly the field-scheme conditions. Only f has
   `IsSeparated`; the two structure maps remain unrestricted in separatedness.
3. Specified compactification: `c : Compactification f` retains exactly c.i, c.g,
   c.Z. `d : ℕ` and `hd` give the stated dimension bound, including empty c.Z at 0.
4. Coefficients: `∀ E : FieldStage l, ∀ n : ℕ+` includes every finite extension and
   every positive uniformizer quotient, including n=1. The finiteness instance is
   `Padic.finite_coefficientExtensionRing`, not a changed coefficient ring.
5. Actual full categories: F and G are between `finiteTorConstructibleCategory`.
   The new `eF` equality forces F on objects AND morphisms to restrict the recorded
   `sfIntrinsicCompactSupport c A`. The new `eG` equality does the same for the
   coefficient-equivalence conjugate of `sfFiniteExceptionalAt A c`.
6. Exact additive adjunction: existential `F.Additive`, `G.Additive`, shifts, `adj`,
   and the `IsTriangulated` conjuncts state the required structures on these functors.
7. Ambient realizations: the equalities to `sfFiniteOperationsLeftRealization` and
   `sfFiniteOperationsRightRealization` now pin rF and rG. The left helper is built
   from `sfIntrinsicCompactSupportComparison`, using `Iso.compInverseIso` and
   `Iso.inverseCompIso` to cancel the fixed coefficient equivalences. The right
   helper cancels the coefficient unit via `Iso.compInverseIso (Iso.refl _)`.
8. Coherent shifts: both realization maps now have `CommShift ℤ`. The fixed right
   ambient shift uses the specified etale adjunction's `rightAdjointCommShift`,
   composed with the derived comparison shifts. The unit and counit of adj have
   `CommShift ℤ` and `sG = adj.rightAdjointCommShift ℤ` retains the adjoint shift.
9. Hom normalization: `hX`, `hY` give the D+ domain; actual origin witnesses exist.
   For EVERY witness W and morphism a the equation compares the realized transpose
   with `specifiedExceptionalHomEquiv`, with rF inverse on the source and rG on the
   target. The new definition node names this exact existing Hom chain. Because
   rF/rG are pinned, replacing the unit and counit by their negatives cannot be
   compensated by replacing rG by its negative.
10. Left Tor bound: the first universal amplitude clause is precisely
    `[a,b] → [a,b+2*d]`, using the published intrinsic amplitude predicate.
11. Right cohomological bound: the middle interval clause uses exactly
    `constructibleInterval` and endpoints `a+cMinus`, `b+cPlus`.
12. Right Tor bound: the last clause uses the same signed endpoints for the
    published intrinsic Tor predicate. The constants precede BOTH E and n.
13. Repetition and edge cases: c is arbitrary, E and n are universal; empty schemes,
    zero objects, n=1, identity maps and reversed empty intervals remain included.
    The full small-site and coefficient universes are unchanged.
14. H2 ownership: all introduced definition owners are in `stmt_deps`; the Hom chain
    gets the new existing-definition attachment rather than promoting the class
    theorem to a statement prerequisite. H4 is repaired by using
    `sfIntrinsicCompactSupport` directly in eF. No data uses sorry; only the named
    theorem has the postponed proof.

## Returned statement repair

The prior Lean statement left `rF` and `rG` existential and did not pin the functors to the
canonical intrinsic compact-support and coefficient-conjugated exceptional constructions.
Following the finite-level definition in `def-weil-exceptional-inverse-image.md` and the
returned H3 repair, the statement now includes `eF`, `eG`, canonical realization
equalities for `rF` and `rG`, and `CommShift ℤ` for both realization maps. All four
citers were audited and continue to hold: `lem-sf-exceptional-refinement-mates`,
`lem-sf-constructible-exceptional-coefficient-construction`,
`lem-sf-exceptional-integral-reconstruction`, and
`lem-sf-exceptional-finite-scalar-mates`.


## New nodes

`def-sf-specified-exceptional-hom-chain` records the exact existing definition
`AlgebraicGeometry.ProEtale.specifiedExceptionalHomEquiv` from
`Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`, with `existing: true` and no
new module. Its self-contained statement specifies the six-factor chain: retained
origin isomorphism, proper/open comparison, comparison adjunction, specified ordinary
etale adjunction, fully faithful comparison map, and origin isomorphism again.
The source is the finite-level adjunction paragraph of the current blueprint
`def-weil-exceptional-inverse-image.md`. Searches: msearch LeanSearch query
"Canonical Hom equivalence from ordinary etale compact support adjunction transported
to pro etale etale-origin complexes" returned eight generic hits; Loogle
`CategoryTheory.Adjunction.homEquiv` returned twelve generic adjunction formulae;
msearch grep `specifiedExceptionalHomEquiv|compactSupport.*HomEquiv` in CategoryTheory
returned zero hits. Direct rg in WeilConjectures found no exact definition; Sheaf
found the published definition above. DAG searches found its theorem-node attachment
but no independent definition node; blueprint_refs search `normalized Hom` found zero
blueprint nodes. This attachment gives definition ownership to the existing map,
without assuming the class theorem in the statement or copying its construction.

Additional landed definition owners added to `stmt_deps` are
`def-weil-proetale-tor-amplitude`, `def-weil-constructible-intervals`,
`def-weil-pbc-etale-origin-witness`, `def-sp-finite-intrinsic-direct-adjunction`,
`def-sfb-finite-derived-lower-shriek-compactification`, and
`def-sf-intrinsic-compact-support-realization`. The direct-adjunction definition node
explicitly records `sfIntrinsicDerivedEquivalence`, so it is the precise owner of
this realization rather than the unrelated scalar-presentation construction.
Their recorded module declarations were read and are reused. No dependency module
or natural-language statement correction is needed.
